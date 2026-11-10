#!/usr/bin/env python

import itertools
import os
import re
import sys
import tempfile
import time
import unittest
from base64 import b64decode, b64encode
from concurrent.futures import ThreadPoolExecutor
from dataclasses import replace
from datetime import datetime, timezone
from glob import glob
from typing import ClassVar
from xml.etree import ElementTree as stdlibElementTree

import cryptography.exceptions
from cryptography import x509
from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric import dsa, ec, rsa
from cryptography.hazmat.primitives.asymmetric.padding import PKCS1v15
from lxml import etree

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))
from signxml import (
    CanonicalizationMethod,
    DigestAlgorithm,
    InvalidCertificate,
    InvalidDigest,
    InvalidInput,
    InvalidSignature,
    SignatureConfiguration,
    SignatureConstructionMethod,
    SignatureMethod,
    SignatureReference,
    VerifyResult,
    XMLSignatureProcessor,
    XMLSigner,
    XMLVerifier,
    methods,
    namespaces,
    processor,
)
from signxml.util import ds_tag
from signxml.xades import (
    XAdESDataObjectFormat,
    XAdESSignatureConfiguration,
    XAdESSignaturePolicy,
    XAdESSigner,
    XAdESVerifier,
    XAdESVerifyResult,
)


class XMLSignerWithSHA1(XMLSigner):
    def check_deprecated_methods(self):
        pass


sha1_ok = SignatureConfiguration(signature_methods=list(SignatureMethod), digest_algorithms=list(DigestAlgorithm))
hmac_only = SignatureConfiguration(
    signature_methods=[sm for sm in SignatureMethod if "HMAC" in sm.name], digest_algorithms=list(DigestAlgorithm)
)
xades_sha1_ok = XAdESSignatureConfiguration(
    signature_methods=list(SignatureMethod), digest_algorithms=list(DigestAlgorithm)
)
example_cert_verification_time = datetime(2015, 1, 1, tzinfo=timezone.utc)
example_cert_config = SignatureConfiguration(verification_time=example_cert_verification_time)
sha1_ok_example_cert = replace(sha1_ok, verification_time=example_cert_verification_time)
xades_sha1_ok_example_cert = replace(xades_sha1_ok, verification_time=example_cert_verification_time)


def get_cert_midpoint_verification_time(cert_text):
    try:
        cert = x509.load_der_x509_certificate(b64decode("".join(cert_text.split())))
    except ValueError:
        return None
    return cert.not_valid_before_utc + (cert.not_valid_after_utc - cert.not_valid_before_utc) / 2


def reset_tree(t, method):
    if not isinstance(t, str):
        for s in t.findall(".//ds:Signature", namespaces=namespaces):
            if method == methods.enveloped and s.get("Id") == "placeholder":
                continue
            s.getparent().remove(s)


def get_no_dsig_key_usage_ee_policy_verifier_at_time(verification_time):
    class _Verifier(XMLVerifier):
        def verify(self, data, **kwargs):
            expect_config = kwargs.pop("expect_config", SignatureConfiguration())
            expect_config = replace(expect_config, verification_time=verification_time)
            return super().verify(data, expect_config=expect_config, **kwargs)

        def get_cert_chain_verifier(self, ca_pem_file, ee_policy, ca_policy):
            ee_policy = x509.verification.ExtensionPolicy.webpki_defaults_ee()
            return super().get_cert_chain_verifier(ca_pem_file, ee_policy, ca_policy)

    return _Verifier()


def get_no_dsig_key_usage_ee_policy_verifier_for_year(year: int):
    verification_time = datetime(year, 1, 1, tzinfo=timezone.utc)
    return get_no_dsig_key_usage_ee_policy_verifier_at_time(verification_time)


def get_verifier_for_year(year: int):
    verification_time = datetime(year, 1, 1, tzinfo=timezone.utc)

    class _Verifier(XMLVerifier):
        def verify(self, data, **kwargs):
            expect_config = kwargs.pop("expect_config", SignatureConfiguration())
            expect_config = replace(expect_config, verification_time=verification_time)
            return super().verify(data, expect_config=expect_config, **kwargs)

    return _Verifier()


class URIResolver(etree.Resolver):
    def resolve(self, url, id, context):
        print(f"Resolving URL '{url}'")


parser = etree.XMLParser(load_dtd=True)
parser.resolvers.add(URIResolver())

interop_dir = os.path.join(os.path.dirname(__file__), "interop")


class LoadExampleKeys:
    def load_example_keys(self):
        with open(os.path.join(os.path.dirname(__file__), "example.pem"), "rb") as fh:
            crt = fh.read()
        with open(os.path.join(os.path.dirname(__file__), "example.key"), "rb") as fh:
            key = fh.read()
        return crt, key

    def load_example_ecdsa_keys(self):
        with open(os.path.join(os.path.dirname(__file__), "example_ecdsa.pem"), "rb") as fh:
            crt = fh.read()
        with open(os.path.join(os.path.dirname(__file__), "example_ecdsa.key"), "rb") as fh:
            key = fh.read()
        return crt, key


class TestVerifyXML(unittest.TestCase, LoadExampleKeys):
    def test_example_multi(self):
        cert, _ = self.load_example_keys()
        with open(os.path.join(os.path.dirname(__file__), "example.pem")) as fh:
            cert = fh.read()
        example_file = os.path.join(os.path.dirname(__file__), "example-125.xml")
        XMLVerifier().verify(
            data=etree.parse(example_file),
            x509_cert=cert,
            expect_references=2,
            expect_config=example_cert_config,
        )

    def test_example_multi_unspecified_reference_count(self):
        cert, _ = self.load_example_keys()
        with open(os.path.join(os.path.dirname(__file__), "example.pem")) as fh:
            cert = fh.read()
        example_file = os.path.join(os.path.dirname(__file__), "example-125.xml")
        res = XMLVerifier().verify(
            data=etree.parse(example_file),
            x509_cert=cert,
            expect_references=True,
            expect_config=example_cert_config,
        )

        self.assertIsInstance(res, list)
        self.assertEqual(2, len(res))

    def test_schema_cache_is_scoped_to_processor_subclasses(self):
        for first, second in ((XMLVerifier, XAdESVerifier), (XAdESVerifier, XMLVerifier)):
            for cls in (XMLVerifier, XAdESVerifier):
                if "_schemas" in cls.__dict__:
                    delattr(cls, "_schemas")

            first_schemas = first.schemas()
            second_schemas = second.schemas()

            self.assertIsNot(first_schemas, second_schemas)
            self.assertEqual(len(first_schemas), len(first.schema_files))
            self.assertEqual(len(second_schemas), len(second.schema_files))

    def test_schema_cache_is_thread_safe_on_first_access(self):
        class ThreadedProcessor(processor.XMLProcessor):
            schema_files: ClassVar[list[str]] = ["schema-a.xsd", "schema-b.xsd"]

        original_get_schema = processor.get_schema
        original_schemas = processor.XMLProcessor._schemas
        calls = []

        def fake_get_schema(schema_file):
            time.sleep(0.01)
            calls.append(schema_file)
            return schema_file

        processor.XMLProcessor._schemas = []
        processor.get_schema = fake_get_schema
        try:
            with ThreadPoolExecutor(max_workers=8) as executor:
                results = list(executor.map(lambda _: ThreadedProcessor.schemas(), range(8)))
        finally:
            processor.get_schema = original_get_schema
            processor.XMLProcessor._schemas = original_schemas
            if "_schemas" in ThreadedProcessor.__dict__:
                delattr(ThreadedProcessor, "_schemas")

        self.assertEqual(ThreadedProcessor.schema_files, calls)
        self.assertTrue(all(result is results[0] for result in results))


class TestSignXML(unittest.TestCase, LoadExampleKeys):
    def setUp(self):
        self.example_xml_files = (
            os.path.join(os.path.dirname(__file__), "example.xml"),
            os.path.join(os.path.dirname(__file__), "example2.xml"),
        )
        self.keys = {
            "hmac": b"secret",
            "rsa": rsa.generate_private_key(public_exponent=65537, key_size=2048),
            "dsa": dsa.generate_private_key(key_size=1024),
            "ecdsa": ec.generate_private_key(curve=ec.SECP384R1()),
        }

    def test_basic_signxml_statements(self):
        self.assertEqual(SignatureMethod.RSA_SHA256.value, "http://www.w3.org/2001/04/xmldsig-more#rsa-sha256")
        self.assertEqual(SignatureConstructionMethod.enveloped, methods.enveloped)
        with self.assertRaisesRegex(InvalidInput, "Unknown signature construction method"):
            XMLSignerWithSHA1(method=None)

        with self.assertRaisesRegex(InvalidInput, "must be an XML element"):
            XMLSigner(signature_algorithm="hmac-sha256").sign("x", key=b"abc")

        digest_algs = list(DigestAlgorithm)
        sig_algs = list(SignatureMethod)
        c14n_algs = {
            "http://www.w3.org/2001/10/xml-exc-c14n#",
            "http://www.w3.org/2001/10/xml-exc-c14n#WithComments",
        }

        def test_case(case):
            digest_alg, sig_alg, method, c14n_alg = case
            data = [etree.parse(f).getroot() for f in self.example_xml_files]
            # FIXME: data.extend(stdlibElementTree.parse(f).getroot() for f in (self.example_xml_files)
            data.append(stdlibElementTree.parse(self.example_xml_files[0]).getroot())
            data.append("x y \n z t\n я\n")
            for d in data:
                if isinstance(d, str) and method != methods.enveloping:
                    continue
                print(digest_alg.name, sig_alg.name, c14n_alg, method, type(d))
                reset_tree(d, method)
                signer = XMLSignerWithSHA1(
                    method=method,
                    signature_algorithm=sig_alg,
                    digest_algorithm=digest_alg,
                    c14n_algorithm=c14n_alg,
                )
                sig_alg_type = "rsa" if "RSA_MGF1" in sig_alg.name else sig_alg.name.split("_")[0].lower()
                signed = signer.sign(
                    d, key=self.keys[sig_alg_type], reference_uri="URI" if method == methods.detached else None
                )
                # print(etree.tostring(signed))
                hmac_key = self.keys["hmac"] if sig_alg_type == "hmac" else None
                expect_config = hmac_only if sig_alg_type == "hmac" else sha1_ok
                verify_kwargs = {
                    "require_x509": False,
                    "hmac_key": hmac_key,
                    "validate_schema": True,
                    "expect_config": expect_config,
                }

                if method == methods.detached:

                    def resolver(uri, data=d):
                        if isinstance(data, stdlibElementTree.Element):
                            return etree.fromstring(stdlibElementTree.tostring(data))
                        else:
                            return data

                    verify_kwargs["uri_resolver"] = resolver

                signed_data = etree.tostring(signed)
                XMLVerifier().verify(signed_data, **verify_kwargs)
                XMLVerifier().verify(signed_data, parser=parser, **verify_kwargs)
                res = XMLVerifier().verify(signed_data, id_attribute="Id", **verify_kwargs)
                self.assertIsInstance(res, VerifyResult)
                for attr in "signed_data", "signed_xml", "signature_xml":
                    self.assertTrue(hasattr(res, attr))

                if res.signed_xml is not None:
                    # Ensure the signature is not part of the signed data
                    self.assertIsNone(res.signed_xml.find(".//{http://www.w3.org/2000/09/xmldsig#}Signature"))
                    self.assertNotEqual(res.signed_xml.tag, "{http://www.w3.org/2000/09/xmldsig#}Signature")

                # Ensure the signature was returned
                self.assertEqual(res.signature_xml.tag, "{http://www.w3.org/2000/09/xmldsig#}Signature")

                if method == methods.enveloping:
                    with self.assertRaisesRegex(InvalidInput, "Unable to resolve reference URI"):
                        XMLVerifier().verify(signed_data, id_attribute="X", **verify_kwargs)

                with self.assertRaisesRegex(InvalidInput, "Expected a X.509 certificate based signature"):
                    XMLVerifier().verify(
                        signed_data,
                        hmac_key=hmac_key,
                        uri_resolver=verify_kwargs.get("uri_resolver"),
                        expect_config=expect_config,
                    )

                if method != methods.detached:
                    with self.assertRaisesRegex(InvalidSignature, "Digest mismatch"):
                        mangled_sig = signed_data.replace(b"Austria", b"Mongolia").replace(b"x y", b"a b")
                        XMLVerifier().verify(mangled_sig, **verify_kwargs)

                with self.assertRaises(cryptography.exceptions.InvalidSignature):
                    mangled_sig = signed_data.replace(b"<ds:DigestValue>", b"<ds:DigestValue>!")
                    XMLVerifier().verify(mangled_sig, **verify_kwargs)

                with self.assertRaises(cryptography.exceptions.InvalidSignature):
                    sig_value = re.search(b"<ds:SignatureValue>(.+?)</ds:SignatureValue>", signed_data).group(1)
                    mangled_sig = re.sub(
                        b"<ds:SignatureValue>(.+?)</ds:SignatureValue>",
                        b"<ds:SignatureValue>" + b64encode(b64decode(sig_value)[::-1]) + b"</ds:SignatureValue>",
                        signed_data,
                    )
                    XMLVerifier().verify(mangled_sig, **verify_kwargs)

                with self.assertRaises(etree.XMLSyntaxError):
                    XMLVerifier().verify("", hmac_key=hmac_key, require_x509=False)

                if sig_alg_type == "hmac":
                    with self.assertRaisesRegex(InvalidSignature, "Signature mismatch"):
                        verify_kwargs["hmac_key"] = b"SECRET"
                        XMLVerifier().verify(signed_data, **verify_kwargs)

        executor = ThreadPoolExecutor()
        for _ in executor.map(test_case, itertools.product(digest_algs, sig_algs, methods, c14n_algs)):
            pass

    def test_x509_certs(self):
        verifier = get_no_dsig_key_usage_ee_policy_verifier_for_year(2015)
        tree = etree.parse(self.example_xml_files[0])
        ca_pem_file = os.path.join(os.path.dirname(__file__), "example-ca.pem").encode("utf-8")
        crt, key = self.load_example_keys()
        for method in methods.enveloped, methods.enveloping:
            data = tree.getroot()
            reset_tree(data, method)
            signer = XMLSigner(method=method, signature_algorithm=SignatureMethod.RSA_SHA256)
            signed = signer.sign(data, key=key, cert=crt)
            signed_data = etree.tostring(signed)
            verifier.verify(signed_data, x509_cert=crt, expect_config=example_cert_config)
            verifier.verify(signed_data, x509_cert=x509.load_pem_x509_certificate(crt))
            verifier.verify(signed_data, x509_cert=crt, cert_subject_name="*.example.com")

            with self.assertRaises(ValueError):
                verifier.verify(signed_data, x509_cert=crt[::-1])

            with self.assertRaises(InvalidSignature):
                verifier.verify(signed_data, x509_cert=crt, cert_subject_name="test")

            # FIXME: create new test case with reconfigured CA/EKU
            with self.assertRaisesRegex(InvalidCertificate, "required EKU not found"):
                verifier.verify(signed_data, ca_pem_file=ca_pem_file)

            with self.assertRaisesRegex(InvalidCertificate, "required EKU not found"):
                verifier.verify(signed_data)

            # TODO: negative: verify with wrong cert, wrong CA

    def test_x509_cert_chain_verification_time(self):
        def make_key_usage(digital_signature=False, key_cert_sign=False, crl_sign=False):
            return x509.KeyUsage(
                digital_signature=digital_signature,
                content_commitment=False,
                key_encipherment=False,
                data_encipherment=False,
                key_agreement=False,
                key_cert_sign=key_cert_sign,
                crl_sign=crl_sign,
                encipher_only=False,
                decipher_only=False,
            )

        tree = etree.parse(self.example_xml_files[0])
        ca_key = ec.generate_private_key(ec.SECP384R1())
        ca_name = x509.Name([x509.NameAttribute(x509.oid.NameOID.COMMON_NAME, "SignXML Test CA")])
        ca_cert = (
            x509.CertificateBuilder()
            .subject_name(ca_name)
            .issuer_name(ca_name)
            .public_key(ca_key.public_key())
            .serial_number(x509.random_serial_number())
            .not_valid_before(datetime(2020, 1, 1, tzinfo=timezone.utc))
            .not_valid_after(datetime(2030, 1, 1, tzinfo=timezone.utc))
            .add_extension(x509.BasicConstraints(ca=True, path_length=None), critical=True)
            .add_extension(make_key_usage(key_cert_sign=True, crl_sign=True), critical=True)
            .add_extension(x509.SubjectKeyIdentifier.from_public_key(ca_key.public_key()), critical=False)
            .sign(ca_key, hashes.SHA384())
        )

        leaf_key = ec.generate_private_key(ec.SECP384R1())
        leaf_cert = (
            x509.CertificateBuilder()
            .subject_name(x509.Name([x509.NameAttribute(x509.oid.NameOID.COMMON_NAME, "XML Signature Test")]))
            .issuer_name(ca_cert.subject)
            .public_key(leaf_key.public_key())
            .serial_number(x509.random_serial_number())
            .not_valid_before(datetime(2020, 1, 1, tzinfo=timezone.utc))
            .not_valid_after(datetime(2021, 1, 1, tzinfo=timezone.utc))
            .add_extension(x509.BasicConstraints(ca=False, path_length=None), critical=True)
            .add_extension(make_key_usage(digital_signature=True), critical=True)
            .add_extension(x509.SubjectKeyIdentifier.from_public_key(leaf_key.public_key()), critical=False)
            .add_extension(x509.AuthorityKeyIdentifier.from_issuer_public_key(ca_key.public_key()), critical=False)
            .sign(ca_key, hashes.SHA384())
        )

        signer = XMLSigner(method=methods.enveloped, signature_algorithm=SignatureMethod.ECDSA_SHA384)
        signed = signer.sign(tree.getroot(), key=leaf_key, cert=[leaf_cert])
        signed_data = etree.tostring(signed)

        XMLVerifier().verify(
            signed_data,
            x509_cert=leaf_cert,
            expect_config=SignatureConfiguration(verification_time=datetime(2020, 6, 1, tzinfo=timezone.utc)),
        )
        with self.assertRaisesRegex(
            InvalidCertificate, "provided x509_cert.*certificate is not yet valid.*SignatureConfiguration"
        ):
            XMLVerifier().verify(
                signed_data,
                x509_cert=leaf_cert,
                expect_config=SignatureConfiguration(verification_time=datetime(2019, 1, 1, tzinfo=timezone.utc)),
            )
        with self.assertRaisesRegex(
            InvalidCertificate, "provided x509_cert.*certificate has expired.*SignatureConfiguration"
        ):
            XMLVerifier().verify(
                signed_data,
                x509_cert=leaf_cert,
                expect_config=SignatureConfiguration(verification_time=datetime(2025, 1, 1, tzinfo=timezone.utc)),
            )

        with tempfile.TemporaryDirectory() as temp_dir:
            ca_pem_file = os.path.join(temp_dir, "ca.pem")
            with open(ca_pem_file, "wb") as fh:
                fh.write(ca_cert.public_bytes(serialization.Encoding.PEM))

            XMLVerifier().verify(
                signed_data,
                ca_pem_file=ca_pem_file,
                expect_config=SignatureConfiguration(verification_time=datetime(2020, 6, 1, tzinfo=timezone.utc)),
            )
            with self.assertRaisesRegex(
                InvalidCertificate,
                "X509Data/X509Certificate certificate at index 0.*certificate has expired.*SignatureConfiguration",
            ):
                XMLVerifier().verify(
                    signed_data,
                    ca_pem_file=ca_pem_file,
                    expect_config=SignatureConfiguration(verification_time=datetime(2025, 1, 1, tzinfo=timezone.utc)),
                )

    def test_issue_284_expired_certificate_can_verify_at_signing_time(self):
        issue_file = os.path.join(os.path.dirname(__file__), "issues", "issue_284_expired_cert.xml")
        with open(issue_file, "rb") as fh:
            signed_xml = fh.read()
        doc = etree.fromstring(signed_xml)
        cert_text = doc.find(".//ds:X509Certificate", namespaces=namespaces).text
        signing_cert = x509.load_der_x509_certificate(b64decode(cert_text))
        config = SignatureConfiguration(
            signature_methods=frozenset({SignatureMethod.RSA_SHA1}),
            digest_algorithms=frozenset({DigestAlgorithm.SHA1}),
            default_reference_c14n_method=CanonicalizationMethod.CANONICAL_XML_1_0,
        )

        verifier = XMLVerifier()
        verifier.excise_empty_xmlns_declarations = True
        with self.assertRaisesRegex(
            InvalidCertificate, "provided x509_cert.*certificate has expired.*SignatureConfiguration"
        ):
            verifier.verify(signed_xml, x509_cert=signing_cert, expect_config=config)

        verifier = XMLVerifier()
        verifier.excise_empty_xmlns_declarations = True
        result = verifier.verify(
            signed_xml,
            x509_cert=signing_cert,
            expect_config=replace(config, verification_time=datetime(2018, 5, 28, 17, 0, tzinfo=timezone.utc)),
        )
        self.assertIsInstance(result, VerifyResult)

    def test_sign_rejects_invalid_x509_cert_input(self):
        _, key = self.load_example_keys()
        data = etree.parse(self.example_xml_files[0]).getroot()
        invalid_pem = "-----BEGIN CERTIFICATE-----\nnot a certificate\n-----END CERTIFICATE-----"

        invalid_cert_inputs = [
            ("", "No PEM-encoded certificates found"),
            ([], "No certificates found"),
            ([""], "Invalid X.509 certificate"),
            (invalid_pem, "Invalid X.509 certificate"),
            ([invalid_pem], "Invalid X.509 certificate"),
        ]
        for cert, message in invalid_cert_inputs:
            with self.subTest(cert=repr(cert)), self.assertRaisesRegex(InvalidInput, message):
                XMLSigner().sign(data, key=key, cert=cert)

    def test_x509_cert_chain_requires_digital_signature_key_usage(self):
        def make_key_usage(digital_signature=False, key_cert_sign=False, crl_sign=False):
            return x509.KeyUsage(
                digital_signature=digital_signature,
                content_commitment=False,
                key_encipherment=False,
                data_encipherment=False,
                key_agreement=False,
                key_cert_sign=key_cert_sign,
                crl_sign=crl_sign,
                encipher_only=False,
                decipher_only=False,
            )

        verifier = get_verifier_for_year(2027)
        tree = etree.parse(self.example_xml_files[0])
        ca_key = ec.generate_private_key(ec.SECP384R1())
        ca_name = x509.Name([x509.NameAttribute(x509.oid.NameOID.COMMON_NAME, "SignXML Test CA")])
        ca_cert = (
            x509.CertificateBuilder()
            .subject_name(ca_name)
            .issuer_name(ca_name)
            .public_key(ca_key.public_key())
            .serial_number(x509.random_serial_number())
            .not_valid_before(datetime(2026, 1, 1))
            .not_valid_after(datetime(2030, 1, 1))
            .add_extension(x509.BasicConstraints(ca=True, path_length=None), critical=True)
            .add_extension(make_key_usage(key_cert_sign=True, crl_sign=True), critical=True)
            .add_extension(x509.SubjectKeyIdentifier.from_public_key(ca_key.public_key()), critical=False)
            .sign(ca_key, hashes.SHA384())
        )

        def make_leaf_cert(digital_signature):
            leaf_key = ec.generate_private_key(ec.SECP384R1())
            leaf_cert = (
                x509.CertificateBuilder()
                .subject_name(x509.Name([x509.NameAttribute(x509.oid.NameOID.COMMON_NAME, "XML Signature Test")]))
                .issuer_name(ca_cert.subject)
                .public_key(leaf_key.public_key())
                .serial_number(x509.random_serial_number())
                .not_valid_before(datetime(2026, 1, 1))
                .not_valid_after(datetime(2030, 1, 1))
                .add_extension(x509.BasicConstraints(ca=False, path_length=None), critical=True)
                .add_extension(make_key_usage(digital_signature=digital_signature), critical=True)
                .add_extension(x509.SubjectKeyIdentifier.from_public_key(leaf_key.public_key()), critical=False)
                .add_extension(x509.AuthorityKeyIdentifier.from_issuer_public_key(ca_key.public_key()), critical=False)
                .sign(ca_key, hashes.SHA384())
            )
            return leaf_key, leaf_cert

        signer = XMLSigner(method=methods.enveloped, signature_algorithm=SignatureMethod.ECDSA_SHA384)
        with tempfile.TemporaryDirectory() as temp_dir:
            ca_pem_file = os.path.join(temp_dir, "ca.pem")
            with open(ca_pem_file, "wb") as fh:
                fh.write(ca_cert.public_bytes(serialization.Encoding.PEM))

            leaf_key, leaf_cert = make_leaf_cert(digital_signature=True)
            key_usage = leaf_cert.extensions.get_extension_for_class(x509.KeyUsage).value
            self.assertTrue(key_usage.digital_signature)
            signed = signer.sign(tree.getroot(), key=leaf_key, cert=[leaf_cert])
            verifier.verify(etree.tostring(signed), ca_pem_file=ca_pem_file)

            leaf_key, leaf_cert = make_leaf_cert(digital_signature=False)
            key_usage = leaf_cert.extensions.get_extension_for_class(x509.KeyUsage).value
            self.assertFalse(key_usage.digital_signature)
            signed = signer.sign(etree.parse(self.example_xml_files[0]).getroot(), key=leaf_key, cert=[leaf_cert])
            with self.assertRaisesRegex(InvalidCertificate, "certificate KeyUsage does not allow digitalSignature"):
                verifier.verify(etree.tostring(signed), ca_pem_file=ca_pem_file)

    def test_xmldsig_interop_examples(self):
        ca_pem_file = os.path.join(os.path.dirname(__file__), "interop", "cacert.pem").encode("utf-8")

        verifier = get_no_dsig_key_usage_ee_policy_verifier_for_year(2015)
        for signature_file in glob(os.path.join(os.path.dirname(__file__), "interop", "*.xml")):
            print("Verifying", signature_file)
            with open(signature_file, "rb") as fh:
                msg = "basicConstraints.cA must not be asserted in an EE certificate"
                with self.assertRaisesRegex(InvalidCertificate, msg):
                    verifier.verify(fh.read(), ca_pem_file=ca_pem_file, expect_config=sha1_ok)

    def test_xmldsig_interop_TR2012(self):
        def get_x509_cert(**kwargs):
            with open(os.path.join(interop_dir, "TR2012", "rsa-cert.der"), "rb") as fh:
                return [x509.load_der_x509_certificate(fh.read())]

        signature_files = glob(os.path.join(interop_dir, "TR2012", "signature*.xml"))
        for signature_file in signature_files:
            print("Verifying", signature_file)
            with open(signature_file, "rb") as fh:
                try:
                    sig = fh.read()
                    XMLVerifier().verify(
                        sig,
                        require_x509=False,
                        hmac_key=b"testkey" if "hmac" in signature_file else None,
                        validate_schema=True,
                        cert_resolver=get_x509_cert if "x509digest" in signature_file else None,
                        expect_config=hmac_only if "hmac" in signature_file else sha1_ok,
                    )
                    sig.decode("utf-8")
                except Exception as e:
                    if "keyinforeference" in signature_file:
                        print("Unsupported test case:", type(e), e)
                    elif "x509digest" in signature_file:
                        assert isinstance(e, InvalidCertificate)
                    else:
                        raise

    def test_xmldsig_interop(self):
        def resolver(uri):
            if uri == "document.xml":
                with open(os.path.join(interop_dir, "phaos-xmldsig-three", uri), "rb") as fh:
                    return fh.read()
            elif uri == "http://www.ietf.org/rfc/rfc3161.txt":
                with open(os.path.join(os.path.dirname(__file__), "rfc3161.txt"), "rb") as fh:
                    return fh.read()
            return None

        def get_x509_cert(signature_file):
            if "windows_store_signature" in signature_file:
                return open(os.path.join(interop_dir, "xml-crypto", "windows_store_certificate.pem")).read()
            elif "pyXMLSecurity" in signature_file:
                return open(os.path.join(interop_dir, "pyXMLSecurity", "test.pem")).read()
            else:
                return None

        def get_ca_pem_file(signature_file):
            if "signature-dsa" in signature_file:
                ca_pem_file = os.path.join(interop_dir, "phaos-xmldsig-three", "certs", "dsa-ca-cert.pem")
            elif "signature-rsa" in signature_file:
                ca_pem_file = os.path.join(interop_dir, "phaos-xmldsig-three", "certs", "rsa-ca-cert.pem")
            elif "aleksey-xmldsig-01-enveloped" in signature_file:
                ca_pem_file = os.path.join(interop_dir, "aleksey-xmldsig-01-enveloped", "cacert.pem")
            elif "aleksey" in signature_file:
                ca_pem_file = os.path.join(interop_dir, "aleksey-xmldsig-01", "cacert.pem")
            elif "wsfederation_metadata" in signature_file:
                ca_pem_file = os.path.join(interop_dir, "xml-crypto", "wsfederation_metadata.pem")
            elif "signature_with_inclusivenamespaces" in signature_file:
                ca_pem_file = os.path.join(interop_dir, "xml-crypto", "signature_with_inclusivenamespaces.pem")
            else:
                return None
            return ca_pem_file.encode("utf-8")

        def cert_resolver(x509_issuer_name, x509_serial_number, x509_digest):
            with open(os.path.join(interop_dir, "phaos-xmldsig-three", "certs", "rsa-cert.pem")) as fh:
                return [fh.read()]

        signature_files = glob(os.path.join(interop_dir, "*", "signature*.xml"))
        signature_files += glob(os.path.join(interop_dir, "aleksey*", "*.xml"))
        signature_files += glob(os.path.join(interop_dir, "xml-crypto", "*.xml"))
        signature_files += glob(os.path.join(interop_dir, "pyXMLSecurity", "*.xml"))
        for signature_file in signature_files:
            print("Verifying", signature_file)
            hmac_key = None
            expect_config = sha1_ok
            if "hmac" in signature_file:
                hmac_key = b"test" if "phaos" in signature_file else b"secret"
                expect_config = hmac_only
            with open(signature_file, "rb") as fh:
                try:
                    sig = fh.read()
                    verification_time = datetime(2010 if "phaos" in signature_file else 2014, 1, 1, tzinfo=timezone.utc)
                    if "pyXMLSecurity" in signature_file:
                        verification_time = datetime(2009, 10, 15, tzinfo=timezone.utc)
                    verifier = get_no_dsig_key_usage_ee_policy_verifier_at_time(verification_time)
                    verifier.excise_empty_xmlns_declarations = True
                    verifier.verify(
                        sig,
                        require_x509=False,
                        hmac_key=hmac_key,
                        validate_schema=True,
                        uri_resolver=resolver,
                        x509_cert=get_x509_cert(signature_file),
                        cert_resolver=cert_resolver if "issuer-serial" in signature_file else None,
                        ca_pem_file=get_ca_pem_file(signature_file),
                        expect_config=expect_config,
                    )
                except Exception as e:
                    unsupported_cases = (
                        "xpath-transform",
                        "xslt-transform",
                        "xpointer",
                        "x509-data-ski",
                        "x509-data-subject-name",
                        "x509data",
                        "signature-x509-ski",
                        "signature-x509-is",
                    )
                    bad_interop_cases = (
                        "signature-big",
                        "enveloping-dsa-x509chain",
                        "enveloping-sha512-hmac-sha512",
                        "enveloping-sha512-rsa-sha512",
                        "enveloping-rsa-x509chain",
                        "enveloping-sha1-rsa-sha1",
                        "enveloping-sha224-rsa-sha224",
                        "enveloping-sha256-rsa-sha256",
                        "enveloping-sha384-rsa-sha384",
                    )
                    if signature_file.endswith(("expired-cert.xml", "wsfederation_metadata.xml")):
                        with self.assertRaisesRegex(
                            InvalidCertificate,
                            "certificate (has expired|is not yet valid).*SignatureConfiguration",
                        ):
                            raise
                    elif signature_file.endswith("invalid_enveloped_transform.xml"):
                        self.assertIsInstance(e, InvalidSignature)
                        # with self.assertRaisesRegex(ValueError, "Can't remove the root signature node"):
                        #    raise
                    elif "md5" in signature_file or "ripemd160" in signature_file:
                        self.assertIsInstance(e, InvalidInput)
                        # with self.assertRaisesRegex(InvalidInput, "Algorithm .+ is not recognized"):
                        #    raise
                    elif "HMACOutputLength" in sig.decode("utf-8"):
                        self.assertIsInstance(e, (InvalidSignature, InvalidDigest))
                    elif signature_file.endswith("signature-rsa-enveloped-bad-digest-val.xml"):
                        # self.assertIsInstance(e, InvalidDigest)
                        self.assertIsInstance(e, InvalidCertificate)
                    elif signature_file.endswith("signature-rsa-detached-xslt-transform-bad-retrieval-method.xml"):
                        self.assertIsInstance(e, InvalidInput)
                    elif signature_file.endswith("signature-rsa-enveloped-bad-sig.xml"):
                        self.assertIsInstance(e, etree.DocumentInvalid)
                    elif signature_file.endswith("signature-x509-crt.xml"):
                        self.assertIsInstance(e, InvalidCertificate)
                    elif signature_file.endswith(("signature-keyname.xml", "signature-x509-sn.xml")):
                        self.assertIsInstance(e, InvalidInput)
                    elif signature_file.endswith("signature-x509-crt-crl.xml"):
                        self.assertIsInstance(e, InvalidCertificate)
                    elif signature_file.endswith(
                        (
                            "signature-retrievalmethod-rawx509crt.xml",
                            os.path.join("merlin-xmldsig-twenty-three", "signature.xml"),
                        )
                    ):
                        self.assertIsInstance(e, InvalidInput)
                    elif any(x in signature_file for x in unsupported_cases):
                        print("Unsupported test case:", type(e), e)
                    elif any(x in signature_file for x in bad_interop_cases) or "Unable to resolve reference" in str(e):
                        print("Bad interop test case:", type(e), e)
                    elif (
                        "Certificate is missing required extension" in str(e)
                        or "certificate must be an X509v3 certificate" in str(e)
                        or "basicConstraints.cA must not be asserted in an EE certificate" in str(e)
                    ):
                        print("IGNORED:", type(e), e)
                    elif "TR2012" not in signature_file:
                        raise
                else:
                    decoded_sig = sig.decode("utf-8")
                    if "HMACOutputLength" in decoded_sig or "bad" in signature_file or "expired" in signature_file:
                        self.fail("Expected an exception to occur")

    def test_changing_signature_namespace_prefix(self):
        data = etree.parse(self.example_xml_files[0]).getroot()
        signer = XMLSigner()
        signer.namespaces = {"digi_sign": namespaces["ds"]}
        signed = signer.sign(data, key=self.keys["rsa"])
        signed_data = etree.tostring(signed)
        expected_match = f'<digi_sign:Signature xmlns:digi_sign="{namespaces["ds"]}">'
        self.assertTrue(re.search(expected_match.encode("ascii"), signed_data))

    def test_changing_signature_namespace_prefix_to_default(self):
        data = etree.parse(self.example_xml_files[0]).getroot()
        signer = XMLSigner()
        ns = {}
        ns[None] = namespaces["ds"]
        signer.namespaces = ns
        signed = signer.sign(data, key=self.keys["rsa"])
        signed_data = etree.tostring(signed)
        expected_match = f'<Signature xmlns="{namespaces["ds"]}">'
        self.assertTrue(re.search(expected_match.encode("ascii"), signed_data))

    def test_sign_verify_default_ns_roundtrip(self):
        """
        Test sign/verify round-trip when using default namespace.

        See https://github.com/XML-Security/signxml/issues/275
        """
        crt, key = self.load_example_keys()
        data = etree.parse(self.example_xml_files[0]).getroot()
        signer = XMLSigner()
        signer.namespaces = {None: namespaces["ds"]}
        signed = signer.sign(data, key=key, cert=crt)

        signed_info = signed.find(".//SignedInfo")
        self.assertIsNotNone(signed_info)
        c14n_output = etree.tostring(signed_info, method="c14n").decode()
        self.assertNotIn('xmlns=""', c14n_output)
        self.assertIn('xmlns="http://www.w3.org/2000/09/xmldsig#"', c14n_output)

        signed_data = etree.tostring(signed)
        verifier = XMLVerifier()
        verifier.excise_empty_xmlns_declarations = True
        verifier.verify(signed_data, x509_cert=crt, expect_config=example_cert_config)

    def test_elementtree_compat(self):
        data = stdlibElementTree.parse(self.example_xml_files[0]).getroot()
        signer = XMLSigner()
        signer.sign(data, key=self.keys["rsa"])

    saml_test_vectors: ClassVar[list[str]] = [
        """<samlp:Response xmlns:samlp="urn:oasis:names:tc:SAML:2.0:protocol"
                            xmlns:saml="urn:oasis:names:tc:SAML:2.0:assertion" ID="responseId">
            <saml:Assertion xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
                            xmlns:xs="http://www.w3.org/2001/XMLSchema" ID="assertionId">
            <ds:Signature xmlns:ds="http://www.w3.org/2000/09/xmldsig#" Id="placeholder" />
            </saml:Assertion>
            </samlp:Response>""",
        """<samlp:Response xmlns:samlp="urn:oasis:names:tc:SAML:2.0:protocol"
                            xmlns:saml="urn:oasis:names:tc:SAML:2.0:assertion" Id="responseId">
            <saml:Assertion xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
                            xmlns:xs="http://www.w3.org/2001/XMLSchema" Id="assertionId">
            <ds:Signature xmlns:ds="http://www.w3.org/2000/09/xmldsig#" Id="placeholder" />
            </saml:Assertion>
            <saml:Assertion xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
                            xmlns:xs="http://www.w3.org/2001/XMLSchema" Id="assertion2">
            </saml:Assertion>
            </samlp:Response>""",
    ]

    def test_verify_results_with_nonspecific_reference_count(self):
        crt, key = self.load_example_keys()
        data = etree.fromstring(self.saml_test_vectors[0])
        reference_uri = "assertionId"
        signed_root = XMLSigner().sign(data, reference_uri=reference_uri, key=key, cert=crt)
        res = XMLVerifier().verify(
            etree.tostring(signed_root), x509_cert=crt, expect_references=True, expect_config=example_cert_config
        )

        self.assertIsInstance(res, list)
        self.assertEqual(1, len(res))

    def test_reference_uris_and_custom_key_info(self):
        crt, key = self.load_example_keys()

        # Both ID and Id formats. XPath 1 doesn't have case insensitive attribute search
        for d in self.saml_test_vectors:
            data = etree.fromstring(d)
            reference_uri = ["assertionId", "assertion2"] if "assertion2" in d else "assertionId"
            signed_root = XMLSigner().sign(data, reference_uri=reference_uri, key=key, cert=crt)
            res = XMLVerifier().verify(
                etree.tostring(signed_root), x509_cert=crt, expect_references=True, expect_config=example_cert_config
            )
            signed_data_root = res[0].signed_xml
            ref = signed_root.xpath(
                "/samlp:Response/saml:Assertion/ds:Signature/ds:SignedInfo/ds:Reference",
                namespaces={
                    "ds": "http://www.w3.org/2000/09/xmldsig#",
                    "saml": "urn:oasis:names:tc:SAML:2.0:assertion",
                    "samlp": "urn:oasis:names:tc:SAML:2.0:protocol",
                },
            )
            self.assertEqual("assertionId", ref[0].attrib["URI"][1:])

            self.assertEqual("{urn:oasis:names:tc:SAML:2.0:assertion}Assertion", signed_data_root.tag)

            # Also test with detached signing
            ref_xpath = "/ds:Signature/ds:SignedInfo/ds:Reference"
            signer = XMLSigner(method=methods.detached)
            s = signer.sign(data, reference_uri=reference_uri, key=key, cert=crt)
            self.assertTrue(s.xpath(ref_xpath + "/ds:Transforms", namespaces=namespaces))
            self.assertTrue(s.xpath(ref_xpath + "/ds:DigestMethod", namespaces=namespaces))
            self.assertTrue(s.xpath(ref_xpath + "/ds:DigestValue", namespaces=namespaces))

            self.assertTrue(s.xpath("/ds:Signature/ds:KeyInfo/ds:X509Data", namespaces=namespaces))
            self.assertFalse(s.xpath("/ds:Signature/ds:KeyInfo/ds:KeyValue", namespaces=namespaces))
            s2 = signer.sign(data, reference_uri=reference_uri, key=key, cert=crt, always_add_key_value=True)
            self.assertTrue(s2.xpath("/ds:Signature/ds:KeyInfo/ds:X509Data", namespaces=namespaces))
            self.assertTrue(s2.xpath("/ds:Signature/ds:KeyInfo/ds:KeyValue", namespaces=namespaces))

            # Test setting custom key info
            wsse_ns = "http://docs.oasis-open.org/wss/2004/01/oasis-200401-wss-wssecurity-secext-1.0.xsd"
            with open(os.path.join(os.path.dirname(__file__), "wsse_keyinfo.xml")) as fh:
                custom_key_info = etree.fromstring(fh.read())
            s3 = signer.sign(data, reference_uri=reference_uri, key=key, cert=crt, key_info=custom_key_info)
            self.assertTrue(
                s3.xpath(
                    "/ds:Signature/ds:KeyInfo/wsse:SecurityTokenReference", namespaces=dict(namespaces, wsse=wsse_ns)
                )
            )

            # Test setting both X509Data and KeyInfo
            s4 = XMLSigner().sign(data, reference_uri=reference_uri, key=key, cert=crt, always_add_key_value=True)
            try:
                XMLVerifier().verify(s4, x509_cert=crt, expect_config=example_cert_config)
            except InvalidSignature as e:
                self.assertIn("Expected to find 1 references, but found 2", str(e))
            expect_refs = etree.tostring(s4).decode().count("<ds:Reference")
            XMLVerifier().verify(
                s4,
                x509_cert=crt,
                ignore_ambiguous_key_info=True,
                expect_references=expect_refs,
                expect_config=example_cert_config,
            )

    def test_inclusive_namespaces_signing(self):
        # Test exclusive canonicalization with InclusiveNamespace PrefixList
        data = etree.fromstring(self.saml_test_vectors[0])
        reference_uri = "assertionId"
        signer = XMLSigner(
            c14n_algorithm=CanonicalizationMethod.EXCLUSIVE_XML_CANONICALIZATION_1_0,
            signature_algorithm=SignatureMethod.HMAC_SHA256,
        )
        sign_args = {"data": data, "reference_uri": reference_uri, "key": b"secret"}
        signed_with_insp = signer.sign(inclusive_ns_prefixes=["saml", "samlp", "ds"], **sign_args)
        self.assertEqual(
            signed_with_insp.find(".//ds:SignatureValue", namespaces=namespaces).text,
            "V3HwLySk6TmkPFlqtOU3xCln1Cga7v30rFqy8ZmJITA=",
        )
        signed_without_insp = signer.sign(**sign_args)
        self.assertEqual(
            signed_without_insp.find(".//ds:SignatureValue", namespaces=namespaces).text,
            "2Sk3E2SZwQCqX2STDkplw5JJp1ATAB5wsdRdQBAe/7o=",
        )
        # Test different c14n methods for signature and payload
        ref = SignatureReference(
            URI=reference_uri, c14n_method=CanonicalizationMethod.EXCLUSIVE_XML_CANONICALIZATION_1_0
        )
        sign_args = {"data": data, "reference_uri": [ref], "key": b"secret"}
        signed = signer.sign(**sign_args)
        self.assertEqual(
            signed.find(".//ds:SignatureValue", namespaces=namespaces).text,
            "2Sk3E2SZwQCqX2STDkplw5JJp1ATAB5wsdRdQBAe/7o=",
        )
        sign_args["reference_uri"][0] = replace(
            sign_args["reference_uri"][0], c14n_method=CanonicalizationMethod.CANONICAL_XML_1_0
        )
        signed2 = signer.sign(**sign_args)
        self.assertEqual(
            signed2.find(".//ds:SignatureValue", namespaces=namespaces).text,
            "8GPAVJstDxHyuoJqec8C0ssji4zfdXanu1YHGlWbfx0=",
        )

        # Test correct default c14n method for payload when c14n transform metadata is omitted
        def _build_transforms_for_reference(transforms_node, reference, exclude_c14n_transform_element=False):
            etree.SubElement(
                transforms_node, ds_tag("Transform"), Algorithm=SignatureConstructionMethod.enveloped.value
            )

        signer._build_transforms_for_reference = _build_transforms_for_reference
        signed3 = signer.sign(**sign_args)
        self.assertEqual(
            signed3.find(".//ds:SignatureValue", namespaces=namespaces).text,
            "/iezjApGBVMMUspj5WyZwIOEw30qLX3Gv576vwFMAbQ=",
        )
        XMLVerifier().verify(signed3, hmac_key=b"secret", require_x509=False)

    def test_excision_of_untrusted_comments(self):
        pass  # TODO: test comments excision

    def test_doctype_rejection(self):
        doc = """<!DOCTYPE samlp:Response [<!ATTLIST saml:Assertion xmlns:saml CDATA "urn:oasis:names:tc:SAML:2.0:assertion">]><samlp:Response xmlns:samlp="urn:oasis:names:tc:SAML:2.0:protocol" xmlns:saml="urn:oasis:names:tc:SAML:2.0:Assertion"><saml:Assertion Version="2.0" ID="_test">
          <saml:Subject><saml:NameID>admin@example.com</saml:NameID></saml:Subject>
          <ds:Signature xmlns:ds="http://www.w3.org/2000/09/xmldsig#"><ds:SignedInfo><ds:CanonicalizationMethod Algorithm="http://www.w3.org/2001/10/xml-exc-c14n#"/><ds:SignatureMethod Algorithm="http://www.w3.org/2001/04/xmldsig-more#rsa-sha256"/><ds:Reference URI="#_test"><ds:Transforms><ds:Transform Algorithm="http://www.w3.org/2000/09/xmldsig#enveloped-signature"/><ds:Transform Algorithm="http://www.w3.org/2001/10/xml-exc-c14n#"/></ds:Transforms><ds:DigestMethod Algorithm="http://www.w3.org/2001/04/xmlenc#sha256"/><ds:DigestValue>qMAYPT7tK9U5s0OuDLgiY7t3uXBgXxmM8doM849sH2g=</ds:DigestValue></ds:Reference></ds:SignedInfo><ds:SignatureValue>VfrFy9IakkV48zDp0NJxdueUPG8Ec9II0I9InWHDaQzIlNm+F8fwdvYU6JEoXoIKHv3Bj8beE9qcNh03xzL/l7DVtKV31YQc0+cylp/5YvkZBZHza643tKKPIXag3tR6Zo/wR+X+e1YuDlbb1oAOcl85Ob9ZPmW7wnVqu27kGratcYbU2vHh4jbYua3ZkPyUajwbw8O5R/LLIg3uko1oWdQxWnmNM9zoxLT3V5O7rYPp/gwvebhYTX6tnxkKrHK7CsslEINRbEDCXbpc0gT9TuADSP/aHrQmFN8eLXahpyBygYnNIdbil4usKfdcf2L13x03OkWiLdhvqMbOQZOV0g==</ds:SignatureValue><ds:KeyInfo><ds:X509Data><ds:X509Certificate>MIIC/zCCAeegAwIBAgIUZd6NULqQQPpHUImmpZ5d8KO0meYwDQYJKoZIhvcNAQEL
          BQAwDzENMAsGA1UEAwwEdGVzdDAeFw0yNjAzMDExNzExNTlaFw0yNjAzMDIxNzEx
          NTlaMA8xDTALBgNVBAMMBHRlc3QwggEiMA0GCSqGSIb3DQEBAQUAA4IBDwAwggEK
          AoIBAQDAyHLFxknSg8igmRlNJwSnZ1HzRtaqmLb6THv2cyNdGspvce6LmfOE/0dz
          KEqh7XVhvK3pMfsDi0NEjddyENA+IRZIcjQinBaG6d1+k/LmJybO+SBtopKbOMi2
          EsjlTbcOj/TzvEkdSJukHvZWd/AfUJcl7YWHTYCeevtad/ko454AfS6fGSWg4HXd
          7s6SI/RlcDW3VAzY19C6bIX8GPVW5aZZg0Dihe2QW1ghN5n/6Etp9No2zooBdV1f
          zq79xvECUdTSwGEvEZz92sxjFnOJKVFZetDuE+BylpYxnc7akiPQZbhHCeiTheiL
          yiDE2BVp6q2zxXuhNjbkXvVLI0qtAgMBAAGjUzBRMB0GA1UdDgQWBBQcgXR3Y2y/
          jjlgm1DyvNLu/+NN4TAfBgNVHSMEGDAWgBQcgXR3Y2y/jjlgm1DyvNLu/+NN4TAP
          BgNVHRMBAf8EBTADAQH/MA0GCSqGSIb3DQEBCwUAA4IBAQATqMPgzLiUaxJBBvKa
          +TyUTiH/ZFjGY3eYEWxbjzaBvRll8r09rd8roORdPr299EKKfDMn4N9l9X+nYvAY
          //sJ+NO54yO6uiWW6ScOqq9igj5Q6bnNgvuz/5PBai/i/sb8cFKHzY+TEIRnRMBb
          8LAynzKgh9IXyTvjeBCiIT06C0nP4tKIygIoXcESBzzLjOO9rxG9nLqznZYfUKMT
          4h8Lh2DO5VeLsZawPsR9VU99MjrYsMrcHPXdW42KUTY7IpjBcd69xI6lhwTOqOV0
          TStby5C4JWMZtMpJPwBJjczYSBsxx91OTDzMhQuEqH4WiCOcrBtqLjT7DSj6kAHx
          ea+x
          </ds:X509Certificate></ds:X509Data></ds:KeyInfo></ds:Signature></saml:Assertion></samlp:Response>"""

        with self.assertRaises(InvalidInput):
            XMLVerifier().verify(doc)

    def test_mismatched_key_value_with_x509_data(self):
        crt, key = self.load_example_keys()
        data = etree.parse(os.path.join(os.path.dirname(__file__), "example.xml")).getroot()
        signer = XMLSigner()
        signed = signer.sign(data, key=key, cert=crt, always_add_key_value=True)
        key_info = signed.find(".//ds:KeyInfo", namespaces=namespaces)
        key_value = key_info.find("ds:KeyValue", namespaces=namespaces)
        key_info.remove(key_value)
        mismatched_key = rsa.generate_private_key(public_exponent=65537, key_size=2048)
        signer._serialize_key_value(mismatched_key, key_info)
        signed_xml = etree.tostring(signed)

        with self.assertRaisesRegex(
            InvalidInput,
            "Both X509Data and KeyValue found and they represent different public keys",
        ):
            XMLVerifier().verify(signed_xml, x509_cert=crt, expect_config=example_cert_config)

        XMLVerifier().verify(
            signed_xml, x509_cert=crt, ignore_ambiguous_key_info=True, expect_config=example_cert_config
        )

    def test_mismatched_ecdsa_key_value_with_x509_data(self):
        crt, key = self.load_example_ecdsa_keys()
        data = etree.parse(os.path.join(os.path.dirname(__file__), "example.xml")).getroot()
        signer = XMLSigner(
            signature_algorithm=SignatureMethod.ECDSA_SHA384,
        )
        signed = signer.sign(data, key=key, cert=crt, always_add_key_value=True)
        key_info = signed.find(".//ds:KeyInfo", namespaces=namespaces)
        key_value = key_info.find("ds:KeyValue", namespaces=namespaces)
        key_info.remove(key_value)
        mismatched_key = ec.generate_private_key(curve=ec.SECP384R1())
        signer._serialize_key_value(mismatched_key, key_info)
        signed_xml = etree.tostring(signed)

        with self.assertRaisesRegex(
            InvalidInput,
            "Both X509Data and KeyValue found and they represent different public keys",
        ):
            XMLVerifier().verify(signed_xml, x509_cert=crt)

        XMLVerifier().verify(signed_xml, x509_cert=crt, ignore_ambiguous_key_info=True)

    def test_matched_ecdsa_key_value_with_x509_data(self):
        crt, key = self.load_example_ecdsa_keys()
        data = etree.parse(os.path.join(os.path.dirname(__file__), "example.xml")).getroot()
        signer = XMLSigner(
            signature_algorithm=SignatureMethod.ECDSA_SHA384,
        )
        signed = signer.sign(data, key=key, cert=crt, always_add_key_value=True)
        signed_xml = etree.tostring(signed)

        XMLVerifier().verify(signed_xml, x509_cert=crt, ignore_ambiguous_key_info=False)

    def test_ecdsa_key_value_coordinate_padding(self):
        # Fixed private scalars produce points with neither, only X, only Y, or both coordinates starting with zero.
        cases = (
            (ec.SECP256R1(), (1, 379, 43, 49350)),
            (ec.SECP384R1(), (1, 197, 176, 6394)),
            (ec.SECP521R1(), (3, 1, 9, 2)),
        )
        data = b"<root><a>1</a></root>"
        verification_time = datetime(2025, 1, 1, tzinfo=timezone.utc)
        for curve, private_values in cases:
            for private_value in private_values:
                key = ec.derive_private_key(private_value, curve)
                name = x509.Name([x509.NameAttribute(x509.NameOID.COMMON_NAME, "EC coordinate padding test")])
                cert = (
                    x509.CertificateBuilder()
                    .subject_name(name)
                    .issuer_name(name)
                    .public_key(key.public_key())
                    .serial_number(1)
                    .not_valid_before(datetime(2024, 1, 1, tzinfo=timezone.utc))
                    .not_valid_after(datetime(2026, 1, 1, tzinfo=timezone.utc))
                    .sign(key, hashes.SHA256())
                )
                for signer_class, verifier_class, cert_chain, config in (
                    (XMLSigner, XMLVerifier, None, SignatureConfiguration(require_x509=False)),
                    (XMLSigner, XMLVerifier, [cert], SignatureConfiguration()),
                    (XAdESSigner, XAdESVerifier, [cert], XAdESSignatureConfiguration()),
                ):
                    with self.subTest(
                        curve=curve.name,
                        private_value=private_value,
                        signer=signer_class.__name__,
                        with_certificate=cert_chain is not None,
                    ):
                        signed = signer_class(signature_algorithm=SignatureMethod.ECDSA_SHA256).sign(
                            etree.fromstring(data), key=key, cert=cert_chain, always_add_key_value=True
                        )
                        public_key = signed.find(".//dsig11:ECKeyValue/dsig11:PublicKey", namespaces=namespaces)
                        encoded_point = b64decode(public_key.text)
                        self.assertEqual(len(encoded_point), 1 + 2 * ((curve.key_size + 7) // 8))
                        self.assertEqual(encoded_point[0], 4)
                        self.assertEqual(
                            ec.EllipticCurvePublicKey.from_encoded_point(curve, encoded_point).public_numbers(),
                            key.public_key().public_numbers(),
                        )
                        result = verifier_class().verify(
                            etree.tostring(signed),
                            x509_cert=cert if cert_chain is not None else None,
                            expect_config=replace(config, verification_time=verification_time),
                        )
                        if isinstance(result, list):
                            result = result[0]
                        self.assertEqual(result.signed_data, data)

    def test_ws_security(self):
        wsse_dir = os.path.join(interop_dir, "ws-security", "ws.js")
        with open(os.path.join(wsse_dir, "examples", "server_public.pem"), "rb") as fh:
            crt = fh.read()
        data = etree.parse(os.path.join(wsse_dir, "test", "unit", "client", "files", "valid wss resp.xml"))
        XMLVerifier().verify(data, x509_cert=crt, validate_schema=False, expect_references=2, expect_config=sha1_ok)

        data = etree.parse(
            os.path.join(wsse_dir, "test", "unit", "client", "files", "invalid wss resp - changed content.xml")
        )
        with self.assertRaisesRegex(InvalidDigest, "Digest mismatch for reference 0"):
            XMLVerifier().verify(data, x509_cert=crt, validate_schema=False, expect_references=2, expect_config=sha1_ok)

    def test_psha1(self):
        from signxml.util import p_sha1

        a, b, c, d = (
            "grrlUUfhuNwlvQzQ4bV6TT3wA8ieZPltIf4+H7nIvCE=",
            "YLABh3ZmZyiO5gvVLZe9J4JPd9w59KGeTFwE85XlzxE=",
            "Wv3QzY84KfgwSkn1z3QV+LXEoo3nPraZPysJYtA3u4c=",
            "g/uYZmYX7rOm/X7UV4usrvjIPCiWMWwNZJL0ejvz6Y4=",
        )
        self.assertEqual(p_sha1(a, b), c)
        self.assertEqual(p_sha1(b, a), d)

    def test_xml_attacks(self):
        for filename in glob(os.path.join(os.path.dirname(__file__), "defusedxml-test-data", "*.xml")):
            with open(filename, "rb") as fh, self.assertRaises((InvalidInput, etree.XMLSyntaxError)):
                XMLVerifier().verify(fh.read())

    def test_signature_properties_with_detached_method(self):
        doc = etree.Element("Test", attrib={"Id": "mytest"})
        sigprop = etree.Element("{http://somenamespace}MyCustomProperty")
        sigprop.text = "Some Text"
        cert, key = self.load_example_keys()
        signature = XMLSigner(method=methods.detached).sign(
            doc, cert=cert, key=key, reference_uri="#mytest", signature_properties=sigprop
        )
        fulldoc = b"<root>" + etree.tostring(signature) + etree.tostring(doc) + b"</root>"
        XMLVerifier().verify(
            etree.fromstring(fulldoc), x509_cert=cert, expect_references=2, expect_config=example_cert_config
        )

    def test_signature_properties_with_detached_method_re_enveloping(self):
        doc = etree.Element("{http://somenamespace}Test", attrib={"Id": "mytest"})
        sigprop = etree.Element("{http://somenamespace}MyCustomProperty")
        sigprop.text = "Some Text"
        cert, key = self.load_example_keys()
        signer = XMLSigner(method=methods.detached, c14n_algorithm="http://www.w3.org/TR/2001/REC-xml-c14n-20010315")
        signer.namespaces["ns0"] = "http://enveloping.namespace"
        signature = signer.sign(doc, cert=cert, key=key, reference_uri="#mytest", signature_properties=sigprop)
        fulldoc = (
            b'<ns0:root xmlns:ns0="http://enveloping.namespace">'
            + etree.tostring(signature)
            + etree.tostring(doc)
            + b"</ns0:root>"
        )
        XMLVerifier().verify(
            etree.fromstring(fulldoc), x509_cert=cert, expect_references=2, expect_config=example_cert_config
        )

    def test_payload_c14n(self):
        doc = etree.fromstring('<abc xmlns="http://example.com"><foo xmlns="">bar</foo></abc>')
        self.assertEqual(
            XMLSignatureProcessor()._c14n(doc, algorithm=CanonicalizationMethod.CANONICAL_XML_1_1),
            b'<abc xmlns="http://example.com"><foo xmlns="">bar</foo></abc>',
        )

    def test_xmlns_insulation_of_reference_c14n(self):
        cert, key = self.load_example_keys()
        doc = etree.fromstring(
            '<rDE xmlns="http://example.com/ns1">'
            '<DE Id="target"><dDVId>9</dDVId><gOpeDE><iTipEmi>1</iTipEmi></gOpeDE></DE>'
            "</rDE>"
        )
        root = XMLSigner().sign(doc, cert=cert, key=key, reference_uri="#target")
        XMLVerifier().verify(root, x509_cert=cert, expect_config=example_cert_config)

    def test_include_c14n_transform_element_by_default(self):
        cert, key = self.load_example_keys()
        doc = etree.fromstring(
            '<rDE xmlns="http://example.com/ns1">'
            '<DE Id="target"><dDVId>9</dDVId><gOpeDE><!-- comment --><iTipEmi>1</iTipEmi></gOpeDE></DE>'
            "</rDE>"
        )
        root = XMLSigner().sign(doc, cert=cert, key=key, reference_uri="#target")
        XMLVerifier().verify(root, x509_cert=cert, expect_config=example_cert_config)
        transform_elements = root.findall(
            "ds:Signature/ds:SignedInfo/ds:Reference/ds:Transforms/ds:Transform", namespaces=namespaces
        )
        transform_algorithms = [el.attrib["Algorithm"] for el in transform_elements]
        self.assertEqual(len(transform_elements), 2)
        self.assertIn("http://www.w3.org/2000/09/xmldsig#enveloped-signature", transform_algorithms)
        self.assertIn("http://www.w3.org/2006/12/xml-c14n11", transform_algorithms)

    def test_exclude_c14n_transform_element_option(self):
        cert, key = self.load_example_keys()
        doc = etree.fromstring(
            '<rDE xmlns="http://example.com/ns1">'
            '<DE Id="target"><dDVId>9</dDVId><gOpeDE><!-- comment --><iTipEmi>1</iTipEmi></gOpeDE></DE>'
            "</rDE>"
        )
        root = XMLSigner(c14n_algorithm=CanonicalizationMethod.CANONICAL_XML_1_0_WITH_COMMENTS).sign(
            doc, cert=cert, key=key, reference_uri="#target", exclude_c14n_transform_element=True
        )

        # The default to use is CANONICAL_XML_1_1 (no comments), and since it's not specified in Transforms,
        # verification without specifying the reference canonicalization algorithm should fail.
        self.assertRaises(
            InvalidDigest,
            XMLVerifier().verify,
            root,
            x509_cert=cert,
            expect_config=example_cert_config,
        )

        # However, if we use the right configuration, it should verify correctly
        config = SignatureConfiguration(
            default_reference_c14n_method=CanonicalizationMethod.CANONICAL_XML_1_0_WITH_COMMENTS,
            verification_time=example_cert_verification_time,
        )
        XMLVerifier().verify(root, x509_cert=cert, expect_config=config)
        transform_elements = root.findall(
            "ds:Signature/ds:SignedInfo/ds:Reference/ds:Transforms/ds:Transform", namespaces=namespaces
        )
        transform_algorithms = [el.attrib["Algorithm"] for el in transform_elements]
        self.assertEqual(len(transform_elements), 1)
        self.assertIn("http://www.w3.org/2000/09/xmldsig#enveloped-signature", transform_algorithms)
        self.assertNotIn("http://www.w3.org/2006/12/xml-c14n11", transform_algorithms)

    def test_verify_config(self):
        data = etree.parse(self.example_xml_files[0]).getroot()
        cert, key = self.load_example_keys()
        signer = XMLSigner()
        signed = signer.sign(data, cert=cert, key=key)
        verifier = XMLVerifier()
        verifier.verify(signed, x509_cert=cert, expect_config=example_cert_config)
        config = SignatureConfiguration(location="./foo/bar/")
        with self.assertRaisesRegex(
            InvalidInput, "Expected to find XML element Signature in data using XPath ./foo/bar/ds:Signature"
        ):
            verifier.verify(signed, x509_cert=cert, expect_config=config)
        config = SignatureConfiguration(signature_methods=[])
        with self.assertRaisesRegex(InvalidInput, "Signature method RSA_SHA256 forbidden by configuration"):
            verifier.verify(signed, x509_cert=cert, expect_config=config)
        config = SignatureConfiguration(
            digest_algorithms=[DigestAlgorithm.SHA3_512], verification_time=example_cert_verification_time
        )
        with self.assertRaisesRegex(InvalidInput, "Digest algorithm SHA256 forbidden by configuration"):
            verifier.verify(signed, x509_cert=cert, expect_config=config)
        config = SignatureConfiguration(digest_algorithms=[], verification_time=example_cert_verification_time)
        with self.assertRaisesRegex(InvalidInput, "Digest algorithm SHA256 forbidden by configuration"):
            verifier.verify(signed, x509_cert=cert, expect_config=config)

    def test_sha1_policy(self):
        data = etree.parse(self.example_xml_files[0]).getroot()
        cert, key = self.load_example_keys()
        with self.assertRaisesRegex(InvalidInput, "SHA1-based algorithms are not supported"):
            XMLSigner(signature_algorithm=SignatureMethod.RSA_SHA1)
        signer = XMLSignerWithSHA1(signature_algorithm=SignatureMethod.RSA_SHA1, digest_algorithm=DigestAlgorithm.SHA1)
        signed = signer.sign(data, cert=cert, key=key)
        verifier = XMLVerifier()
        with self.assertRaisesRegex(InvalidInput, "Signature method RSA_SHA1 forbidden by configuration"):
            verifier.verify(signed, x509_cert=cert)
        verifier.verify(signed, x509_cert=cert, expect_config=sha1_ok_example_cert)


class TestStrictTransformPolicy(unittest.TestCase, LoadExampleKeys):
    enveloped_uri = SignatureConstructionMethod.enveloped.value
    base64_uri = "http://www.w3.org/2000/09/xmldsig#base64"
    c14n_uri = CanonicalizationMethod.CANONICAL_XML_1_1.value
    xpath_uri = "http://www.w3.org/TR/1999/REC-xpath-19991116"
    xslt_uri = "http://www.w3.org/TR/1999/REC-xslt-19991116"
    strict_config = SignatureConfiguration(
        strict_transform_policy=True, verification_time=example_cert_verification_time
    )

    def _copy_element(self, element):
        return etree.fromstring(etree.tostring(element))

    def _get_transforms_node(self, signed_root, reference_index=0):
        references = signed_root.findall(".//ds:Reference", namespaces=namespaces)
        return references[reference_index].find("ds:Transforms", namespaces=namespaces)

    def _set_transform_chain(self, signed_root, transform_uris, reference_index=0):
        mutated = self._copy_element(signed_root)
        transforms_node = self._get_transforms_node(mutated, reference_index)
        for child in list(transforms_node):
            transforms_node.remove(child)
        for uri in transform_uris:
            etree.SubElement(transforms_node, ds_tag("Transform"), Algorithm=uri)
        return mutated

    def _resign(self, signed_root):
        """
        Re-sign a mutated signature so that the outer SignatureValue and the reference DigestValue are both valid
        for the document as presented. Any rejection afterwards cannot be caused by a digest or signature mismatch.
        """
        from cryptography.hazmat.primitives.serialization import load_pem_private_key

        _, key_pem = self.load_example_keys()
        private_key = load_pem_private_key(key_pem, password=None)
        resigned = self._copy_element(signed_root)

        signed_info = resigned.find(".//ds:SignedInfo", namespaces=namespaces)
        c14n_method = signed_info.find("ds:CanonicalizationMethod", namespaces=namespaces).get("Algorithm")
        signature_method = SignatureMethod(
            signed_info.find("ds:SignatureMethod", namespaces=namespaces).get("Algorithm")
        )
        verifier = XMLVerifier()
        signed_info_c14n = verifier._c14n(
            signed_info, algorithm=CanonicalizationMethod(c14n_method)
        )
        signature = private_key.sign(signed_info_c14n, padding=PKCS1v15(), algorithm=hashes.SHA256())
        assert signature_method is SignatureMethod.RSA_SHA256
        resigned.find(".//ds:SignatureValue", namespaces=namespaces).text = b64encode(signature).decode()
        return resigned

    def _recompute_digest(self, signed_root, reference_index=0):
        """Recompute the reference DigestValue using the lenient transform processing path."""
        mutated = self._copy_element(signed_root)
        reference = mutated.findall(".//ds:Reference", namespaces=namespaces)[reference_index]
        transforms_node = reference.find("ds:Transforms", namespaces=namespaces)
        digest_alg = DigestAlgorithm(reference.find("ds:DigestMethod", namespaces=namespaces).get("Algorithm"))
        verifier = XMLVerifier()
        verifier.config = SignatureConfiguration()
        copied_root = verifier._fromstring(verifier._tostring(mutated))
        copied_signature = verifier._get_signature(copied_root)
        payload = verifier._resolve_reference(copied_root, reference)
        payload_c14n = verifier._apply_transforms(
            payload,
            transforms_node=transforms_node,
            signature=copied_signature,
            reference_index=reference_index,
            reference_uri=reference.get("URI"),
        )
        reference.find("ds:DigestValue", namespaces=namespaces).text = b64encode(
            verifier._get_digest(payload_c14n, digest_alg)
        ).decode()
        return mutated

    def _make_valid_enveloped_signature(self):
        cert, key = self.load_example_keys()
        data = etree.fromstring(
            '<root xmlns="http://example.com/ns1"><data Id="target"><value>1</value></data></root>'
        )
        signed_root = XMLSigner().sign(data, cert=cert, key=key, reference_uri="#target")
        return cert, signed_root

    def _assert_policy_rejection(self, signed_root, *, position, algorithm_fragment):
        cert, _ = self.load_example_keys()
        with self.assertRaises(InvalidInput) as context:
            XMLVerifier().verify(signed_root, x509_cert=cert, expect_config=self.strict_config)
        message = str(context.exception)
        self.assertIn("Strict transform policy violation", message)
        self.assertIn("reference 0", message)
        self.assertIn(f"position {position}", message)
        self.assertIn(algorithm_fragment, message)

    def test_signer_generated_chains_pass_strict_policy(self):
        cert, key = self.load_example_keys()
        data = etree.fromstring(
            '<root xmlns="http://example.com/ns1"><data Id="target"><value>1</value></data></root>'
        )

        # Default enveloped chain: enveloped-signature followed by canonicalization
        enveloped = XMLSigner().sign(self._copy_element(data), cert=cert, key=key, reference_uri="#target")
        XMLVerifier().verify(enveloped, x509_cert=cert, expect_config=self.strict_config)

        # Enveloped chain with c14n transform omitted: enveloped-signature only, default c14n applied implicitly
        enveloped_no_c14n = XMLSigner().sign(
            self._copy_element(data), cert=cert, key=key, reference_uri="#target",
            exclude_c14n_transform_element=True,
        )
        XMLVerifier().verify(enveloped_no_c14n, x509_cert=cert, expect_config=self.strict_config)

        # Detached and enveloping chains carry canonicalization only (or no transforms), no enveloped-signature
        detached = XMLSigner(method=methods.detached).sign(
            self._copy_element(data), cert=cert, key=key, reference_uri="#target"
        )
        detached_doc = etree.fromstring(b"<root>" + etree.tostring(detached) + etree.tostring(data) + b"</root>")
        XMLVerifier().verify(
            detached_doc, x509_cert=cert, expect_config=replace(self.strict_config, expect_references=1)
        )

        enveloping = XMLSigner(method=methods.enveloping).sign(
            etree.fromstring("<data>payload</data>"), cert=cert, key=key
        )
        XMLVerifier().verify(enveloping, x509_cert=cert, expect_config=self.strict_config)

    def test_default_config_keeps_lenient_behavior(self):
        cert, signed_root = self._make_valid_enveloped_signature()
        # A chain with an unrecognized transform embedded among supported ones is ignored by default mode.
        mutated = self._set_transform_chain(
            signed_root, [self.enveloped_uri, self.xpath_uri, self.c14n_uri]
        )
        mutated = self._recompute_digest(mutated)
        mutated = self._resign(mutated)
        XMLVerifier().verify(mutated, x509_cert=cert, expect_config=example_cert_config)
        # Strict mode rejects the same well-formed, cryptographically valid document.
        self._assert_policy_rejection(mutated, position=1, algorithm_fragment=self.xpath_uri)

    def test_unknown_transform_is_rejected(self):
        cert, signed_root = self._make_valid_enveloped_signature()
        for unknown_uri in (self.xpath_uri, self.xslt_uri, "http://example.com/custom-transform"):
            with self.subTest(unknown_uri=unknown_uri):
                mutated = self._set_transform_chain(signed_root, [unknown_uri, self.c14n_uri])
                mutated = self._recompute_digest(mutated)
                mutated = self._resign(mutated)
                self._assert_policy_rejection(mutated, position=0, algorithm_fragment=unknown_uri)

    def test_reordered_chain_is_rejected_not_silently_accepted(self):
        cert, signed_root = self._make_valid_enveloped_signature()

        # Canonicalization first, enveloped-signature second: lenient processing produces identical output to the
        # valid chain, so only the policy can be responsible for the rejection.
        reversed_chain = self._set_transform_chain(signed_root, [self.c14n_uri, self.enveloped_uri])
        reversed_chain = self._recompute_digest(reversed_chain)
        reversed_chain = self._resign(reversed_chain)
        XMLVerifier().verify(reversed_chain, x509_cert=cert, expect_config=example_cert_config)
        self._assert_policy_rejection(
            reversed_chain, position=0, algorithm_fragment=self.c14n_uri
        )

        # Duplicate enveloped-signature transforms.
        duplicated = self._set_transform_chain(
            signed_root, [self.enveloped_uri, self.enveloped_uri, self.c14n_uri]
        )
        duplicated = self._recompute_digest(duplicated)
        duplicated = self._resign(duplicated)
        XMLVerifier().verify(duplicated, x509_cert=cert, expect_config=example_cert_config)
        self._assert_policy_rejection(
            duplicated, position=1, algorithm_fragment=self.enveloped_uri
        )

        # Duplicate canonicalization transforms. The lenient implementation has no meaningful semantics for a second
        # c14n pass (it would feed the already-serialized bytes back into the c14n serializer), so strict mode is
        # expected to reject the chain on its policy before any transform is applied. The digest is computed over the
        # c14n output of the otherwise identical, supported chain (enveloped-signature + one c14n pass).
        supported = self._set_transform_chain(signed_root, [self.enveloped_uri, self.c14n_uri])
        supported = self._recompute_digest(supported)
        supported_digest = supported.find(
            ".//ds:Reference/ds:DigestValue", namespaces=namespaces
        ).text
        duplicated_c14n = self._set_transform_chain(
            signed_root, [self.enveloped_uri, self.c14n_uri, self.c14n_uri]
        )
        duplicated_c14n.find(".//ds:Reference/ds:DigestValue", namespaces=namespaces).text = supported_digest
        duplicated_c14n = self._resign(duplicated_c14n)
        self._assert_policy_rejection(
            duplicated_c14n, position=1, algorithm_fragment=self.c14n_uri
        )

    def test_base64_chain_ordering_is_enforced(self):
        cert, key = self.load_example_keys()
        payload_text = b"Hello, base64 transform!"
        doc = etree.fromstring(
            f'<data xmlns="http://example.com/ns1" Id="target">{b64encode(payload_text).decode()}</data>'
        )

        def build_with_chain(transform_uris):
            signer = XMLSigner(method=methods.detached)
            signed = signer.sign(self._copy_element(doc), cert=cert, key=key, reference_uri="#target")
            full_doc = etree.fromstring(b"<root>" + etree.tostring(signed) + etree.tostring(doc) + b"</root>")
            return self._set_transform_chain(full_doc, transform_uris)

        # base64 as the only transform is a valid chain.
        valid_b64 = build_with_chain([self.base64_uri])
        valid_b64 = self._recompute_digest(valid_b64)
        valid_b64 = self._resign(valid_b64)
        result = XMLVerifier().verify(
            valid_b64,
            x509_cert=cert,
            expect_config=replace(self.strict_config, expect_references=True),
        )
        self.assertEqual(result[0].signed_data, payload_text)

        # base64 followed by canonicalization is a type-incompatible combination (bytes fed to a node-set transform)
        # and also violates last-position ordering. Strict mode rejects it before touching the transforms. The digest
        # is computed over the decoded base64 payload, i.e. the output the chain would have produced up to its last
        # meaningful transform, so the outer signature and reference digest remain cryptographically valid.
        b64_then_c14n = build_with_chain([self.base64_uri, self.c14n_uri])
        b64_only = self._recompute_digest(build_with_chain([self.base64_uri]))
        b64_digest = b64_only.find(".//ds:Reference/ds:DigestValue", namespaces=namespaces).text
        b64_then_c14n.find(".//ds:Reference/ds:DigestValue", namespaces=namespaces).text = b64_digest
        b64_then_c14n = self._resign(b64_then_c14n)
        self._assert_policy_rejection(b64_then_c14n, position=0, algorithm_fragment=self.base64_uri)

        # Duplicate base64 transforms. The digest is the single-base64 chain's digest (the output of the first
        # decode), and the document is re-signed so only the transform policy can cause the rejection.
        duplicated_b64 = build_with_chain([self.base64_uri, self.base64_uri])
        duplicated_b64.find(".//ds:Reference/ds:DigestValue", namespaces=namespaces).text = b64_digest
        duplicated_b64 = self._resign(duplicated_b64)
        self._assert_policy_rejection(duplicated_b64, position=0, algorithm_fragment=self.base64_uri)

    def test_transform_after_bytes_producing_chain_is_rejected(self):
        cert, key = self.load_example_keys()
        payload_text = b"binary detached payload"
        doc = etree.fromstring(
            f'<data xmlns="http://example.com/ns1" Id="target">{b64encode(payload_text).decode()}</data>'
        )
        signer = XMLSigner(method=methods.detached)
        signed = signer.sign(self._copy_element(doc), cert=cert, key=key, reference_uri="#target")
        full_doc = etree.fromstring(b"<root>" + etree.tostring(signed) + etree.tostring(doc) + b"</root>")

        # A valid base64 chain turns the text node into bytes; appending an enveloped-signature transform then has no
        # node-set left to operate on. The digest is taken from the valid base64-only chain and the document is
        # re-signed, ensuring the policy check (not a signature mismatch) is what triggers the rejection.
        valid_b64_doc = self._set_transform_chain(full_doc, [self.base64_uri])
        valid_b64_doc = self._recompute_digest(valid_b64_doc)
        valid_b64_doc = self._resign(valid_b64_doc)
        bytes_then_enveloped = self._set_transform_chain(valid_b64_doc, [self.base64_uri, self.enveloped_uri])
        bytes_then_enveloped = self._resign(bytes_then_enveloped)
        with self.assertRaises(InvalidInput) as context:
            XMLVerifier().verify(
                bytes_then_enveloped,
                x509_cert=cert,
                expect_config=self.strict_config,
            )
        message = str(context.exception)
        self.assertIn("Strict transform policy violation", message)
        self.assertIn("reference 0", message)
        self.assertIn("position 0", message)
        self.assertIn(self.base64_uri, message)

    def test_type_incompatible_chain_is_rejected(self):
        # Directly exercise the validator with a chain whose first transform already produces bytes and whose second
        # transform requires a node-set. This ordering cannot occur with last-position enforcement via document-level
        # mutation, so the type-transition branch is covered at the validator level.
        verifier = XMLVerifier()
        verifier.config = self.strict_config
        transforms_node = etree.Element(ds_tag("Transforms"))
        etree.SubElement(transforms_node, ds_tag("Transform"), Algorithm=self.enveloped_uri)
        etree.SubElement(transforms_node, ds_tag("Transform"), Algorithm=self.base64_uri)
        etree.SubElement(transforms_node, ds_tag("Transform"), Algorithm=self.c14n_uri)
        transforms = verifier._findall(transforms_node, "Transform")
        with self.assertRaises(InvalidInput) as context:
            verifier._validate_transform_chain(
                transforms,
                initial_payload=b"already bytes",
                reference_index=2,
                reference_uri="#external",
            )
        message = str(context.exception)
        self.assertIn("Strict transform policy violation", message)
        self.assertIn("reference 2", message)
        self.assertIn("#external", message)
        self.assertIn("position 0", message)
        self.assertIn("already produced bytes", message)

    def test_base64_transform_requires_text_node_input(self):
        verifier = XMLVerifier()
        verifier.config = self.strict_config
        transforms_node = etree.Element(ds_tag("Transforms"))
        etree.SubElement(transforms_node, ds_tag("Transform"), Algorithm=self.base64_uri)
        transforms = verifier._findall(transforms_node, "Transform")
        empty_element = etree.fromstring('<data xmlns="http://example.com/ns1" Id="target"/>')
        with self.assertRaises(InvalidInput) as context:
            verifier._validate_transform_chain(
                transforms, initial_payload=empty_element, reference_index=0, reference_uri="#target"
            )
        self.assertIn("base64 transform requires an element node with text content", str(context.exception))


class TestXAdES(unittest.TestCase, LoadExampleKeys):
    expect_references: ClassVar[dict[str, int]] = {
        "factura_ejemplo2_32v1.xml": 3,
        "dss1770.xml": 3,
        "xades-fake-counter-signature.xml": 3,
        "Signature-X-SK_DIT-1.xml": 5,
        "Signature-X-HR_FIN-1.xml": 5,
        "TEST_S1a_C1a_InTL_VALID.xml": 3,
        "Signature-X-CZ_SEF-4.xml": 4,
        "Signature-X-FR_NOT-3.xml": 3,
        "Signature-X-CZ_SEF-5.xml": 4,
        "xades-counter-signature-injected.xml": 3,
        "11068_signed.xml": 3,
        "signature_property_signed.xml": 3,
        "nonconformant-Signature-X-ES-100.xml": 3,
        "nonconformant-Signature-X-ES-103.xml": 3,
        "nonconformant-dss1770.xml": 3,
    }
    signature_policy = XAdESSignaturePolicy(
        Identifier="urn:sbr:signature-policy:xml:2.0",
        Description="Test description",
        DigestMethod=DigestAlgorithm.SHA256,
        DigestValue="sVHhN1eqNH/PZ1B6h//ehyC1OwRQOrz/tJ3ZYaRrBgA=",
    )
    claimed_roles: ClassVar[list[str]] = ["signer"]
    data_object_format = XAdESDataObjectFormat(Description="Important Document", MimeType="text/xml")

    def test_xades_roundtrip(self):
        cert, key = self.load_example_keys()
        with open(os.path.join(os.path.dirname(__file__), "example.xml"), "rb") as fh:
            doc = etree.parse(fh)
        signer = XAdESSigner(
            signature_policy=self.signature_policy,
            claimed_roles=self.claimed_roles,
            data_object_format=self.data_object_format,
        )
        signed_doc = signer.sign(doc, key=key, cert=cert)

        for ref in signed_doc.findall(".//{http://www.w3.org/2000/09/xmldsig#}Reference"):
            if "SignedProperties" in ref.get("URI"):
                self.assertEqual(ref.get("Type"), "http://uri.etsi.org/01903#SignedProperties")

        verifier = XAdESVerifier()
        verify_results = verifier.verify(
            signed_doc,
            x509_cert=cert,
            expect_references=3,
            expect_signature_policy=self.signature_policy,
            expect_config=xades_sha1_ok_example_cert,
        )
        self.assertIsInstance(verify_results[1], XAdESVerifyResult)
        self.assertTrue(hasattr(verify_results[1], "signed_properties"))

    def test_xades_roundtrip_with_cert_chain(self):
        cert, key = self.load_example_keys()
        with open(os.path.join(os.path.dirname(__file__), "example-ca.pem"), "rb") as fh:
            ca_cert = fh.read()
        with open(os.path.join(os.path.dirname(__file__), "example.xml"), "rb") as fh:
            doc = etree.parse(fh)
        signer = XAdESSigner(
            signature_policy=self.signature_policy,
            claimed_roles=self.claimed_roles,
            data_object_format=self.data_object_format,
        )
        signed_doc = signer.sign(doc, key=key, cert=[cert, ca_cert])

        self.assertEqual(2, len(signed_doc.findall(".//ds:X509Certificate", namespaces=namespaces)))
        self.assertEqual(
            2,
            len(signed_doc.findall(".//xades:SigningCertificateV2/xades:Cert", namespaces=namespaces)),
        )

        verifier = XAdESVerifier()
        verify_results = verifier.verify(
            signed_doc,
            x509_cert=cert,
            expect_references=3,
            expect_signature_policy=self.signature_policy,
            expect_config=xades_sha1_ok_example_cert,
        )
        self.assertIsInstance(verify_results[1], XAdESVerifyResult)
        self.assertTrue(hasattr(verify_results[1], "signed_properties"))

    def test_xades_interop_examples(self):
        error_conditions = {
            "altered": InvalidSignature,
            "newlines": InvalidSignature,
            "unsupported-signature-algorithm": InvalidInput,
            "corrupted-cert": etree.DocumentInvalid,  # FIXME - flaky validation
            "cert-v2-wrong-digest": InvalidDigest,
            "wrong-sign-cert-digest": InvalidDigest,
            "sigPolStore-noDigest": InvalidInput,
        }
        for sig_file in glob(os.path.join(os.path.dirname(__file__), "xades", "*.xml")):
            print("Verifying", sig_file)
            with open(sig_file, "rb") as fh:
                doc = etree.parse(fh)
            cert = doc.find(".//{http://www.w3.org/2000/09/xmldsig#}X509Certificate").text
            expect_config = xades_sha1_ok
            verification_time = get_cert_midpoint_verification_time(cert)
            if verification_time is not None:
                expect_config = replace(expect_config, verification_time=verification_time)
            kwargs = {
                "x509_cert": cert,
                "expect_references": self.expect_references.get(os.path.basename(sig_file), 2),
                "expect_config": expect_config,
            }
            if "nonconformant" in sig_file:
                kwargs.update(validate_schema=False)
            if "sigPolStore" in sig_file:
                kwargs.update(expect_signature_policy=self.signature_policy)
            for condition, error in error_conditions.items():
                if condition in sig_file:
                    with self.assertRaises(error):
                        XAdESVerifier().verify(doc, **kwargs)
                    break
            else:
                XAdESVerifier().verify(doc, **kwargs)


if __name__ == "__main__":
    unittest.main()
