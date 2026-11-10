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
from signxml.algorithms import digest_algorithm_implementations
from signxml.util import ds_tag, xades_tag
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


def make_self_signed_cert(key, common_name, serial_number, not_before, not_after):
    name = x509.Name(
        [
            x509.NameAttribute(x509.oid.NameOID.COUNTRY_NAME, "US"),
            x509.NameAttribute(x509.oid.NameOID.ORGANIZATION_NAME, "SignXML Test"),
            x509.NameAttribute(x509.oid.NameOID.ORGANIZATIONAL_UNIT_NAME, "XAdES"),
            x509.NameAttribute(x509.oid.NameOID.COMMON_NAME, common_name),
        ]
    )
    return (
        x509.CertificateBuilder()
        .subject_name(name)
        .issuer_name(name)
        .public_key(key.public_key())
        .serial_number(serial_number)
        .not_valid_before(not_before)
        .not_valid_after(not_after)
        .add_extension(
            x509.KeyUsage(
                digital_signature=True,
                content_commitment=False,
                key_encipherment=False,
                data_encipherment=False,
                key_agreement=False,
                key_cert_sign=False,
                crl_sign=False,
                encipher_only=False,
                decipher_only=False,
            ),
            critical=True,
        )
        .sign(key, hashes.SHA256())
    )


class DeclaredCertXAdESSigner(XAdESSigner):
    """
    XAdES signer that declares arbitrary certificates in SigningCertificate/SigningCertificateV2,
    independent of the certificate chain written to KeyInfo. The SignedProperties it emits are
    signed normally, so any verification failure comes from the certificate binding declared in
    the signature properties, not from a broken outer signature.
    """

    def __init__(self, *args, declared_certs, emit_v1=False, emit_v2=True, **kwargs):
        super().__init__(*args, **kwargs)
        self.declared_certs = declared_certs
        self.emit_v1 = emit_v1
        self.emit_v2 = emit_v2
        self.signed_signature_properties_annotators = [
            self.add_signing_time,
            self.add_declared_signing_certificate,
            self.add_signature_policy_identifier,
            self.add_signature_production_place,
            self.add_signer_role,
        ]

    def _add_cert_node(self, parent, cert, digest_alg, with_issuer_serial):
        cert_node = etree.SubElement(parent, xades_tag("Cert"), nsmap=self.namespaces)
        cert_digest = etree.SubElement(cert_node, xades_tag("CertDigest"), nsmap=self.namespaces)
        etree.SubElement(cert_digest, ds_tag("DigestMethod"), nsmap=self.namespaces, Algorithm=digest_alg.value)
        digest_value_node = etree.SubElement(cert_digest, ds_tag("DigestValue"), nsmap=self.namespaces)
        digest_value_node.text = b64encode(cert.fingerprint(digest_algorithm_implementations[digest_alg]())).decode()
        if with_issuer_serial:
            issuer_serial = etree.SubElement(cert_node, xades_tag("IssuerSerial"), nsmap=self.namespaces)
            issuer_name = etree.SubElement(issuer_serial, ds_tag("X509IssuerName"), nsmap=self.namespaces)
            issuer_name.text = cert.issuer.rfc4514_string()
            serial_number = etree.SubElement(issuer_serial, ds_tag("X509SerialNumber"), nsmap=self.namespaces)
            serial_number.text = str(cert.serial_number)

    def add_declared_signing_certificate(self, signed_signature_properties, sig_root, signing_settings):
        if self.emit_v1:
            signing_cert = etree.SubElement(
                signed_signature_properties, xades_tag("SigningCertificate"), nsmap=self.namespaces
            )
            for cert in self.declared_certs:
                self._add_cert_node(signing_cert, cert, DigestAlgorithm.SHA1, with_issuer_serial=True)
        if self.emit_v2:
            signing_cert_v2 = etree.SubElement(
                signed_signature_properties, xades_tag("SigningCertificateV2"), nsmap=self.namespaces
            )
            for cert in self.declared_certs:
                self._add_cert_node(signing_cert_v2, cert, self.digest_alg, with_issuer_serial=False)


class RecordingXAdESVerifier(XAdESVerifier):
    """
    XAdES verifier that records which certificate it ultimately bound the signature to, and
    which SignedProperties element was being checked when certificate digest verification ran.
    """

    def _find_signing_cert(self, verify_result, certs):
        self.used_signing_cert = super()._find_signing_cert(verify_result, certs)
        return self.used_signing_cert

    def _verify_cert_digest(self, signing_cert_node, certs, signing_cert):
        self.checked_property = etree.QName(signing_cert_node).localname
        return super()._verify_cert_digest(signing_cert_node, certs=certs, signing_cert=signing_cert)


class TestXAdESSameKeyDifferentCerts(unittest.TestCase):
    """
    Regression tests for XAdES signatures where two certificates share one public key but carry
    different identities (issuer, serial number, validity period). Both certificates can verify
    the same signature value, but the certificate digest declared in SigningCertificate(V2) binds
    the signature to exactly one recognized identity.

    Expected behavior per the currently supported XAdES rules:
    - The signing certificate is the externally supplied x509_cert if given, otherwise the first
      KeyInfo certificate whose public key matches the signature key.
    - Every declared Cert digest must match some certificate available to the verifier, and the
      first declared Cert (the signing certificate reference) must match the signing certificate;
      subsequent Cert entries are chain certificate references checked against any known cert.
    - Exactly one of SigningCertificate / SigningCertificateV2 may be present.
    """

    verification_time = datetime(2026, 6, 1, tzinfo=timezone.utc)

    @classmethod
    def setUpClass(cls):
        cls.key = rsa.generate_private_key(public_exponent=65537, key_size=2048)
        cls.cert_a = make_self_signed_cert(
            cls.key,
            common_name="Recognized Signer",
            serial_number=1001,
            not_before=datetime(2026, 1, 1, tzinfo=timezone.utc),
            not_after=datetime(2027, 1, 1, tzinfo=timezone.utc),
        )
        cls.cert_b = make_self_signed_cert(
            cls.key,
            common_name="Unrecognized Signer",
            serial_number=2002,
            not_before=datetime(2026, 3, 1, tzinfo=timezone.utc),
            not_after=datetime(2026, 12, 1, tzinfo=timezone.utc),
        )
        cls.xades_config = XAdESSignatureConfiguration(
            signature_methods=list(SignatureMethod),
            digest_algorithms=list(DigestAlgorithm),
            verification_time=cls.verification_time,
        )
        cls.plain_config = replace(sha1_ok, verification_time=cls.verification_time, expect_references=3)
        # Local trust store containing both self-signed certificates; no external OCSP or
        # trust service is consulted, and verification runs at a fixed verification time.
        ca_file = tempfile.NamedTemporaryFile(suffix=".pem", delete=False)
        cls.addClassCleanup(os.unlink, ca_file.name)
        with ca_file:
            ca_file.write(cls.cert_a.public_bytes(serialization.Encoding.PEM))
            ca_file.write(cls.cert_b.public_bytes(serialization.Encoding.PEM))
        cls.ca_pem_file = ca_file.name

    def setUp(self):
        with open(os.path.join(os.path.dirname(__file__), "example.xml"), "rb") as fh:
            self.doc = etree.parse(fh)

    def sign(self, key_info_certs, declared_certs, emit_v1=False, emit_v2=True):
        signer = DeclaredCertXAdESSigner(
            signature_policy=TestXAdES.signature_policy,
            claimed_roles=TestXAdES.claimed_roles,
            data_object_format=TestXAdES.data_object_format,
            declared_certs=declared_certs,
            emit_v1=emit_v1,
            emit_v2=emit_v2,
        )
        return signer.sign(self.doc, key=self.key, cert=key_info_certs)

    def verify(self, signed_doc, x509_cert=None):
        verifier = RecordingXAdESVerifier()
        kwargs = {}
        if x509_cert is not None:
            kwargs["x509_cert"] = x509_cert
        verifier.verify(
            signed_doc,
            expect_references=3,
            expect_signature_policy=TestXAdES.signature_policy,
            expect_config=self.xades_config,
            ca_pem_file=self.ca_pem_file,
            **kwargs,
        )
        return verifier

    def assert_signature_layer_ok(self, signed_doc, cert):
        # The outer XML signature must verify with either same-key certificate, so that any
        # XAdES-level failure below comes from the certificate binding, not a broken signature.
        verify_results = XMLVerifier().verify(signed_doc, x509_cert=cert, expect_config=self.plain_config)
        self.assertEqual(3, len(verify_results))

    def assert_cert_binding_fails(self, signed_doc, x509_cert, error_regex, expected_used_cert, expected_property):
        self.assert_signature_layer_ok(signed_doc, x509_cert)
        verifier = RecordingXAdESVerifier()
        with self.assertRaisesRegex(InvalidDigest, error_regex):
            verifier.verify(
                signed_doc,
                x509_cert=x509_cert,
                expect_references=3,
                expect_signature_policy=TestXAdES.signature_policy,
                expect_config=self.xades_config,
                ca_pem_file=self.ca_pem_file,
            )
        self.assertEqual(expected_used_cert, verifier.used_signing_cert)
        self.assertEqual(expected_property, verifier.checked_property)

    def test_same_key_both_certs_verify_signature_value(self):
        # Premise: both certificates wrap the same public key, so the plain XML signature
        # layer accepts either one for the very same signed document.
        signed_doc = self.sign([self.cert_a], [self.cert_a])
        self.assert_signature_layer_ok(signed_doc, self.cert_a)
        self.assert_signature_layer_ok(signed_doc, self.cert_b)

    def test_declared_identity_matches_first_keyinfo_cert(self):
        # Success control: KeyInfo [A, B], declared [A, B], no external cert. The verifier
        # binds to the first KeyInfo cert with a matching key (A); the first declared Cert is
        # the signing certificate reference and the second is a chain certificate reference.
        signed_doc = self.sign([self.cert_a, self.cert_b], [self.cert_a, self.cert_b])
        verifier = self.verify(signed_doc)
        self.assertEqual(self.cert_a, verifier.used_signing_cert)
        self.assertEqual("SigningCertificateV2", verifier.checked_property)

    def test_declared_identity_matches_external_x509_cert(self):
        # Success control: KeyInfo [B, A] but x509_cert=A. The external certificate parameter
        # wins over KeyInfo order, and the declared digest of A is accepted.
        signed_doc = self.sign([self.cert_b, self.cert_a], [self.cert_a, self.cert_b])
        verifier = self.verify(signed_doc, x509_cert=self.cert_a)
        self.assertEqual(self.cert_a, verifier.used_signing_cert)

    def test_keyinfo_order_selects_other_identity(self):
        # KeyInfo [B, A], declared signing cert A, no external cert: the verifier binds to B
        # (first KeyInfo cert with a matching key), so the declared digest of A is rejected
        # at the signing certificate binding layer.
        signed_doc = self.sign([self.cert_b, self.cert_a], [self.cert_a, self.cert_b])
        self.assert_signature_layer_ok(signed_doc, self.cert_b)
        verifier = RecordingXAdESVerifier()
        with self.assertRaisesRegex(InvalidDigest, "Digest mismatch for signing certificate digest"):
            verifier.verify(
                signed_doc,
                expect_references=3,
                expect_signature_policy=TestXAdES.signature_policy,
                expect_config=self.xades_config,
                ca_pem_file=self.ca_pem_file,
            )
        self.assertEqual(self.cert_b, verifier.used_signing_cert)
        self.assertEqual("SigningCertificateV2", verifier.checked_property)

    def test_external_x509_cert_other_identity(self):
        # KeyInfo [A], declared A, but x509_cert=B: B's key verifies the signature value, yet
        # the declared digest binds the signature to A, so verification fails at the signing
        # certificate binding layer.
        signed_doc = self.sign([self.cert_a], [self.cert_a])
        self.assert_cert_binding_fails(
            signed_doc,
            x509_cert=self.cert_b,
            error_regex="Digest mismatch for signing certificate digest",
            expected_used_cert=self.cert_b,
            expected_property="SigningCertificateV2",
        )

    def test_declared_cert_absent_from_keyinfo(self):
        # KeyInfo [A], declared B, x509_cert=A: B's digest matches no certificate available to
        # the verifier, so verification fails at the certificate digest layer.
        signed_doc = self.sign([self.cert_a], [self.cert_b])
        self.assert_cert_binding_fails(
            signed_doc,
            x509_cert=self.cert_a,
            error_regex="^Digest mismatch for certificate digest$",
            expected_used_cert=self.cert_a,
            expected_property="SigningCertificateV2",
        )

    def test_chain_cert_declared_as_signing_cert(self):
        # KeyInfo [A, B], declared [B, A]: every declared digest matches some known
        # certificate, but the first declared Cert (the signing certificate reference) points
        # at chain certificate B while the recognized identity is A.
        signed_doc = self.sign([self.cert_a, self.cert_b], [self.cert_b, self.cert_a])
        self.assert_cert_binding_fails(
            signed_doc,
            x509_cert=self.cert_a,
            error_regex="Digest mismatch for signing certificate digest",
            expected_used_cert=self.cert_a,
            expected_property="SigningCertificateV2",
        )

    def test_legacy_signing_certificate_v1_only(self):
        # Success control with only the legacy SigningCertificate (SHA1 digest) present.
        signed_doc = self.sign([self.cert_a], [self.cert_a], emit_v1=True, emit_v2=False)
        verifier = self.verify(signed_doc, x509_cert=self.cert_a)
        self.assertEqual(self.cert_a, verifier.used_signing_cert)
        self.assertEqual("SigningCertificate", verifier.checked_property)

    def test_legacy_signing_certificate_v1_other_identity(self):
        # Only SigningCertificate present, declaring B while KeyInfo carries A.
        signed_doc = self.sign([self.cert_a], [self.cert_b], emit_v1=True, emit_v2=False)
        self.assert_cert_binding_fails(
            signed_doc,
            x509_cert=self.cert_a,
            error_regex="^Digest mismatch for certificate digest$",
            expected_used_cert=self.cert_a,
            expected_property="SigningCertificate",
        )

    def test_both_signing_certificate_versions_rejected(self):
        # Current rule: exactly one of SigningCertificate / SigningCertificateV2 may be
        # present, even when both declare the correct certificate.
        signed_doc = self.sign([self.cert_a], [self.cert_a], emit_v1=True, emit_v2=True)
        self.assert_signature_layer_ok(signed_doc, self.cert_a)
        verifier = RecordingXAdESVerifier()
        with self.assertRaisesRegex(
            InvalidInput, "Expected to find exactly one of xades:SigningCertificate or xades:SigningCertificateV2"
        ):
            verifier.verify(
                signed_doc,
                x509_cert=self.cert_a,
                expect_references=3,
                expect_signature_policy=TestXAdES.signature_policy,
                expect_config=self.xades_config,
                ca_pem_file=self.ca_pem_file,
            )
        self.assertEqual(self.cert_a, verifier.used_signing_cert)


if __name__ == "__main__":
    unittest.main()
