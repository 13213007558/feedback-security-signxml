from __future__ import annotations

import importlib.resources
import logging
import threading
from functools import lru_cache
from typing import Any, ClassVar
from xml.etree import ElementTree as stdlibElementTree

from cryptography.hazmat.primitives.asymmetric import ec
from cryptography.hazmat.primitives.hashes import Hash
from lxml import etree

from .algorithms import CanonicalizationMethod, DigestAlgorithm, digest_algorithm_implementations
from .exceptions import InvalidInput
from .util import namespaces

logger = logging.getLogger(__name__)


@lru_cache
def get_schema(schema_file: str) -> etree.XMLSchema:
    pkg_name = "signxml.xades.schemas" if schema_file.startswith("XAdES") else "signxml.schemas"

    pkg_resources = importlib.resources.files(pkg_name)
    with pkg_resources.joinpath(schema_file).open("r") as schema_fh:
        return etree.XMLSchema(etree.parse(schema_fh))


class XMLProcessor:
    _schemas: ClassVar[list[Any]] = []
    _schemas_lock = threading.Lock()
    schema_files: ClassVar[list[str]] = []
    _default_parser, _parser = None, None

    @classmethod
    def schemas(cls):
        with cls._schemas_lock:
            if "_schemas" not in cls.__dict__:
                cls._schemas = [get_schema(schema_file) for schema_file in cls.schema_files]
        return cls._schemas

    @property
    def parser(self):
        if self._parser is None:
            if self._default_parser is None:
                self._default_parser = etree.XMLParser(resolve_entities=False)
            return self._default_parser
        return self._parser

    def _fromstring(self, xml_string, **kwargs):
        xml_node = etree.fromstring(xml_string, parser=self.parser, **kwargs)
        docinfo = etree.ElementTree(xml_node).docinfo
        if docinfo.internalDTD is not None or docinfo.externalDTD is not None:
            raise InvalidInput("DTD declarations are not supported in XML input")
        for entity in xml_node.iter(etree.Entity):
            raise InvalidInput("Entities are not supported in XML input")
        return xml_node

    def _tostring(self, xml_node, **kwargs):
        return etree.tostring(xml_node, **kwargs)

    def get_root(self, data):
        if isinstance(data, (str, bytes)):
            return self._fromstring(data)
        elif isinstance(data, stdlibElementTree.Element):
            # TODO: add debug level logging statement re: performance impact here
            return self._fromstring(stdlibElementTree.tostring(data, encoding="utf-8"))
        else:
            # Create a separate copy of the node so we can modify the tree and avoid any c14n inconsistencies from
            # namespaces propagating from parent nodes. The lxml docs recommend using copy.deepcopy for this, but it
            # doesn't seem to preserve namespaces. It would be nice to find a less heavy-handed way of doing this.
            return self._fromstring(self._tostring(data))


class XMLSignatureProcessor(XMLProcessor):
    schema_files: ClassVar[list[str]] = ["xmldsig1-schema.xsd"]

    # See https://tools.ietf.org/html/rfc5656
    # ec.SECT* curves have been de-registered due to CVE-2026-26007
    # (https://github.com/pyca/cryptography/security/advisories/GHSA-r6ph-v2qm-q3c2)
    # List of disabled curves:
    # "urn:oid:1.3.132.0.1": ec.SECT163K1,
    # "urn:oid:1.3.132.0.26": ec.SECT233K1,
    # "urn:oid:1.3.132.0.27": ec.SECT233R1,
    # "urn:oid:1.3.132.0.16": ec.SECT283R1,
    # "urn:oid:1.3.132.0.36": ec.SECT409K1,
    # "urn:oid:1.3.132.0.37": ec.SECT409R1,
    # "urn:oid:1.3.132.0.38": ec.SECT571K1
    known_ecdsa_curves: ClassVar[dict[str, ec.EllipticCurve]] = {
        "urn:oid:1.2.840.10045.3.1.7": ec.SECP256R1(),
        "urn:oid:1.3.132.0.34": ec.SECP384R1(),
        "urn:oid:1.3.132.0.35": ec.SECP521R1(),
        "urn:oid:1.2.840.10045.3.1.1": ec.SECP192R1(),
        "urn:oid:1.3.132.0.33": ec.SECP224R1(),
    }
    known_ecdsa_curve_oids: ClassVar[dict[str, str]] = {curve.name: oid for oid, curve in known_ecdsa_curves.items()}

    excise_empty_xmlns_declarations = False

    id_attributes: tuple[str, ...] = ("Id", "ID", "id", "xml:id")

    _known_id_attribute_namespaces: ClassVar[dict[str, str]] = {
        "xml": "http://www.w3.org/XML/1998/namespace",
        "wsu": "http://docs.oasis-open.org/wss/2004/01/oasis-200401-wss-wssecurity-utility-1.0.xsd",
    }

    def _get_digest(self, data, algorithm: DigestAlgorithm):
        algorithm_implementation = digest_algorithm_implementations[algorithm]()
        hasher = Hash(algorithm=algorithm_implementation)
        hasher.update(data)
        return hasher.finalize()

    def _find(self, element, query, require=True, xpath=""):
        namespace = "ds"
        if ":" in query:
            namespace, _, query = query.partition(":")
        expression = f"{xpath}{namespace}:{query}"
        result = element.find(expression, namespaces=namespaces)

        if require and result is None:
            raise InvalidInput(f"Expected to find XML element {query} in {element.tag} using XPath {expression}")
        return result

    def _findall(self, element, query, xpath=""):
        namespace = "ds"
        if ":" in query:
            namespace, _, query = query.partition(":")
        return element.findall(f"{xpath}{namespace}:{query}", namespaces=namespaces)

    def _c14n(self, nodes, algorithm: CanonicalizationMethod, inclusive_ns_prefixes=None):
        exclusive, with_comments = False, False

        if algorithm.value.startswith("http://www.w3.org/2001/10/xml-exc-c14n#"):
            exclusive = True
        if algorithm.value.endswith("#WithComments"):
            with_comments = True

        if not isinstance(nodes, list):
            nodes = [nodes]

        c14n = b""
        for node in nodes:
            c14n += etree.tostring(
                node,
                method="c14n",
                exclusive=exclusive,
                with_comments=with_comments,
                inclusive_ns_prefixes=inclusive_ns_prefixes,
            )
        if exclusive is False and self.excise_empty_xmlns_declarations is True:
            # Incorrect legacy behavior. See also:
            # - https://github.com/XML-Security/signxml/issues/193
            # - http://www.w3.org/TR/xml-c14n, "namespace axis"
            # - http://www.w3.org/TR/xml-c14n2/#sec-Namespace-Processing
            c14n = c14n.replace(b' xmlns=""', b"")
        logger.debug("Canonicalized string (exclusive=%s, with_comments=%s): %s", exclusive, with_comments, c14n)
        return c14n

    def _resolve_reference(self, doc_root, reference, uri_resolver=None):
        uri = reference.get("URI")
        if uri is None:
            raise InvalidInput("References without URIs are not supported")
        elif uri == "":
            return doc_root
        elif uri.startswith("#xpointer("):
            raise InvalidInput("XPointer references are not supported")
            # doc_root.xpath(uri.lstrip("#"))[0]
        elif uri.startswith("#"):
            results = self._find_referenced_nodes(doc_root, uri.lstrip("#"))
            if len(results) > 1:
                raise InvalidInput(f"Ambiguous reference URI {uri} resolved to {len(results)} nodes")
            elif len(results) == 1:
                return results[0]
            raise InvalidInput(f"Unable to resolve reference URI: {uri}")
        else:
            if uri_resolver is None:
                raise InvalidInput(f"External URI dereferencing is not configured: {uri}")
            result = uri_resolver(uri)
            if result is None:
                raise InvalidInput(f"Unable to resolve reference URI: {uri}")
            return result

    def _find_referenced_nodes(self, doc_root, uri):
        # Match all configured ID attributes in a single query so that a value collision across
        # different ID attribute names (e.g. Id on one node, ID on another) is detected as
        # ambiguous regardless of search order. Each attribute name is matched exactly: an
        # unprefixed name matches only a no-namespace attribute of that name, and a prefixed
        # name (e.g. "xml:id") matches only an attribute in that prefix's namespace. Because a
        # single XPath query returns each node at most once, multiple equivalent ID attributes
        # on the same node are not treated as ambiguous.
        predicates = []
        for id_attribute in self.id_attributes:
            prefix, sep, local_name = id_attribute.partition(":")
            if sep:
                namespace = self._known_id_attribute_namespaces.get(prefix, namespaces.get(prefix))
                if namespace is None:
                    raise InvalidInput(f"Unknown namespace prefix in id_attribute: {id_attribute}")
                predicates.append(f"@*[local-name() = '{local_name}' and namespace-uri() = '{namespace}'] = $uri")
            else:
                predicates.append(f"@{id_attribute} = $uri")
        xpath_query = "//*[" + " or ".join(predicates) + "]"
        return doc_root.xpath(xpath_query, uri=uri)
