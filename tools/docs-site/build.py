#!/usr/bin/env python3
# Copyright (c) 2026 the Nonadditivity project contributors.
# All rights reserved. See COPYRIGHT.md for licensing and attribution.
"""Build the offline reader site from committed metadata and exact Lean sources.

Python standard library only. The output has no network dependencies. `--check`
checks byte-for-byte freshness, links, line anchors, source downloads, and search
entries without writing files. This is a documentation check, not a proof check.
"""

from __future__ import annotations

import argparse
import base64
import codecs
from collections import defaultdict, deque
import gzip
import hashlib
import html
from html.parser import HTMLParser
import io
import json
import os
from pathlib import Path, PurePosixPath
import re
import sys
from urllib.parse import unquote, urlsplit


ROOT = Path(__file__).resolve().parents[2]
TOOLS = Path(__file__).resolve().parent
OUT = ROOT / "html"
REPO = "https://github.com/JWang226/Holevo-Additivity-Gap"
SITE = "https://JWang226.github.io/Holevo-Additivity-Gap/"
COPYRIGHT = "Copyright (c) 2026 the Nonadditivity project contributors. All rights reserved."
NAV = [("Overview", "index.html"), ("Start here", "guide/introduction.html"),
       ("Concepts", "concepts/index.html"), ("Results", "results.html"),
       ("Proof route", "route.html"), ("Verify", "verify.html")]
LEAN_NAV = [("Proof map", "dependencies.html"), ("Declarations", "declarations.html"),
            ("Modules", "modules.html"), ("Imports", "imports.html"),
            ("Documents", "docs/index.html"), ("About", "about.html")]
STAGES = [
    ("Actual channels and entropy", "Begin with finite density matrices, concrete Kraus channels, output ensembles, and entropy. The channel endpoints refer to these physical objects.",
     ["purity-entropy", "bell-entropy"],
     ["StateEnsembles", "QuantumHolevo", "BellOutput", "BlockBell"]),
    ("Free comparison and finite Haar estimates", "The free-group norm bound is proved. Actual Haar integration and finite matrix moment estimates supply the quantitative input, rather than an assumed strong-convergence theorem.",
     ["free-collins-youn", "haar-moment-range", "universal-factorization"],
     ["CollinsYounProduct", "HaarAveraging", "HaarWeingartenGram", "HaarIteratedExpectation"]),
    ("Repaired combinatorial counts", "The revised manuscript incorporates two repaired intermediate estimates. The proof library includes literal counterexamples and the replacements used by the channel construction.",
     ["correction-important-times", "correction-middle-runs"],
     ["HaarPathExplorationCounterexample", "HaarPathRunCounterexample", "HaarSharpCounting", "HaarRefinedCoefficientBound"]),
    ("Prescribed dimensions and the channel witness", "The finite expectation bound feeds the structured certificate and channel construction. The main theorem has only its displayed numerical hypotheses and gives the supplementary single-use lower bound on the same witness.",
     ["prescribed-norm-certificate", "prescribed-dimensions", "favorable-probability"],
     ["StructuredHaarConsequences", "HaarPrescribedBound", "HaarPrescribedProbability"]),
    ("Conversion and qualitative separation", "Switch and Weyl extensions convert entropy bounds into Holevo bounds. A separate deterministic finite-moment and damping construction gives the exact qualitative endpoints and positivity.",
     ["weyl-all-uses", "qualitative-realization", "small-large-and-sequence"],
     ["Conversion", "WeylPowersEntropy", "ExactQualitative", "DeterministicConsequences"]),
    ("Operational coding and capacity", "Classical capacity is independently defined through actual codes and vanishing average decoding error. Spectral packing and the weak converse prove its equality with regularized Holevo information.",
     ["operational-coding", "capacity-gain", "simultaneous-separation"],
     ["QuantumCodingHSW", "QuantumCodingSequential", "OperationalCodingTheorem", "OperationalConsequences"]),
    ("Asymptotics and precise scope", "Read the two-use ratio, output scaling, input costs, and the fixed-channel regrouping limit. The catalog also records unproved general convergence predicates and broader manuscript claims.",
     ["two-use-ratio", "fixed-k-scaling", "input-size-expansion", "guaranteed-gap-fraction", "growing-family-cost", "fixed-channel-regrouping", "generic-haar-convergence", "background-generality", "undamped-all-dimensions"],
     ["HaarPrescribedScaling", "HaarInputScaling", "PrescribedCostCapacity", "HolevoPowerGap"]),
]


def esc(value: object) -> str:
    return html.escape(str(value), quote=True)


def pretty(value: object) -> bytes:
    return (json.dumps(value, indent=2, ensure_ascii=False) + "\n").encode()


def hidden_declaration(record: dict) -> bool:
    """Use exported Lean predicates, not an independently inferred name rule."""
    return bool(record["is_internal"] or record["is_private"] or record.get("is_internal_detail", False))


def mask_lean(source: str) -> str:
    """Hide nested comments and strings, preserving source offsets/newlines."""
    out = list(source)
    i = 0
    depth = 0
    string = False
    line_comment = False
    while i < len(source):
        if line_comment:
            if source[i] == "\n":
                line_comment = False
            else:
                out[i] = " "
            i += 1
        elif depth:
            if source.startswith("/-", i):
                out[i:i+2] = "  "
                depth += 1
                i += 2
            elif source.startswith("-/", i):
                out[i:i+2] = "  "
                depth -= 1
                i += 2
            else:
                if source[i] != "\n":
                    out[i] = " "
                i += 1
        elif string:
            if source[i] == "\\":
                out[i] = " "
                if i + 1 < len(source):
                    if source[i+1] != "\n":
                        out[i+1] = " "
                    i += 2
                else:
                    i += 1
            else:
                if source[i] == '"':
                    string = False
                if source[i] != "\n":
                    out[i] = " "
                i += 1
        elif source.startswith("/-", i):
            depth = 1
            out[i:i+2] = "  "
            i += 2
        elif source.startswith("--", i):
            line_comment = True
            out[i:i+2] = "  "
            i += 2
        elif source[i] == '"':
            string = True
            out[i] = " "
            i += 1
        else:
            i += 1
    if depth or string:
        raise ValueError("Unterminated Lean comment or string in documentation input")
    return "".join(out)


def declaration_header(source: str, name: str) -> tuple[str | None, int | None]:
    """Conservatively quote a unique literal header up to its outer `:=`.

    Does not reconstruct elaborated types or declaration dependencies. If a
    declaration is ambiguous or its syntax is outside this small recognizer,
    the page links to full source instead of fabricating a statement.
    """
    masked = mask_lean(source)
    short = name.rsplit(".", 1)[-1]
    pattern = re.compile(r"(?m)^(?:private\s+|protected\s+|noncomputable\s+)?(?:theorem|lemma|def|abbrev)\s+(?:[\w.]+\.)?" + re.escape(short) + r"(?=\s|[:({\[])")
    matches = list(pattern.finditer(masked))
    if len(matches) != 1:
        return None, None
    start = matches[0].start()
    line = source.count("\n", 0, start) + 1
    depth = 0
    i = matches[0].end()
    limit = min(len(source), start + 18000)
    while i < limit:
        char = masked[i]
        if char in "([{⦃":
            depth += 1
        elif char in ")]}⦄":
            depth -= 1
            if depth < 0:
                return None, line
        elif depth == 0 and masked.startswith(":=", i):
            header = source[start:i].rstrip()
            if ":" not in mask_lean(header):
                return None, line
            return header, line
        if i > matches[0].end() and depth == 0 and char == "\n":
            next_line = masked[i+1:].split("\n", 1)[0]
            if re.match(r"(?:theorem|lemma|def|namespace|end)\b", next_line):
                return None, line
        i += 1
    return None, line


def command(text: str, label: str = "Copy command") -> str:
    statement = label == "Copy statement"
    return '<div class="command' + (' statement' if statement else '') + '"><button class="copy" type="button" aria-label="' + esc(label) + '">' + ('Copy statement' if statement else 'Copy') + '</button><pre><code>' + esc(text.rstrip()) + '</code></pre></div>'


class Site:
    def __init__(self) -> None:
        self.outputs: dict[str, bytes] = {}
        self.inputs: dict[str, str] = {}
        self.search: list[dict[str, object]] = []
        self.meta = json.loads(self.read("metadata/results.json"))
        self.results = self.meta["results"]
        self.result_by_id = {x["id"]: x for x in self.results}
        self.modules: dict[str, dict] = {}
        self.used_by: dict[str, list[str]] = defaultdict(list)
        self.module_results: dict[str, list[dict]] = defaultdict(list)
        self.headers: dict[str, tuple[str | None, int | None]] = {}
        self.declaration_meta = json.loads(self.read("metadata/declarations.json"))
        self.declarations = {record["name"]: record for record in self.declaration_meta["declarations"]}
        if len(self.declarations) != len(self.declaration_meta["declarations"]):
            raise ValueError("Duplicate names in Lean declaration export")
        self.declaration_urls = {name: "declarations/" + hashlib.sha256(name.encode()).hexdigest()[:24] + ".html" for name in self.declarations}
        if len(set(self.declaration_urls.values())) != len(self.declaration_urls):
            raise ValueError("Declaration URL hash collision")
        self.declaration_users: dict[str, list[str]] = defaultdict(list)
        self.module_declarations: dict[str, list[str]] = defaultdict(list)
        self.declaration_results: dict[str, list[dict]] = defaultdict(list)
        self.validate_declaration_export()
        for name, record in self.declarations.items():
            self.module_declarations[record["module"]].append(name)
            for dependency in record["project_dependencies"]:
                self.declaration_users[dependency].append(name)
        self.docs: dict[str, str] = {}
        self.ci_record = self.meta["verification_current"]["record"]
        self.ci_excerpt = self.meta["verification_current"]["log_excerpt"]
        self.ci = json.loads(self.read(self.ci_record))
        if self.ci["commit"] != self.meta["verification_current"]["commit"]:
            raise ValueError("Current CI metadata disagrees with the retained verification record")
        proof_paths = list((ROOT / "Nonadditivity").glob("*.lean"))
        proof_paths += [ROOT / name for name in ["Nonadditivity.lean", "Audit.lean", "All.lean"]]
        for path in sorted(proof_paths):
            rel = path.relative_to(ROOT).as_posix()
            source = self.read(rel)
            module = rel[:-5].replace("/", ".")
            imports = re.findall(r"(?m)^import\s+([\w.]+)\s*$", mask_lean(source))
            self.modules[module] = {"path": rel, "source": source, "imports": imports}
            self.emit("source/" + rel, source)
        for name, module in self.modules.items():
            for imp in module["imports"]:
                self.used_by[imp].append(name)
        for name, record in self.declarations.items():
            if record["module"] not in self.modules:
                raise ValueError("Exported declaration refers to a module outside the source catalog: " + name)
        for result in self.results:
            for ref in result["lean"]:
                module_name = ref["file"][:-5].replace("/", ".")
                if module_name not in self.modules:
                    raise ValueError("Result references unavailable module: " + ref["file"])
                self.module_results[module_name].append(result)
                if ref["declaration"] not in self.declarations:
                    raise ValueError("Mapped declaration absent from Lean export: " + ref["declaration"])
                self.declaration_results[ref["declaration"]].append(result)
                self.headers[ref["declaration"]] = declaration_header(self.modules[module_name]["source"], ref["declaration"])
        doc_paths = ["README.md", "PROOF-PATH.md", "COPYRIGHT.md", "THIRD_PARTY_NOTICES.md", "verification/README.md", "ComparatorChallenges/README.md"]
        doc_paths += [p.relative_to(ROOT).as_posix() for p in sorted((ROOT / "docs").glob("*.md"))]
        for rel in doc_paths:
            self.docs[rel] = self.read(rel)
            self.emit("source/" + rel, self.docs[rel])
        source_paths = ["paper/nonadditivity.tex", "formalization.yaml", "metadata/results.json", "metadata/declarations.json", self.ci_record, self.ci_excerpt, "Audit.lean", "All.lean", "Nonadditivity.lean", "lean-toolchain", "lake-manifest.json", "verification/lean/run.sh", "verification/comparator/run.sh", "requirements-validation.txt", "check.sh"]
        # Historical CI evidence remains downloadable when repository documents
        # retain links to an earlier checked source commit.
        for pattern in ["github-actions-*.json", "github-actions-*-excerpt.log"]:
            source_paths += [p.relative_to(ROOT).as_posix() for p in sorted((ROOT / "verification").glob(pattern))]
        source_paths += [p.relative_to(ROOT).as_posix() for p in sorted((ROOT / "ComparatorChallenges").glob("*")) if p.suffix in {".lean", ".json"}]
        for rel in source_paths:
            self.emit("source/" + rel, self.read(rel))
        # Track the generator and its own assets in the deterministic manifest.
        for name in ["build.py", "site.css", "site.js", "dependencies.js", "proof-graph.json", "README.md"]:
            rel = "tools/docs-site/" + name
            if (ROOT / rel).exists():
                self.read(rel)
        self.read("tools/docs-site/math.js")
        self.load_reader()

    def load_reader(self) -> None:
        self.reader = json.loads(self.read("tools/docs-site/reader/index.json"))
        if self.reader.get("schema_version") != 1:
            raise ValueError("Unsupported mathematical reader schema")
        self.reader_text: dict[str, str] = {}
        self.reader_by_decl: dict[str, list[dict]] = defaultdict(list)
        for group in ("guides", "concepts", "results", "stages"):
            items = self.reader[group]
            if len({item["id"] for item in items}) != len(items):
                raise ValueError("Duplicate mathematical reader page: " + group)
            for item in items:
                if not re.fullmatch(r"[a-z0-9-]+", item["id"]):
                    raise ValueError("Invalid mathematical reader ID")
                if group == "results":
                    item["title"] = self.result_by_id[item["id"]]["name"]
                if group == "stages":
                    item["title"] = STAGES[int(item["id"]) - 1][0]
                item["source"] = "tools/docs-site/reader/" + group + "/" + item["id"] + ".md"
                item["category"] = group
                item["page"] = (("guide" if group == "guides" else group) + "/" + item["id"] + ".html") if group != "stages" else "route.html#stage-" + item["id"]
                text = self.read(item["source"])
                self.reader_text[item["source"]] = text
                self.emit("source/" + item["source"], text)
                names = set(re.findall(r"\]\(lean:([^\s)]+)\)", text))
                if group == "results":
                    if item["id"] not in self.result_by_id:
                        raise ValueError("Unknown explained result " + item["id"])
                    names.update(ref["declaration"] for ref in self.result_by_id[item["id"]]["lean"])
                for name in sorted(names):
                    if name not in self.declarations:
                        raise ValueError("Unknown Lean correspondence in reader: " + name)
                    self.reader_by_decl[name].append(item)
                item["declarations"] = sorted(names)
        if {item["id"] for item in self.reader["results"]} != self.result_by_id.keys():
            raise ValueError("Every result needs a mathematical explanation")
        if {item["id"] for item in self.reader["stages"]} != {str(i) for i in range(1, len(STAGES) + 1)}:
            raise ValueError("Every proof stage needs an explanation")

    def read(self, rel: str) -> str:
        data = (ROOT / rel).read_bytes()
        self.inputs[rel] = hashlib.sha256(data).hexdigest()
        return data.decode("utf-8")

    def emit(self, rel: str, content: str | bytes) -> None:
        self.outputs[rel] = content.encode("utf-8") if isinstance(content, str) else content

    def validate_declaration_export(self) -> None:
        """Refuse stale source provenance or dangling project-constant edges."""
        if self.declaration_meta.get("schema_version") != 1:
            raise ValueError("Unsupported Lean declaration export schema")
        if self.declaration_meta["count"] != len(self.declarations):
            raise ValueError("Declaration count disagrees with exported records")
        provenance = self.declaration_meta["provenance"]
        hashes = provenance["source_sha256"]
        required = {p.relative_to(ROOT).as_posix() for p in (ROOT / "Nonadditivity").glob("*.lean")}
        required.update({"Nonadditivity.lean", "Audit.lean", "All.lean", "lean-toolchain", "lake-manifest.json"})
        if not required.issubset(hashes):
            raise ValueError("Declaration export provenance misses sources: " + ", ".join(sorted(required - set(hashes))))
        for rel, expected in hashes.items():
            if rel.startswith("/") or ".." in PurePosixPath(rel).parts:
                raise ValueError("Unsafe export provenance path: " + rel)
            data = (ROOT / rel).read_bytes()
            actual = hashlib.sha256(data).hexdigest()
            self.inputs[rel] = actual
            if actual != expected:
                raise ValueError("Stale Lean declaration export: " + rel + "; rerun the declaration exporter")
        for name, record in self.declarations.items():
            if record["file"] != record["module"].replace(".", "/") + ".lean":
                raise ValueError("Declaration file/module mismatch: " + name)
            if not isinstance(record["type"], str) or not record["type"].strip():
                raise ValueError("Empty elaborated type: " + name)
            if record.get("type_encoding") == "gzip+base64":
                self.validate_full_type(name, record)
            elif record.get("type_encoding") not in {None, "utf-8"}:
                raise ValueError("Unsupported elaborated type encoding: " + name)
            combined = set(record["type_dependencies"]) | set(record["value_dependencies"])
            expected = combined & self.declarations.keys()
            if expected != set(record["project_dependencies"]):
                raise ValueError("Inconsistent project dependencies: " + name)
            missing = set(record["project_dependencies"]) - self.declarations.keys()
            if missing:
                raise ValueError("Unknown project dependency: " + name + ": " + ", ".join(sorted(missing)))

    def validate_full_type(self, name: str, record: dict) -> None:
        """Stream one exact type artifact; validate canonical kernel DAG references."""
        packed = base64.b64decode(record["type"], validate=True)
        digest = hashlib.sha256()
        decoder = codecs.getincrementaldecoder("utf-8")()
        count = 0
        representation = record.get("type_representation", "lean-fully-explicit-text-v1")
        if representation not in {"lean-kernel-expr-dag-v1", "lean-fully-explicit-text-v1"}:
            raise ValueError("Unknown full type representation: " + name)
        dag_text = []
        with gzip.GzipFile(fileobj=io.BytesIO(packed)) as stream:
            while chunk := stream.read(65536):
                count += len(chunk)
                digest.update(chunk)
                text = decoder.decode(chunk)
                if representation == "lean-kernel-expr-dag-v1":
                    dag_text.append(text)
                elif "⋯" in text:
                    raise ValueError("Full type contains pretty-printer elision: " + name)
        decoder.decode(b"", final=True)
        if count != record["type_uncompressed_bytes"] or digest.hexdigest() != record["type_sha256"]:
            raise ValueError("Compressed full type integrity mismatch: " + name)
        if count == 0:
            raise ValueError("Empty full type payload: " + name)
        if representation == "lean-kernel-expr-dag-v1":
            self.validate_type_dag(name, json.loads("".join(dag_text)))

    def validate_type_dag(self, name: str, dag: dict) -> None:
        if dag.get("format") != "lean-kernel-expr-dag-v1":
            raise ValueError("Kernel type DAG format mismatch: " + name)
        nodes, levels, names = dag["nodes"], dag["levels"], dag["names"]

        def index(value: object, bound: int) -> None:
            if type(value) is not int or not 0 <= value < bound:
                raise ValueError("Kernel type DAG reference out of range: " + name)

        def natural(value: object) -> None:
            if type(value) is not int or value < 0:
                raise ValueError("Kernel type DAG natural index invalid: " + name)

        def decimal(value: object) -> None:
            if not isinstance(value, str) or not re.fullmatch(r"0|[1-9][0-9]*", value):
                raise ValueError("Kernel type DAG decimal invalid: " + name)

        index(dag["root"], len(nodes))
        for parts in names:
            if not isinstance(parts, list):
                raise ValueError("Kernel type DAG name is not a part list: " + name)
            for part in parts:
                if len(part) != 2 or part[0] not in {"str", "num"} or not isinstance(part[1], str):
                    raise ValueError("Kernel type DAG name part invalid: " + name)
                if part[0] == "num":
                    decimal(part[1])
        for i, level in enumerate(levels):
            tag = level[0]
            if tag == "zero" and len(level) == 1:
                continue
            if tag == "succ" and len(level) == 2:
                index(level[1], i)
            elif tag in {"max", "imax"} and len(level) == 3:
                index(level[1], i); index(level[2], i)
            elif tag == "param" and len(level) == 2:
                index(level[1], len(names))
            else:
                raise ValueError("Kernel type DAG universe tag invalid: " + name)
        for i, node in enumerate(nodes):
            tag = node[0]
            if tag == "bvar" and len(node) == 2:
                natural(node[1])
            elif tag == "sort" and len(node) == 2:
                index(node[1], len(levels))
            elif tag == "const" and len(node) == 3:
                index(node[1], len(names))
                for level in node[2]:
                    index(level, len(levels))
            elif tag == "app" and len(node) == 3:
                index(node[1], i); index(node[2], i)
            elif tag in {"lam", "forall"} and len(node) == 5:
                index(node[1], len(names)); index(node[2], i); index(node[3], i)
                if node[4] not in {"default", "implicit", "strictImplicit", "instImplicit"}:
                    raise ValueError("Kernel type DAG binder info invalid: " + name)
            elif tag == "let" and len(node) == 6:
                index(node[1], len(names)); index(node[2], i); index(node[3], i); index(node[4], i)
                if type(node[5]) is not bool:
                    raise ValueError("Kernel type DAG let flag invalid: " + name)
            elif tag == "lit_nat" and len(node) == 2:
                decimal(node[1])
            elif tag == "lit_string" and len(node) == 2 and isinstance(node[1], str):
                continue
            elif tag == "proj" and len(node) == 4:
                index(node[1], len(names)); natural(node[2]); index(node[3], i)
            else:
                raise ValueError("Kernel type DAG expression tag invalid: " + name)
        # A shared node can appear under several binder depths. Validate scope
        # using (node, depth) pairs without expanding the shared DAG into a tree.
        pending = [(dag["root"], 0)]
        seen = set()
        while pending:
            node_id, depth = pending.pop()
            if (node_id, depth) in seen:
                continue
            seen.add((node_id, depth))
            node = nodes[node_id]
            tag = node[0]
            if tag == "bvar" and node[1] >= depth:
                raise ValueError("Kernel type DAG has an unbound variable: " + name)
            if tag == "app":
                pending.extend([(node[1], depth), (node[2], depth)])
            elif tag in {"lam", "forall"}:
                pending.extend([(node[2], depth), (node[3], depth + 1)])
            elif tag == "let":
                pending.extend([(node[2], depth), (node[3], depth), (node[4], depth + 1)])
            elif tag == "proj":
                pending.append((node[3], depth))

    def declaration_link(self, name: str, page: str) -> str:
        if name in self.declarations:
            return self.link(self.declaration_urls[name], "<code>" + esc(name) + "</code>", page)
        return '<code>' + esc(name) + '</code>'

    def module_url(self, name: str) -> str:
        return "modules/" + name + ".html"

    def doc_url(self, rel: str) -> str:
        return "docs/" + rel[:-3].replace("/", "--") + ".html"

    def link(self, url: str, label: str, page: str, css: str = "") -> str:
        root = "../" * (len(PurePosixPath(page).parts) - 1)
        return '<a href="' + esc(root + url) + '"' + (f' class="{css}"' if css else "") + '>' + label + '</a>'

    def module_link(self, name: str, page: str) -> str:
        if name in self.modules:
            return self.link(self.module_url(name), "<code>" + esc(name) + "</code>", page)
        return '<code>' + esc(name) + '</code> <span class="muted small">dependency</span>'

    def result_link(self, result_id: str, page: str) -> str:
        result = self.result_by_id[result_id]
        return self.link("results/" + result_id + ".html", esc(result["name"]), page)

    def tag(self, status: str) -> str:
        return f'<span class="tag {status.replace("_", "-")}">{esc(status.replace("_", " "))}</span>'

    def page(self, path: str, title: str, content: str, active: str, wide: bool = False, extra_scripts: tuple[str, ...] = ()) -> None:
        root = "../" * (len(PurePosixPath(path).parts) - 1)
        nav = "".join(f'<a href="{root + url}"' + (' aria-current="page"' if label == active else "") + f'>{label}</a>' for label, url in NAV)
        technical = "".join(f'<a href="{root + url}"' + (' aria-current="page"' if label == active or (label == "Proof map" and active == "Dependencies") else "") + f'>{label}</a>' for label, url in LEAN_NAV)
        has_math = 'class="math-inline"' in content or 'class="math-display"' in content
        math_head = f'<link rel="stylesheet" href="{root}assets/katex/katex.min.css">' if has_math else ""
        math_scripts = f'<script defer src="{root}assets/katex/katex.min.js"></script><script defer src="{root}assets/math.js"></script>' if has_math else ""
        footer = '<p>Reader documentation for exact Lean sources; the source and its declared context determine what is proved.</p>'
        footer += '<p>Lean 4.29.0-rc6 · Mathlib <code>f156f7ab…</code> · Only <code>propext</code>, <code>Classical.choice</code>, and <code>Quot.sound</code> permitted in solution dependencies.</p>'
        footer += '<p class="footer-links">' + self.link("about.html", "About these pages", path) + self.link("generation.json", "Generation record", path) + f'<a href="{REPO}">GitHub repository</a></p>'
        self.emit(path, f'''<!doctype html>
<!-- {COPYRIGHT} See COPYRIGHT.md for attribution. -->
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<meta name="description" content="A reader guide to Lean proofs of Holevo additivity gaps, exact source statements, and reproducible verification.">
<title>{esc(title)} · Holevo Additivity Gap</title><link rel="stylesheet" href="{root}assets/site.css">{math_head}{math_scripts}</head>
<body data-root="{root}"><header class="top"><div class="top-inner">
<a class="brand" href="{root}index.html">Holevo Additivity Gap <span>in Lean 4</span></a>
<nav aria-label="Main navigation">{nav}</nav><h2 class="lean-explorer-heading" id="lean-explorer-heading">Lean explorer</h2><nav class="technical-nav" aria-labelledby="lean-explorer-heading">{technical}</nav>
<div class="search-wrap"><label class="hidden" for="site-search">Search concepts, results and Lean declarations</label><input id="site-search" type="search" placeholder="Search concepts, results, or Lean declarations…" autocomplete="off" spellcheck="false" aria-label="Search concepts, results and Lean declarations"><label class="internal-toggle"><input id="search-internal" type="checkbox"> Include Lean internal, generated-detail or private constants</label><div id="search-results" class="search-results" hidden></div></div>
</div></header><main><article class="{'wide' if wide else 'prose'}">{content}</article></main>
<footer>{footer}</footer><script src="{root}assets/search-data.js"></script><script src="{root}assets/site.js"></script>{''.join('<script src="' + root + script + '"></script>' for script in extra_scripts)}</body></html>
''')

    def card(self, result_id: str, page: str) -> str:
        result = self.result_by_id[result_id]
        explanation = self.reader_item("results", result_id)
        return '<div class="card">' + self.tag(result["status"]) + '<h3>' + self.result_link(result_id, page) + '</h3><p>' + esc(explanation["summary"]) + '</p></div>'

    def reader_item(self, group: str, item_id: str) -> dict:
        return next(item for item in self.reader[group] if item["id"] == item_id)

    def reader_body(self, item: dict, page: str, heading_shift: int = 0) -> str:
        text = re.sub(r"(?m)^#\s+[^\n]+\n", "", self.reader_text[item["source"]], count=1)
        prefix = "stage-" + item["id"] + "-" if item["category"] == "stages" else ""
        return self.render_markdown(item["source"], text, page, heading_shift, prefix)

    def explanation_links(self, name: str, page: str) -> str:
        items = self.reader_by_decl.get(name, [])
        if not items:
            return ""
        order = {"results": 0, "concepts": 1, "guides": 2, "stages": 3}
        items = sorted(items, key=lambda item: (order[item["category"]], item["title"]))
        return '<div class="explanation-links"><span>Read the mathematics:</span> ' + ' · '.join(self.link(item["page"], esc(item["title"]), page) for item in items) + '</div>'

    @staticmethod
    def math(tex: str, display: bool = False) -> str:
        tag = "div" if display else "span"
        return f'<{tag} class="math-{("display" if display else "inline")}">' + esc(tex) + f'</{tag}>'

    def build_reader(self) -> None:
        for group in ("guides", "concepts"):
            for item in self.reader[group]:
                page = item["page"]
                body = self.reader_body(item, page)
                headings = re.findall(r'<h([23]) id="([^"]+)">(.*?)</h\1>', body, re.S)
                toc = '<aside class="reader-toc"><p>On this page</p><ol>' + ''.join('<li class="toc-level-' + level + '"><a href="#' + anchor + '">' + re.sub(r'<[^>]+>', '', label) + '</a></li>' for level, anchor, label in headings) + '</ol><p>' + self.link("guide/index.html", "Reading guide", page) + '</p><p>' + self.link("concepts/index.html", "All concepts", page) + '</p></aside>'
                content = '<div class="breadcrumb">' + self.link("guide/index.html" if group == "guides" else "concepts/index.html", "Reading guide" if group == "guides" else "Concepts", page) + '</div><p class="eyebrow">' + ("Mathematical guide" if group == "guides" else esc(item["topic"])) + '</p><h1>' + esc(item["title"]) + '</h1><p class="lead">' + esc(item["summary"]) + '</p><div class="reader-layout"><div class="reader-body">' + body + '<p class="reader-source">' + self.link("source/" + item["source"], "Exact explanation source", page) + ' · ' + self.link("reader-map.json", "Explanation-to-Lean map", page) + '</p></div>' + toc + '</div>'
                self.page(page, item["title"], content, "Start here" if group == "guides" else "Concepts", True)
                self.search.append({"title": item["title"], "detail": ("Concept" if group == "concepts" else "Mathematical guide") + " · " + item["summary"], "url": page, "search": (item["title"] + " " + item["summary"] + " " + self.reader_text[item["source"]]).lower(), "reader": True})
        page = "guide/index.html"
        content = '<p class="eyebrow">Read the mathematics</p><h1>A guide to the results and proofs.</h1><p class="lead">Start with the communication problem, then follow the channel construction and its consequences. Every chapter connects the explanation to exact Lean objects.</p><ol class="reading-path">'
        for item in self.reader["guides"]:
            content += '<li><h2>' + self.link(item["page"], esc(item["title"]), page) + '</h2><p>' + esc(item["summary"]) + '</p></li>'
        content += '</ol>'
        self.page(page, "Reading guide", content, "Start here")
        page = "concepts/index.html"
        content = '<p class="eyebrow">Definitions, intuition, and formal objects</p><h1>The concepts behind the proof.</h1><p class="lead">Each entry explains the idea, its role in this project, and the corresponding Lean definitions or lemmas.</p>'
        for topic in dict.fromkeys(item["topic"] for item in self.reader["concepts"]):
            content += '<h2>' + esc(topic) + '</h2><div class="cards">'
            for item in self.reader["concepts"]:
                if item["topic"] == topic:
                    content += '<div class="card"><h3>' + self.link(item["page"], esc(item["title"]), page) + '</h3><p>' + esc(item["summary"]) + '</p></div>'
            content += '</div>'
        self.page(page, "Concepts", content, "Concepts", True)
        pages = [{"category": item["category"], "title": item["title"], "page": item["page"], "source": item["source"], "source_sha256": self.inputs[item["source"]], "declarations": [{"name": name, "kind": self.declarations[name]["kind"], "module": self.declarations[name]["module"], "url": self.declaration_urls[name]} for name in item["declarations"]]} for group in ("guides", "concepts", "results", "stages") for item in self.reader[group]]
        self.emit("reader-map.json", pretty({"schema_version": 1, "copyright": COPYRIGHT, "purpose": "Reading correspondence, not an informal-to-formal equivalence certificate", "declaration_export_sha256": self.inputs["metadata/declarations.json"], "pages": pages}))

    def build_overview(self) -> None:
        page = "index.html"
        content = '<div class="hero"><div><p class="eyebrow">Quantum communication · mathematics and Lean proofs</p><h1>Two uses can reveal much more than one.</h1><p class="lead">Finite quantum channels can have arbitrarily small single-use Holevo information and arbitrarily large information per use when inputs are entangled across uses.</p><p>This guide explains Jinzhao Wang’s Holevo additivity-gap construction, its scaling, and its operational meaning. Each explanation leads to the corresponding formal statements.</p><div class="actions">'
        content += self.link("guide/introduction.html", "Start with the mathematics", page, "button primary") + self.link("guide/construction.html", "How the construction works", page, "button") + '<a class="button" href="https://arxiv.org/abs/2609.18222">Read the paper</a></div></div><aside class="hero-note reader-key"><h2>Three quantities to keep apart</h2>'
        for expression, text in [(r"\chi(T)", "Single-use Holevo information: optimize over ensembles sent through one channel."), (r"\tfrac12\chi(T\otimes T)", "Two-use information per use: allow entangled inputs to a pair of uses."), (r"C(T)", "Operational capacity: the rate of physical codes with vanishing decoding error.")]:
            content += '<p><strong>' + self.math(expression) + '</strong><span>' + esc(text) + '</span></p>'
        content += self.link("guide/capacity.html", "How these quantities are related →", page) + '</aside></div>'
        content += '<section class="reader-highlight"><h2>The central separation</h2><p>For every positive tolerance and every target gain and ratio, one finite channel can satisfy all three conditions:</p>' + self.math(r"0<\chi(T)\le\varepsilon,\qquad C(T)-\chi(T)\ge A,\qquad \frac{\chi(T\otimes T)}{2\chi(T)}\ge R.", True)
        content += '<p>The channel may depend on the targets. Its input and output spaces are finite, and their dimensions grow along the constructed families. ' + self.result_link("simultaneous-separation", page) + ' explains the quantifiers and proof.</p></section>'
        content += '<h2>Follow the argument</h2><div class="cards">'
        for title, url, text in [("1. Understand the problem", "guide/introduction.html", "What additivity would predict, what entangled inputs change, and what the results establish."), ("2. Build the channel", "guide/construction.html", "Uniformly high single-use entropy, a low-entropy Bell witness, and the switch/Weyl conversion."), ("3. Read the scaling", "guide/scaling.html", "Fixed-K gaps, vanishing one-use information, and the actual input/output size costs.")]:
            content += '<div class="card"><h3>' + self.link(url, title, page) + '</h3><p>' + esc(text) + '</p></div>'
        content += '</div><h2>Explore the results</h2><div class="cards">'
        for result_id in ["prescribed-dimensions", "operational-coding", "growing-family-cost", "free-collins-youn", "weyl-all-uses", "fixed-channel-regrouping"]:
            content += self.card(result_id, page)
        content += '</div><h2>Connect intuition to the formal proof</h2><p>Use the ' + self.link("concepts/index.html", "concept guide", page) + ' for definitions and intuition, the ' + self.link("route.html", "proof route", page) + ' for the reasoning, and the ' + self.link("dependencies.html", "interactive map", page) + ' for actual Lean reference paths. ' + self.link("guide/reading-lean.html", "Reading a formal statement", page) + ' explains how to inspect hypotheses, units, and definitions.</p><div class="note"><strong>Formalization status.</strong> The principal endpoints passed the Lean build and axiom audit. The full manuscript is not formalized; Comparator and an independent kernel remain pending. ' + self.link("verify.html", "Reproducer commands and evidence →", page) + '</div>'
        self.page(page, "Overview", content, "Overview", True)

    def build_verify(self) -> None:
        page = "verify.html"
        content = '<p class="eyebrow">Reproducible verification</p><h1>Check the formal proofs.</h1><p class="lead">Reproduce the Lean build and audit. For independent Comparator checking, use a separate fresh checkout so the proof sources are compiled under the prescribed sandbox.</p>'
        content += '<h2>1. Get the repository</h2><p>On Linux or macOS, install <a href="https://github.com/leanprover/elan">elan</a>, Git, Python 3.11 or later, and Python’s <code>venv</code>/<code>pip</code> support. Ensure <code>elan</code> is on your <code>PATH</code>. The repository pins Lean <code>4.29.0-rc6</code> and its Mathlib revision. Dependency downloads require network access.</p>'
        content += command('git clone https://github.com/JWang226/Holevo-Additivity-Gap.git\ncd Holevo-Additivity-Gap')
        content += '<h2>2. Run the Lean verifier</h2><p>The wrapper rebuilds the project sources, performs the complete transitive-axiom audit, validates metadata and every catalog declaration, and checks all six challenge types locally.</p>'
        content += command('./verification/lean/run.sh')
        content += '<p>For usage and a prerequisite check:</p>' + command('./verification/lean/run.sh --help\n./verification/lean/run.sh --check-prerequisites')
        content += '<p>Success prints <code>LEAN REPRODUCTION PASSED. Comparator was not run.</code> and returns exit code zero. The log directory is <code>.verify-work/logs/lean-&lt;UTC timestamp&gt;-&lt;process ID&gt;/</code>, with a <code>status.txt</code> record and per-step logs. Prerequisite checks download and build nothing; their success does not certify a proof.</p>'
        content += '<p>' + self.link(self.doc_url("verification/README.md"), "Detailed Lean procedure, logs, and trust boundary →", page) + ' · ' + self.link("source/verification/lean/run.sh", "Read the exact wrapper", page) + '</p>'
        content += '<h2>3. Run Comparator separately</h2><div class="note warning"><strong>Execution status:</strong> the Comparator configurations and local statement checks are prepared and checked. End-to-end Comparator verification remains pending.</div>'
        content += '<p>Use Linux with a nonprivileged account, Git, elan, Python 3.11 or later, a working systemd user session, and a real <a href="https://github.com/Zouuup/landrun">landrun</a> installation. Comparator is pinned at <code>a4f696825c583ed8a5b4060d9a0faa5b882d365b</code>; the script preserves its committed manifest.</p><p>From the repository root used above, clone a fresh sibling checkout. Review the expected statements and their trusted imports before running the sandboxed verifier, and avoid compiling project proof sources outside that sandbox in this fresh checkout.</p>'
        content += command('git clone https://github.com/JWang226/Holevo-Additivity-Gap.git ../Holevo-Additivity-Gap-comparator\ncd ../Holevo-Additivity-Gap-comparator\n./verification/comparator/run.sh --check-prerequisites\n./verification/comparator/run.sh')
        content += '<p>The script builds the pinned Comparator and exporter, obtains trusted dependency cache material, and runs all five configurations for six expected statements. Each successful configuration must print <code>Your solution is okay!</code>; completion prints <code>COMPARATOR REPRODUCTION PASSED: five configurations. Nanoda was not run.</code> and returns exit code zero. Logs are retained in <code>.verify-work/logs/comparator-&lt;UTC timestamp&gt;-&lt;process ID&gt;/</code>. These configurations use Lean kernel replay; additional independent Nanoda checking is disabled.</p>'
        content += '<p>' + self.link(self.doc_url("ComparatorChallenges/README.md"), "Comparator prerequisites, configurations, and trust assumptions →", page) + ' · ' + self.link("source/verification/comparator/run.sh", "Read the exact wrapper", page) + '</p>'
        content += '<h2 id="evidence">Recorded evidence</h2><p>The successful full project-source rebuild is a retained historical result for commit <code>' + esc(self.ci["commit"]) + '</code>, run attempt ' + str(self.ci["run_attempt"]) + '. It used the pinned prebuilt Mathlib cache; Mathlib was not rebuilt from source.</p>'
        content += '<table><thead><tr><th>Check</th><th>Recorded result</th></tr></thead><tbody>'
        for label, value in [("Project-source rebuild", f'{self.ci["project_modules_rebuilt"]} project modules rebuilt'), ("Transitive axiom audit", f'{self.ci["audited_project_declarations"]:,} declarations; only the standard three axioms'), ("Theorem constants", f'{self.ci["audited_theorem_constants"]:,} including generated helpers'), ("Catalog references", f'{self.ci["mapped_declarations_checked_in_lean"]} declarations checked in Lean'), ("Local challenge type checks", f'{self.ci["expected_types_checked_against_solution_proofs"]} expected statements fit solution proofs'), ("Comparator engine", "Not run"), ("Independent kernel", "Not run")]:
            content += '<tr><td>' + esc(label) + '</td><td>' + esc(value) + '</td></tr>'
        content += '</tbody></table><p><a href="' + esc(self.ci["url"]) + '">Successful GitHub Actions run</a> · ' + self.link("source/" + self.ci_record, "Machine-readable record", page) + ' · ' + self.link("source/" + self.ci_excerpt, "Retained log excerpt", page) + '</p>'
        content += '<h2>What these checks certify</h2><p>The audit permits only <code>propext</code>, <code>Classical.choice</code>, and <code>Quot.sound</code> across all project declarations, including definitions with proof fields and private helpers. The six intentional expected-statement placeholders in isolated Comparator challenge files are excluded from the solution build.</p><p>Kernel acceptance concerns exactly the formal statements in their Lean context. Mathematical review must still assess their correspondence to the manuscript. The revised manuscript incorporates both repaired intermediate counting arguments, with correspondence recorded at the stated endpoint scope.</p>'
        content += '<p>' + self.link(self.doc_url("docs/FORMALIZATION_STATUS.md"), "Formalization status", page) + ' · ' + self.link(self.doc_url("docs/CORRECTIONS.md"), "Manuscript corrections", page) + '</p>'
        self.page(page, "Verify", content, "Verify")

    def build_route(self) -> None:
        page = "route.html"
        content = '<p class="eyebrow">Why the construction works</p><h1>The proof, step by step.</h1><p class="lead">Make every single-use output highly mixed, find an entangled input with a less mixed two-use output, and turn this entropy difference into a communication advantage.</p><p>Read the ' + self.link("guide/construction.html", "construction chapter", page) + ' for the formulas and the ' + self.link("dependencies.html", "interactive proof map", page) + ' for the implemented Lean paths.</p>'
        for n, (title, text, results, modules) in enumerate(STAGES, 1):
            content += f'<section class="route-stage" id="stage-{n}"><h2><span class="stage-number">{n}</span>{esc(title)}</h2>' + self.reader_body(self.reader_item("stages", str(n)), page, 1) + '<p class="small"><strong>Results at this step</strong></p><ul>'
            content += ''.join('<li>' + self.result_link(result_id, page) + '</li>' for result_id in results)
            content += '</ul><p class="small muted">Read these source modules:</p><div class="inline-links">'
            for module in modules:
                full = "Nonadditivity." + module
                if full not in self.modules:
                    raise ValueError("Unknown route module " + full)
                content += self.module_link(full, page)
            content += '</div></section>'
        content += '<p>' + self.link(self.doc_url("docs/PROOF_MAP.md"), "Complete repository proof map →", page) + '</p>'
        self.page(page, "Proof route", content, "Proof route")

    def build_results(self) -> None:
        page = "results.html"
        content = '<p class="eyebrow">Statements, significance, and proof ideas</p><h1>The results explained.</h1><p class="lead">Read each result as mathematics, then open its corresponding Lean statement. The main channel theorem, coding theorem, scaling laws, and intermediate estimates are explained here.</p><p>Entries also identify corrected arguments and broader claims whose formalization remains open.</p>'
        content += '<input class="filter" aria-label="Filter result catalog" placeholder="Filter by result, paper label, or declaration…" data-filter=".catalog-item" data-status="catalog-status"><p class="small muted" id="catalog-status">25 correspondence records</p>'
        for result in self.results:
            terms = result["name"] + " " + " ".join(result["paper"]["labels"]) + " " + " ".join(x["declaration"] for x in result["lean"])
            content += '<section class="catalog-item" data-search="' + esc(terms) + '"><div class="catalog-top">' + self.tag(result["status"]) + '<span class="small muted">' + esc(result["correspondence"].replace("_", " ")) + '</span></div><h2>' + self.result_link(result["id"], page) + '</h2>'
            content += '<div class="label-list">' + ''.join('<code>' + esc(x) + '</code>' for x in result["paper"]["labels"]) + '</div><p>' + esc(self.reader_item("results", result["id"])["summary"]) + '</p></section>'
            self.build_result(result)
        self.page(page, "Results", content, "Results")

    def build_result(self, result: dict) -> None:
        page = "results/" + result["id"] + ".html"
        content = '<div class="breadcrumb">' + self.link("results.html", "Result catalog", page) + ' / ' + esc(result["id"]) + '</div>'
        content += '<p class="eyebrow">' + esc(result["correspondence"].replace("_", " ")) + '</p><h1>' + esc(result["name"]) + '</h1>' + self.tag(result["status"])
        explanation = self.reader_item("results", result["id"])
        content += '<p class="lead">' + esc(explanation["summary"]) + '</p><div class="reader-body">' + self.reader_body(explanation, page) + '</div><h2>Formal scope and manuscript correspondence</h2>'
        if result["notes"]:
            content += '<p>' + esc(result["notes"]) + '</p>'
        if result["status"] == "not_formalized":
            content += '<div class="note warning">No proof of the broader claim is asserted. Any listed predicates are definitions or conditional interfaces, not proofs that those predicates hold.</div>'
        content += '<div class="label-list">' + ''.join('<code>' + esc(x) + '</code>' for x in result["paper"]["labels"]) + '</div>'
        if result["paper"].get("locator"):
            content += '<p>' + esc(result["paper"]["locator"]) + '</p>'
        content += '<p class="small muted">The included manuscript is the revised source incorporating the two counting repairs. Correspondence entries are reading aids rather than an exhaustive statement-equivalence certificate.</p><p>' + self.link("source/paper/nonadditivity.tex", "Revised manuscript source", page) + ' · ' + self.link("source/metadata/results.json", "Correspondence metadata", page) + '</p>'
        if result.get("comparator_config"):
            content += '<p class="small">Comparator configuration: ' + self.link("source/" + result["comparator_config"], '<code>' + esc(result["comparator_config"]) + '</code>', page) + '. End-to-end Comparator execution is pending.</p>'
        if result["lean"]:
            content += '<h2 id="lean-correspondence">Corresponding Lean statements</h2><p>Open a declaration for its complete checked type, definitions, source, and references.</p>'
        for n, ref in enumerate(result["lean"], 1):
            name = ref["declaration"]
            module_name = ref["file"][:-5].replace("/", ".")
            header, line = self.headers[name]
            anchor = f'declaration-{n}'
            source_url = self.module_url(module_name) + (f'#L{line}' if line else "")
            content += '<section class="declaration" id="' + anchor + '"><p class="eyebrow">' + esc(ref["role"].replace("_", " ")) + '</p><h2>' + esc(name) + '</h2>'
            content += '<p>' + self.declaration_link(name, page) + ' — full elaborated type and exact constant references.</p>'
            content += '<details class="lean-details"><summary>Literal source statement and context</summary>'
            if header:
                content += command(header, "Copy statement")
                content += '<p class="source-context">Literal source header; namespace variables, local instances, imports, and notation are not expanded. Open the full module to read the surrounding context.</p>'
            else:
                content += '<p>A standalone header cannot be safely extracted by this documentation generator. Read the exact full module instead.</p>'
            content += '</details><p>' + self.link(source_url, "Exact source" + (f' at line {line}' if line else ""), page) + ' · <a href="' + REPO + '/blob/main/' + ref["file"] + (f'#L{line}' if line else "") + '">View on GitHub</a></p></section>'
        if not result["lean"]:
            content += '<p>No formal declaration is attached to this broader correspondence entry.</p>'
        content += '<p>' + self.link("verify.html", "Verification and trust limits", page) + ' · ' + self.link(self.doc_url("docs/FORMALIZATION_STATUS.md"), "Full scope statement", page) + '</p>'
        self.search.append({"title": result["name"], "detail": result["status"].replace("_", " ") + " · " + explanation["summary"], "url": page, "search": (result["name"] + " " + result["id"] + " " + " ".join(result["paper"]["labels"]) + " " + self.reader_text[explanation["source"]]).lower(), "reader": True})
        self.page(page, result["name"], content, "Results")

    def build_modules(self) -> None:
        page = "modules.html"
        content = '<p class="eyebrow">Full source browser</p><h1>Proof modules and entry points.</h1><p class="lead">All 366 proof modules and three aggregate entry points, with exact full source and direct import relationships.</p><p>The proof namespace is <code>Nonadditivity</code>. Entry points <code>Nonadditivity.lean</code>, <code>Audit.lean</code>, and <code>All.lean</code> are also indexed. Isolated expected-statement challenges and generated local checker modules are excluded from this source catalog.</p>'
        content += '<input class="filter" aria-label="Filter module names" placeholder="Filter module names…" data-filter=".module-entry" data-status="module-status"><p id="module-status" class="small muted">369 modules: 366 proof files + 3 aggregate entry points</p><ul class="module-list">'
        for name, module in self.modules.items():
            content += '<li class="module-entry" data-search="' + esc(name) + '">' + self.module_link(name, page) + '</li>'
            self.build_module(name, module)
        content += '</ul>'
        self.page(page, "Modules", content, "Modules", True)

    def build_module(self, name: str, module: dict) -> None:
        page = self.module_url(name)
        content = '<div class="breadcrumb">' + self.link("modules.html", "Proof modules", page) + ' / ' + esc(name.rsplit(".", 1)[-1]) + '</div><p class="eyebrow">Exact Lean source</p><h1 class="title-code">' + esc(name) + '</h1>'
        content += '<p>' + self.link("source/" + module["path"], "Download original .lean", page) + ' · <a href="' + REPO + '/blob/main/' + module["path"] + '">View on GitHub</a> · <a href="#source">Jump to source</a></p>'
        related = {x["id"]: x for x in self.module_results[name]}
        if related:
            content += '<p class="small">Catalog entries: ' + ' · '.join(self.result_link(rid, page) for rid in related) + '</p>'
        content += '<div class="columns"><div><h2>Direct imports</h2><ul class="module-list">'
        for imp in module["imports"]:
            content += '<li>' + self.module_link(imp, page) + '</li>'
        content += '</ul>' + ('<p class="small muted">No direct imports.</p>' if not module["imports"] else "") + '</div><div><h2>Imported by project modules</h2>'
        users = sorted(self.used_by[name])
        if users:
            content += '<details' + (' open' if len(users) < 7 else "") + '><summary>' + str(len(users)) + ' direct reverse imports</summary><ul class="module-list">' + ''.join('<li>' + self.module_link(user, page) + '</li>' for user in users) + '</ul></details>'
        else:
            content += '<p class="small muted">No direct reverse imports in this project-module catalog.</p>'
        content += '</div></div><p class="small muted">Relationships above come from literal import commands. The declarations below link to types and references extracted from Lean’s environment. Source text is complete and unchanged.</p>'
        names = self.module_declarations[name]
        content += '<h2 id="declarations">Declarations in this module</h2><p class="small muted">' + str(len(names)) + ' project constants, including generated, internal and private declarations.</p>'
        if names:
            content += '<input class="filter" aria-label="Filter this module’s declarations" placeholder="Filter declaration names…" data-filter=".module-declaration" data-status="module-declaration-status"><p class="small muted" id="module-declaration-status">' + str(len(names)) + ' declarations</p><ul class="module-list">'
            for declaration in names:
                record = self.declarations[declaration]
                marked = ' <span class="muted small">internal/detail/private</span>' if hidden_declaration(record) else ''
                content += '<li class="module-declaration" data-search="' + esc(declaration) + '">' + self.declaration_link(declaration, page) + marked + '</li>'
            content += '</ul>'
        else:
            content += '<p>This aggregate module introduces no project constant in the export.</p>'
        content += '<h2 id="source">Full module</h2><pre class="source">'
        for n, line in enumerate(module["source"].splitlines(), 1):
            content += f'<span class="code-line" id="L{n}"><a class="line-number" href="#L{n}" aria-label="Line {n}">{n}</a><code>{esc(line)}</code></span>'
        content += '</pre>'
        self.search.append({"title": name, "detail": ("Aggregate entry point" if "/" not in module["path"] else "Proof module") + " · exact source and direct imports", "url": page, "search": name.lower()})
        self.page(page, name, content, "Modules", True)

    def build_imports(self) -> None:
        page = "imports.html"
        edge_count = sum(sum(imp in self.modules for imp in module["imports"]) for module in self.modules.values())
        content = '<p class="eyebrow">Literal module relationships</p><h1>Import catalog.</h1><p class="lead">' + str(edge_count) + ' direct project-to-project import edges across 366 proof modules and three aggregate entry points.</p><p>Open any row to inspect the modules it imports. These are literal <code>import</code> commands read from source. They are module-level relationships; they do not assert that every declaration in a module depends on every imported theorem.</p>'
        content += '<input class="filter" aria-label="Filter imports" placeholder="Filter by module or imported name…" data-filter=".import-row" data-status="import-status"><p class="small muted" id="import-status">369 project modules</p>'
        graph = {}
        for name, module in self.modules.items():
            graph[name] = module["imports"]
            content += '<details class="import-row" data-search="' + esc(name + " " + " ".join(module["imports"])) + '"><summary>' + esc(name) + '<span class="muted">' + str(len(module["imports"])) + ' imports · ' + str(len(self.used_by[name])) + ' reverse project imports</span></summary><p>' + self.module_link(name, page) + '</p><ul>' + ''.join('<li>' + self.module_link(imp, page) + '</li>' for imp in module["imports"]) + '</ul></details>'
        content += '<p>' + self.link("imports.json", "Download exact import adjacency data", page) + '</p>'
        self.emit("imports.json", pretty(graph))
        self.page(page, "Imports", content, "Imports", True)

    def reference_list(self, names: list[str], page: str, label: str) -> str:
        if not names:
            return '<p class="small muted">No ' + esc(label) + ' in the exported expression.</p>'
        content = '<ul class="reference-list">' + ''.join('<li>' + self.declaration_link(name, page) + (' <span class="muted small">external</span>' if name not in self.declarations else '') + '</li>' for name in names) + '</ul>'
        if len(names) > 12:
            return '<details><summary>' + str(len(names)) + ' ' + esc(label) + '</summary>' + content + '</details>'
        return content

    def build_declarations(self) -> None:
        page = "declarations.html"
        count = len(self.declarations)
        hidden = sum(hidden_declaration(x) for x in self.declarations.values())
        kinds: dict[str, int] = defaultdict(int)
        for record in self.declarations.values():
            kinds[record["kind"]] += 1
        content = '<p class="eyebrow">Extracted from the Lean environment</p><h1>Every project declaration.</h1><p class="lead">' + f'{count:,}' + ' constants, with full elaborated types, exact direct references, and reverse reference links.</p>'
        content += '<p>The export contains theorem and definition constants, structures, constructors, recursors, and generated helpers from the project modules imported by <code>All</code>. Every item has its own page. ' + f'{hidden:,}' + ' constants are flagged by Lean’s <code>Name.isInternal</code>, <code>Name.isInternalDetail</code> or <code>isPrivateName</code> predicates; that flag is not a mathematical judgment and does not identify every generated helper.</p>'
        content += '<p class="small muted">The exported inventory uses the same audited namespace selection as <code>Audit.lean</code>: names beginning <code>Nonadditivity.</code> or <code>_private.Nonadditivity.</code>.</p>'
        content += '<div class="catalog-controls"><label>Search names, kinds or modules <input id="declaration-search" class="filter" type="search" placeholder="For example: channel, HaarPrescribedBound, constructor…" autocomplete="off"></label><label class="internal-toggle"><input id="declaration-internal" type="checkbox"> Include Lean internal, generated-detail or private constants</label><label>Kind <select id="declaration-kind"><option value="">All kinds</option>' + ''.join('<option value="' + esc(kind) + '">' + esc(kind) + ' (' + str(n) + ')</option>' for kind, n in sorted(kinds.items())) + '</select></label></div><p id="declaration-status" class="small muted" aria-live="polite"></p><div id="declaration-catalog"></div><button type="button" id="declaration-more" class="button">Show 100 more</button>'
        content += '<noscript><p>Interactive filtering requires JavaScript. All declaration links remain available on the ' + self.link("modules.html", "module pages", page) + '.</p></noscript><h2>What the export records</h2><p>The readable type is Lean’s pretty-printed elaborated expression with full names and universe levels requested. The compressed kernel expression DAG preserves all kernel-relevant fields, including arguments hidden by readable printing. Universe parameters are listed separately. It includes the implicit context that a literal source header can leave outside the declaration. Pretty printing is a display of the checked expression; proof verification still uses the committed Lean sources.</p><p>References are the constant names occurring directly in a declaration’s type and its stored proof or definition expression, including the structure names carried by projection expressions. They are not a minimal dependency certificate or informal citations. Reverse links are derived from the union of those two lists. Imported library constants appear as plain names where no precise external documentation link is available.</p><p>'
        content += self.link("source/metadata/declarations.json", "Download the exact Lean declaration export", page) + ' · ' + self.link("dependencies.html", "Explore the real constant-reference graph", page) + ' · ' + self.link("about.html", "Export provenance and trust", page) + '</p>'
        self.page(page, "Declarations", content, "Declarations", True)
        for name, record in sorted(self.declarations.items()):
            self.build_declaration(name, record)

    def build_declaration(self, name: str, record: dict) -> None:
        page = self.declaration_urls[name]
        private = bool(record["is_private"])
        internal = bool(record["is_internal"])
        detail = bool(record.get("is_internal_detail", False))
        content = '<div class="breadcrumb">' + self.link("declarations.html", "All declarations", page) + ' / ' + self.module_link(record["module"], page) + '</div><p class="eyebrow">' + esc(record["kind"]) + '</p><h1 class="title-code">' + esc(name) + '</h1>'
        content += self.explanation_links(name, page)
        if private or internal or detail:
            predicates = []
            if internal:
                predicates.append('<code>Name.isInternal</code>')
            if detail:
                predicates.append('<code>Name.isInternalDetail</code>')
            if private:
                predicates.append('<code>isPrivateName</code>')
            content += '<div class="note">Flagged by Lean’s ' + ', '.join(predicates) + ' predicate' + ('s' if len(predicates) > 1 else '') + '. Generated declarations without these flags remain visible in the default catalog.</div>'
        content += '<p>Defined in ' + self.module_link(record["module"], page) + '. '
        source = record.get("source_range")
        line = source.get("start_line") if isinstance(source, dict) else None
        source_url = self.module_url(record["module"]) + (f'#L{line}' if isinstance(line, int) and line > 0 else '')
        content += self.link(source_url, 'Read exact source' + (f' at line {line}' if isinstance(line, int) and line > 0 else ' module'), page) + ' · ' + self.link("source/" + record["file"], "Download .lean", page) + '</p>'
        mapped = {x["id"]: x for x in self.declaration_results[name]}
        if mapped:
            content += '<p>Manuscript correspondence: ' + ' · '.join(self.result_link(rid, page) for rid in mapped) + '.</p>'
        content += '<h2>Readable Lean statement</h2><p class="small muted">Lean’s readable pretty-print of the stored type can hide implicit or proof arguments. The complete kernel JSON expression is available below; universe parameters are listed separately.</p>'
        levels = record["level_parameters"]
        content += '<p class="small">Universe parameters: ' + (', '.join('<code>' + esc(level) + '</code>' for level in levels) if levels else 'none') + '.</p>'
        if record.get("type_readable"):
            content += command(record["type_readable"], "Copy statement")
            if record.get("type_encoding") == "gzip+base64":
                dag = record.get("type_representation") == "lean-kernel-expr-dag-v1"
                suffix = ".expr.json" if dag else ".txt"
                type_file = "types/" + PurePosixPath(page).stem + suffix + ".gz"
                packed = base64.b64decode(record["type"], validate=True)
                self.emit(type_file, packed)
                explanation = 'Canonical JSON encodes the complete kernel type as a shared expression DAG, including every argument, universe, binder and name component. Kernel-irrelevant metadata annotations are omitted. This is a machine expression artifact, distinct from Lean source text.' if dag else 'The same stored expression with full names, explicit arguments and universe levels requested.'
                content += '<details class="full-type" data-size="' + str(record["type_uncompressed_bytes"]) + '" data-sha256="' + esc(record["type_sha256"]) + '" data-filename="' + PurePosixPath(page).stem + suffix + '" data-suffix="' + suffix + '"><summary>' + ('Complete kernel type expression (JSON)' if dag else 'Fully explicit type and exact download') + '</summary><p class="small muted">' + explanation + ' The inline preview is limited to 64,000 characters.</p><p class="small">Uncompressed UTF-8 bytes: <strong>' + f'{record["type_uncompressed_bytes"]:,}' + '</strong><br>SHA-256: <code>' + esc(record["type_sha256"]) + '</code></p><p>' + self.link(type_file, "Download the complete artifact (" + suffix + ".gz)", page) + ' <span class="full-type-download"></span></p><p class="small muted full-type-status" aria-live="polite">Expand to decode a bounded preview locally. The complete compressed download also works without JavaScript.</p><pre class="full-type-preview" hidden><code></code></pre><script type="application/json" class="full-type-payload">' + json.dumps(record["type"]) + '</script></details>'
            else:
                content += '<details><summary>Fully explicit type display</summary><p class="small muted">The same stored expression with full names, explicit arguments and universe levels requested.</p>' + command(record["type"], "Copy statement") + '</details>'
        else:
            if record.get("type_encoding") == "gzip+base64":
                raise ValueError("Compressed type has no readable display: " + name)
            content += command(record["type"], "Copy statement")
        content += '<h2>Direct references in the type</h2>' + self.reference_list(record["type_dependencies"], page, 'type references')
        content += '<h2>Direct references in the proof or definition</h2><p class="small muted">For declaration kinds without a stored value expression, this list is empty. Recursor rules, constructor fields and other kernel metadata are not silently reinterpreted as proof expressions.</p>' + self.reference_list(record["value_dependencies"], page, 'value references')
        users = sorted(self.declaration_users[name])
        content += '<h2>Used by project declarations</h2><p class="small muted">Direct references in types or stored values across the entire exported project environment, including internal and private constants.</p>' + self.reference_list(users, page, 'project declarations referring to this constant')
        content += '<p>' + self.link("dependencies.html#" + self.declaration_urls[name].split('/')[-1][:-5], "Explore these constant dependencies", page) + ' · ' + self.link("verify.html", "Reproduce proof checks", page) + ' · ' + self.link("source/metadata/declarations.json", "Metadata and export provenance", page) + '</p>'
        search = name + ' ' + record["kind"] + ' ' + record["module"]
        if mapped:
            search += ' ' + ' '.join(x["name"] + ' ' + ' '.join(x["paper"]["labels"]) for x in mapped.values())
        self.search.append({"title": name, "detail": record["kind"] + ' · ' + record["module"], "url": page, "search": search.lower(), "kind": record["kind"], "declaration": True, "internal": hidden_declaration(record)})
        self.page(page, name, content, "Declarations", True)

    def build_dependencies(self) -> None:
        page = "dependencies.html"
        nodes = []
        names = sorted(self.declarations)
        indices = {name: n for n, name in enumerate(names)}
        guide = json.loads(self.read("tools/docs-site/proof-graph.json"))
        if guide.get("schema_version") != 1:
            raise ValueError("Unsupported proof-map description schema")
        guide_nodes = {item["id"]: item for item in guide["nodes"]}
        if len(guide_nodes) != len(guide["nodes"]):
            raise ValueError("Duplicate proof-map node ID")
        descriptions = {item["declaration"]: item for item in guide["nodes"]}
        if len(descriptions) != len(guide["nodes"]):
            raise ValueError("Duplicate proof-map declaration")
        for item in guide["nodes"]:
            if item["declaration"] not in indices:
                raise ValueError("Unknown proof-map declaration: " + item["declaration"])
            if not all(isinstance(item.get(key), str) and item[key].strip() for key in ("id", "label", "map_note", "description", "stage")):
                raise ValueError("Incomplete proof-map description: " + item["id"])
            if len(item["map_note"]) > 45:
                raise ValueError("Proof-map takeaway is too long: " + item["id"])
            item["index"] = indices[item["declaration"]]
        if len({preset["id"] for preset in guide["presets"]}) != len(guide["presets"]):
            raise ValueError("Duplicate proof-map preset ID")
        for name in names:
            record = self.declarations[name]
            item = descriptions.get(name)
            short = name.rsplit(".", 1)[-1]
            readable = re.sub(r"(?<=[a-z])(?=[A-Z])", " ", short).replace("_", " ")
            statement = record.get("type_readable", "")
            nodes.append({"name": name, "url": self.declaration_urls[name], "kind": record["kind"], "module": record["module"], "module_url": self.module_url(record["module"]), "source_url": self.module_url(record["module"]), "type": [indices[n] for n in record["type_dependencies"] if n in indices], "value": [indices[n] for n in record["value_dependencies"] if n in indices], "internal": hidden_declaration(record), "curated": bool(item), "label": item["label"] if item else readable, "description": item["description"] if item else "", "statement": statement[:1200], "statement_truncated": len(statement) > 1200})
            if name in self.reader_by_decl:
                order = {"results": 0, "concepts": 1, "guides": 2, "stages": 3}
                nodes[-1]["reader_url"] = min(self.reader_by_decl[name], key=lambda item: order[item["category"]])["page"]
        presets = []
        for preset in guide["presets"]:
            selected = set(preset["nodes"])
            if not re.fullmatch(r"[a-z0-9-]+", preset["id"]) or len(selected) != len(preset["nodes"]) or preset["root"] not in selected or not selected <= guide_nodes.keys():
                raise ValueError("Invalid proof-map preset: " + preset["id"])
            selected_names = {guide_nodes[key]["declaration"]: key for key in selected}
            edges = []
            # Stop at another selected theorem. Each visible arrow therefore
            # has a real proof/definition-reference path through omitted helpers.
            for consumer_id in preset["nodes"]:
                consumer = guide_nodes[consumer_id]["declaration"]
                parents: dict[str, str | None] = {consumer: None}
                queue = deque([consumer])
                while queue:
                    current = queue.popleft()
                    for reference in sorted(self.declarations[current]["value_dependencies"]):
                        if reference not in indices or reference in parents:
                            continue
                        parents[reference] = current
                        if reference in selected_names:
                            path = [reference]
                            while parents[path[-1]] is not None:
                                path.append(parents[path[-1]])
                            path.reverse()
                            edges.append({"from": selected_names[reference], "to": consumer_id, "path": [indices[n] for n in path]})
                        else:
                            queue.append(reference)
            # Remove a visible edge when other visible edges already provide a
            # route, retaining a path witness on each edge that is displayed.
            reduced = []
            for edge in edges:
                adjacency: dict[str, list[str]] = defaultdict(list)
                for other in edges:
                    if other is not edge:
                        adjacency[other["from"]].append(other["to"])
                reached = {edge["from"]}
                queue = deque(reached)
                while queue:
                    for target in adjacency[queue.popleft()]:
                        if target not in reached:
                            reached.add(target)
                            queue.append(target)
                if edge["to"] not in reached:
                    reduced.append(edge)
            ancestors = {preset["root"]}
            while True:
                added = {edge["from"] for edge in reduced if edge["to"] in ancestors} - ancestors
                if not added:
                    break
                ancestors.update(added)
            if ancestors != selected:
                raise ValueError("Proof-map preset contains a step without a proof-reference path to its root: " + preset["id"] + ": " + ", ".join(sorted(selected - ancestors)))
            presets.append({**{key: preset[key] for key in ("id", "label", "root", "description")}, "node_ids": preset["nodes"], "edges": reduced})
        self.emit("assets/dependency-data.js", '// ' + COPYRIGHT + '\nwindow.HOLEVO_DEPENDENCIES = ' + json.dumps(nodes, ensure_ascii=False, separators=(",", ":")) + ';\n')
        self.emit("assets/proof-graph-data.js", '// ' + COPYRIGHT + '\nwindow.HOLEVO_PROOF_GRAPH = ' + json.dumps({"nodes": guide["nodes"], "presets": presets}, ensure_ascii=False, separators=(",", ":")) + ';\n')
        focus = self.result_by_id["prescribed-dimensions"]["lean"][0]["declaration"]
        content = '<p class="eyebrow">The mathematical structure of the formalization</p><h1>How the proofs fit together.</h1><p class="lead">Choose a result, follow its ingredients, and open any step to see what it establishes.</p>'
        content += '<div id="dependency-explorer" data-focus="' + esc(focus) + '"><div class="proof-tabs" role="tablist" aria-label="Dependency view"><button type="button" id="dependency-overview-tab" role="tab" aria-selected="true" aria-controls="dependency-overview-panel">Proof overview</button><button type="button" id="dependency-references-tab" role="tab" aria-selected="false" aria-controls="dependency-references-panel">Lean references</button></div>'
        content += '<section id="dependency-overview-panel" role="tabpanel" aria-labelledby="dependency-overview-tab"><div class="proof-toolbar"><label>Explore <select id="proof-preset">' + ''.join('<option value="' + esc(preset["id"]) + '">' + esc(preset["label"]) + '</option>' for preset in presets) + '</select></label><span class="proof-arrow-key">Ingredient <span aria-hidden="true">→</span> conclusion</span></div><p id="proof-overview-status" class="proof-intro"></p><div class="proof-layout"><div id="proof-map" class="proof-map"></div><aside id="proof-detail" class="proof-detail" aria-live="polite"></aside></div><details class="proof-method"><summary>How these connections are obtained</summary><p>Labels describe the mathematical role of selected Lean results. Each arrow is backed by a path through references in the stored Lean proof or definition; intermediate helpers are grouped away. Expand a step’s supporting paths to inspect those helpers. The overview removes redundant arrows. It records the implemented proof route, with no claim that every ingredient is mathematically indispensable. The detailed tab preserves direct references and their type/proof distinction.</p></details></section>'
        content += '<section id="dependency-references-panel" role="tabpanel" aria-labelledby="dependency-references-tab" hidden><p>Inspect the exact references of any project declaration. Arrows run from a referenced ingredient to the declaration that uses it.</p><div class="graph-controls"><label>Find a theorem or definition <input class="filter" id="dependency-search" type="search" placeholder="Search a result, theorem name, or module…" autocomplete="off" spellcheck="false"></label><div id="dependency-suggestions"></div><label>Follow <select id="dependency-direction"><option value="dependencies">Prerequisites</option><option value="users">Consequences</option></select></label><label>Show <select id="dependency-kind"><option value="value">Proof and definition references</option><option value="type">Statement references</option><option value="all">Both</option></select></label><label>Levels <select id="dependency-depth"><option selected>1</option><option>2</option><option>3</option></select></label><label class="internal-toggle"><input type="checkbox" id="dependency-helpers"> Show Lean internal and private helpers</label><button id="dependency-collapse" class="button" type="button">Reset to one level</button></div><div id="dependency-focus" class="reference-focus"></div><p class="small muted" id="dependency-status" aria-live="polite"></p><div id="dependency-graph" class="dependency-graph"></div><h2>Direct references</h2><p class="small muted">The list includes every matching project reference. The diagram shows a smaller neighborhood and prioritizes the named mathematical steps. Imported-library references and the full type remain on each declaration page.</p><div id="dependency-neighbors"></div><button id="dependency-more" class="button" type="button">Show 50 more references</button></section></div><noscript><p>The interactive diagrams require JavaScript. The selected proof steps are listed below; complete references remain on their declaration pages.</p><ul>' + ''.join('<li>' + self.link(self.declaration_urls[item["declaration"]], esc(item["label"]), page) + ' — ' + esc(item["description"]) + '</li>' for item in guide["nodes"]) + '</ul></noscript>'
        self.page(page, "Dependencies", content, "Dependencies", True, ("assets/dependency-data.js", "assets/proof-graph-data.js", "assets/dependencies.js"))

    def resolve_doc_link(self, destination: str, source: str, page: str) -> str:
        parsed = urlsplit(destination)
        root = "../" * (len(PurePosixPath(page).parts) - 1)
        if parsed.scheme == "lean":
            if parsed.path not in self.declarations:
                raise ValueError("Unknown reader declaration link: " + destination)
            return root + self.declaration_urls[parsed.path]
        if parsed.scheme == "site":
            if not parsed.path or PurePosixPath(parsed.path).is_absolute() or ".." in PurePosixPath(parsed.path).parts:
                raise ValueError("Invalid reader site link: " + destination)
            return root + parsed.path + (("#" + parsed.fragment) if parsed.fragment else "")
        if parsed.scheme in {"guide", "concept", "result", "stage"}:
            group = {"guide": "guides", "concept": "concepts", "result": "results", "stage": "stages"}[parsed.scheme]
            item = self.reader_item(group, parsed.path)
            return root + item["page"] + (("#" + parsed.fragment) if parsed.fragment else "")
        if parsed.scheme or destination.startswith("//"):
            return destination
        if destination.startswith("#"):
            return destination
        resolved = os.path.normpath(str(PurePosixPath(source).parent / unquote(parsed.path))).replace(os.sep, "/")
        if resolved in self.docs:
            return root + self.doc_url(resolved) + (("#" + parsed.fragment) if parsed.fragment else "")
        if resolved in self.inputs and "source/" + resolved in self.outputs:
            return root + "source/" + resolved
        return REPO + "/blob/main/" + resolved + (("#" + parsed.fragment) if parsed.fragment else "")

    def inline_markdown(self, text: str, source: str, page: str) -> str:
        # Escape first. Protect inline code and links before emphasis handling.
        slots: list[str] = []

        def hold(value: str) -> str:
            slots.append(value)
            return "\x00" + str(len(slots) - 1) + "\x00"

        text = re.sub(r"`([^`]+)`", lambda m: hold("<code>" + esc(m.group(1)) + "</code>"), text)
        text = re.sub(r"(?<!\\)\$([^$\n]+)\$", lambda m: hold(self.math(m.group(1))), text)
        text = re.sub(r"\\\((.+?)\\\)", lambda m: hold(self.math(m.group(1))), text)
        text = re.sub(r"\[([^\]]+)\]\(([^)]+)\)", lambda m: hold('<a href="' + esc(self.resolve_doc_link(m.group(2), source, page)) + '">' + esc(m.group(1)) + '</a>'), text)
        text = esc(text)
        text = re.sub(r"\*\*(.+?)\*\*", r"<strong>\1</strong>", text)
        text = re.sub(r"(?<!\*)\*([^*]+)\*(?!\*)", r"<em>\1</em>", text)
        # A link label can contain a protected inline-code slot. Expand earlier
        # slots inside each later slot before restoring the outer text, so code
        # labels remain real <code> elements instead of leaking NUL markers.
        restored: list[str] = []

        def restore_prior(match: re.Match) -> str:
            index = int(match.group(1))
            if index >= len(restored):
                raise ValueError("Invalid Markdown placeholder nesting")
            return restored[index]

        for slot in slots:
            restored.append(re.sub("\x00(\\d+)\x00", restore_prior, slot))
        return re.sub("\x00(\\d+)\x00", lambda m: restored[int(m.group(1))], text)

    def render_markdown(self, source: str, text: str, page: str, heading_shift: int = 1, anchor_prefix: str = "") -> str:
        """Readable subset of Markdown; exact original is always downloadable."""
        lines = text.splitlines()
        out = []
        i = 0
        used_ids: dict[str, int] = defaultdict(int)
        while i < len(lines):
            line = lines[i]
            if not line.strip():
                i += 1
                continue
            if line.startswith("<!--"):
                while i < len(lines) and "-->" not in lines[i]:
                    i += 1
                i += 1
                continue
            if line.strip() in {"$$", r"\["}:
                end = "$$" if line.strip() == "$$" else r"\]"
                equation = []
                i += 1
                while i < len(lines) and lines[i].strip() != end:
                    equation.append(lines[i])
                    i += 1
                if i == len(lines):
                    raise ValueError("Unclosed display math in " + source)
                out.append(self.math("\n".join(equation), True))
                i += 1
                continue
            if line.startswith("```"):
                language = line[3:].strip()
                code = []
                i += 1
                while i < len(lines) and not lines[i].startswith("```"):
                    code.append(lines[i])
                    i += 1
                out.append(command("\n".join(code)) if language in {"sh", "bash", "shell", "text", "lean"} else '<pre><code>' + esc("\n".join(code)) + '</code></pre>')
                i += 1
                continue
            heading = re.match(r"^(#{1,6})\s+(.+)$", line)
            if heading:
                level = min(len(heading.group(1)) + heading_shift, 6)
                name = heading.group(2)
                slug = re.sub(r"[^\w\- ]", "", name.lower()).replace(" ", "-")
                used_ids[slug] += 1
                if used_ids[slug] > 1:
                    slug += "-" + str(used_ids[slug]-1)
                slug = anchor_prefix + slug
                out.append(f'<h{level} id="{esc(slug)}">' + self.inline_markdown(name, source, page) + f'</h{level}>')
                i += 1
                continue
            if i + 1 < len(lines) and "|" in line and re.match(r"^\s*\|?\s*:?-{3,}", lines[i+1]):
                rows = [line]
                i += 2
                while i < len(lines) and "|" in lines[i] and lines[i].strip():
                    rows.append(lines[i])
                    i += 1
                table = '<div class="table-scroll"><table>'
                for row_num, row in enumerate(rows):
                    # Protect bars within code spans from accidental cell splitting.
                    protected = re.sub(r"`([^`]+)`", lambda m: "`" + m.group(1).replace("|", "\x01") + "`", row)
                    cells = [x.strip().replace("\x01", "|") for x in protected.strip().strip("|").split("|")]
                    tag = "th" if row_num == 0 else "td"
                    table += '<tr>' + ''.join(f'<{tag}>' + self.inline_markdown(cell, source, page) + f'</{tag}>' for cell in cells) + '</tr>'
                out.append(table + '</table></div>')
                continue
            item = re.match(r"^\s*(?:[-*]|\d+\.)\s+(.+)$", line)
            if item:
                ordered = bool(re.match(r"^\s*\d+\.", line))
                items = []
                while i < len(lines):
                    item = re.match(r"^\s*(?:[-*]|\d+\.)\s+(.+)$", lines[i])
                    if not item:
                        break
                    item_lines = [item.group(1)]
                    i += 1
                    while i < len(lines) and re.match(r"^\s{2,}\S", lines[i]) and not re.match(r"^\s*(?:[-*]|\d+\.)\s+", lines[i]):
                        item_lines.append(lines[i].strip())
                        i += 1
                    items.append('<li>' + self.inline_markdown(" ".join(item_lines), source, page) + '</li>')
                tag = "ol" if ordered else "ul"
                out.append(f'<{tag}>' + ''.join(items) + f'</{tag}>')
                continue
            if line.startswith(">"):
                quote = []
                while i < len(lines) and lines[i].startswith(">"):
                    quote.append(lines[i].lstrip(">").strip())
                    i += 1
                out.append('<blockquote>' + self.inline_markdown(" ".join(quote), source, page) + '</blockquote>')
                continue
            if re.match(r"^\s*(---+|\*\*\*+)\s*$", line):
                out.append('<hr>')
                i += 1
                continue
            paragraph = [line.strip()]
            i += 1
            while i < len(lines) and lines[i].strip() and lines[i].strip() not in {"$$", r"\["} and not re.match(r"^(?:#{1,6}\s|```|\s*[-*]\s|\s*\d+\.\s|>)", lines[i]):
                if i + 1 < len(lines) and "|" in lines[i] and re.match(r"^\s*\|?\s*:?-{3,}", lines[i+1]):
                    break
                paragraph.append(lines[i].strip())
                i += 1
            out.append('<p>' + self.inline_markdown(" ".join(paragraph), source, page) + '</p>')
        return "\n".join(out)

    def build_docs(self) -> None:
        page = "docs/index.html"
        content = '<p class="eyebrow">Repository prose and provenance</p><h1>Documents.</h1><p class="lead">The project’s status, corrections, architecture, verification evidence, and attribution.</p><p>These pages render the committed Markdown documents, including their mathematical notation. Exact Markdown downloads remain available on every page.</p><div class="cards">'
        for source, text in self.docs.items():
            title_match = re.search(r"(?m)^#\s+(.+)$", text)
            title = title_match.group(1) if title_match else source
            doc_page = self.doc_url(source)
            content += '<div class="card"><h3>' + self.link(doc_page, esc(title), page) + '</h3><p><code>' + esc(source) + '</code></p></div>'
            body = '<div class="breadcrumb">' + self.link("docs/index.html", "Documents", doc_page) + ' / ' + esc(source) + '</div><p class="eyebrow">Repository document</p><h1>' + esc(title) + '</h1><p>' + self.link("source/" + source, "Download exact Markdown", doc_page) + ' · <a href="' + REPO + '/blob/main/' + source + '">View on GitHub</a></p><div class="document-body">' + self.render_markdown(source, text, doc_page) + '</div>'
            self.page(doc_page, title, body, "Documents")
        content += '</div>'
        self.page(page, "Documents", content, "Documents", True)

    def build_about(self) -> None:
        page = "about.html"
        content = '<p class="eyebrow">Sources and trust</p><h1>About these pages.</h1><p class="lead">A mathematical reader guide connected to this repository’s exact formal sources.</p><p>The explanatory organization follows <a href="https://jwang226.github.io/QMDL/">QMDL</a>: an introduction, concepts, result explanations, a proof route, and links in both directions between mathematics and Lean. The formal source explorer also follows the structure of the <a href="https://tianyipeng.github.io/fermats-last-theorem/">Fermat’s Last Theorem documentation</a>. The project’s explanations, design, and generator are original material. Mathematical notation uses a locally bundled KaTeX 0.19.0 distribution under the MIT license; ' + self.link("assets/katex/LICENSE", "its original license", page) + ' is retained.</p><p>The mathematical chapters, concept entries, all 25 result explanations, and seven proof-stage explanations are handwritten documentation. Every attached Lean declaration is validated against the actual export. The ' + self.link("reader-map.json", "machine-readable explanation map", page) + ' records these reading correspondences and source hashes. It does not assert formal equivalence of the prose and proof terms.</p>'
        content += '<h2>What is shown, and how</h2><table class="about-table"><tbody>'
        for label, text in [("Result correspondence", "The 25 records and 49 exact declaration references are read from metadata/results.json. Status and scope notes are carried through unchanged."), ("Quoted headers", "A conservative lexical recognizer quotes a unique literal declaration header before its outer :=. It hides comments and strings while locating syntax, then quotes the original source text. Ambiguous syntax falls back to full source."), ("Elaborated declarations", f"All {len(self.declarations):,} project constants are exported from the actual Lean environment into metadata/declarations.json. Individual pages display a readable elaborated type, with universe parameters separately listed, and link to the exact full source module. A shared kernel expression DAG preserves every kernel-relevant argument, universe, binder and name component, while omitting kernel-irrelevant metadata annotations."), ("Source context", "A literal source header does not expand namespace variables, implicit instances, notation, imports, or local settings. Its display is distinguished from the complete exported type. An exact declaration line is linked only when available from source extraction or trustworthy declaration metadata."), ("Import relationships", "Direct imports are read from literal import commands. Reverse links cover all 366 proof modules and three aggregate entry points. These remain distinct from individual constant references."), ("Constant dependencies", "Type and stored-value expressions provide exact direct constant-reference lists. Reverse project links are computed from those lists. The proof overview gives mathematical labels to selected theorems, with each arrow backed by an actual proof/definition-reference path. Intermediate helpers and redundant arrows are omitted; their paths remain inspectable. A detailed view retains direct type and proof/definition references. No minimality or informal-proof equivalence is asserted."), ("Search", f"Search indexes every one of the {len(self.declarations):,} exported project constants, all result names and paper labels, and all source modules. Names flagged by Lean’s internal, internal-detail or private predicates can be included explicitly; these flags do not identify every generated constant."), ("Export freshness", "The generator verifies the exported SHA-256 provenance against every proof source, aggregate entry point, toolchain and dependency manifest before generating pages. A stale source blocks the documentation build. This checks provenance consistency; it does not independently re-execute the exporter or prove metadata integrity."), ("Repository documents", "A small offline Markdown renderer displays committed prose. Exact Markdown files are available when typography or formula syntax needs checking."), ("Verification evidence", "The retained successful GitHub CI run certifies a full project-source rebuild and Lean audit at its recorded commit. Comparator execution and independent-kernel verification remain pending."), ("Offline use", "Open html/index.html directly after cloning, or visit the GitHub Pages site. Search and dependency data are local JavaScript assets, so no server, CDN, telemetry, or network request is required to browse."), ("Licensing", "No blanket open-source license has been selected for project-owned code or the manuscript. Copyright and original third-party attribution are preserved.")]:
            content += '<tr><td>' + esc(label) + '</td><td>' + esc(text) + '</td></tr>'
        content += '</tbody></table><h2>Complete kernel type expressions</h2><p>Every elaborated type is preserved as a shared kernel expression DAG: names, universes, binders and all arguments are retained; kernel-irrelevant metadata annotations are omitted. This canonical JSON is a machine expression representation, distinct from Lean source text. It is stored losslessly as gzip/base64, with byte counts and SHA-256 hashes. The generator stream-checks each payload and validates its node references before publishing a complete <code>.expr.json.gz</code> artifact. Declaration pages show readable Lean types and decode at most a 64,000-character JSON preview on expansion; modern browsers also offer the entire decoded JSON download. Compressed downloads remain available without browser gzip support.</p><h2>Rebuild the documentation</h2><p>Python 3 is the only dependency. From the repository root:</p>' + command('python3 tools/docs-site/build.py\npython3 tools/docs-site/build.py --check')
        content += '<p>The freshness check compares generated bytes and validates every local file link, HTML anchor, search target, and source download. It is a documentation check; proof verification uses the separate commands on the verification page.</p><p>The generator records input hashes, counts, and extraction results in ' + self.link("generation.json", "generation.json", page) + '. There are no build timestamps or local absolute paths in the generated site.</p>'
        content += '<p>' + self.link("verify.html", "Proof verification", page) + ' · ' + self.link(self.doc_url("COPYRIGHT.md"), "Copyright", page) + ' · ' + self.link(self.doc_url("THIRD_PARTY_NOTICES.md"), "Third-party notices", page) + '</p>'
        self.page(page, "About", content, "About")

    def generate(self) -> None:
        self.emit(".nojekyll", b"")
        for name in ["site.css", "site.js", "dependencies.js", "math.js"]:
            self.emit("assets/" + name, (TOOLS / name).read_bytes())
        for path in sorted((TOOLS / "vendor" / "katex").rglob("*")):
            if path.is_file():
                rel = path.relative_to(ROOT).as_posix()
                data = path.read_bytes()
                self.inputs[rel] = hashlib.sha256(data).hexdigest()
                self.emit("assets/katex/" + path.relative_to(TOOLS / "vendor" / "katex").as_posix(), data)
        self.build_reader()
        self.build_overview()
        self.build_verify()
        self.build_route()
        self.build_results()
        self.build_declarations()
        self.build_dependencies()
        self.build_modules()
        self.build_imports()
        self.build_docs()
        self.build_about()
        self.search.sort(key=lambda x: (bool(x.get("internal")), x["title"].lower()))
        self.emit("assets/search-data.js", '// ' + COPYRIGHT + '\nwindow.HOLEVO_SEARCH = ' + json.dumps(self.search, ensure_ascii=False, separators=(",", ":")) + ';\n')
        self.emit("generation.json", pretty({
            "schema_version": 1, "generator": "tools/docs-site/build.py", "site": SITE,
            "mathematical_guide_chapters": len(self.reader["guides"]), "concept_explanations": len(self.reader["concepts"]), "explained_results": len(self.reader["results"]),
            "explanation_to_lean_map": "reader-map.json", "math_renderer": {"name": "KaTeX", "version": "0.19.0", "license": "MIT", "offline": True},
            "module_count": len(self.modules), "proof_module_count": 366, "aggregate_entry_points": 3, "correspondence_records": len(self.results),
            "mapped_declarations": len(self.headers), "literal_headers_quoted": sum(header is not None for header, line in self.headers.values()),
            "exported_project_declarations": len(self.declarations),
            "internal_detail_or_private_declarations": sum(hidden_declaration(x) for x in self.declarations.values()),
            "direct_project_constant_reference_edges": sum(len(x["project_dependencies"]) for x in self.declarations.values()),
            "declaration_export_sha256": self.inputs["metadata/declarations.json"],
            "compressed_full_type_artifacts": sum(record.get("type_encoding") == "gzip+base64" for record in self.declarations.values()),
            "full_type_uncompressed_bytes": sum(record.get("type_uncompressed_bytes", len(record["type"].encode())) for record in self.declarations.values()),
            "header_fallbacks": [name for name, (header, line) in self.headers.items() if header is None],
            "search_entries": len(self.search), "module_import_edges": sum(sum(x in self.modules for x in m["imports"]) for m in self.modules.values()),
            "evidence_commit": self.ci["commit"], "evidence_run": self.ci["url"],
            "proof_verification_performed_by_site_generator": False,
            "input_sha256": dict(sorted(self.inputs.items())),
        }))


class Links(HTMLParser):
    def __init__(self) -> None:
        super().__init__()
        self.ids: set[str] = set()
        self.links: list[str] = []
        self.duplicate_ids: list[str] = []

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        values = dict(attrs)
        if values.get("id"):
            value = values["id"]
            if value in self.ids:
                self.duplicate_ids.append(value)
            self.ids.add(value)
        for attr in ["href", "src"]:
            if values.get(attr):
                self.links.append(values[attr])


def validate(site: Site) -> list[str]:
    errors: list[str] = []
    pages = {}
    dependency_routes = {PurePosixPath(path).stem for path in site.declaration_urls.values()}
    guide = json.loads((TOOLS / "proof-graph.json").read_text())
    dependency_routes.update("overview-" + preset["id"] for preset in guide["presets"])
    for rel, data in site.outputs.items():
        if rel.endswith(".html"):
            if b"\x00" in data:
                errors.append(rel + ": generated HTML contains a NUL placeholder")
            parsed = Links()
            parsed.feed(data.decode())
            pages[rel] = parsed
            errors.extend(rel + ": duplicate id " + value for value in parsed.duplicate_ids)
    for rel, parsed in pages.items():
        for destination in parsed.links:
            url = urlsplit(destination)
            if url.scheme or url.netloc:
                continue
            target = os.path.normpath(str(PurePosixPath(rel).parent / unquote(url.path))) if url.path else rel
            target = target.replace(os.sep, "/")
            if target not in site.outputs:
                errors.append(rel + ": broken local link " + destination)
            elif url.fragment and target in pages and unquote(url.fragment) not in pages[target].ids:
                # Dependency hashes are explicit client-side routes, validated
                # against the same complete constant registry used by the UI.
                if target != "dependencies.html" or unquote(url.fragment) not in dependency_routes:
                    errors.append(rel + ": missing anchor " + destination)
    for entry in site.search:
        url = urlsplit(entry["url"])
        if url.path not in pages or (url.fragment and url.fragment not in pages[url.path].ids):
            errors.append("Search target missing: " + entry["url"])
    for name, module in site.modules.items():
        if site.outputs["source/" + module["path"]] != (ROOT / module["path"]).read_bytes():
            errors.append("Source download differs: " + name)
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Check byte-for-byte freshness and link/source consistency without writing")
    args = parser.parse_args()
    site = Site()
    site.generate()
    errors = validate(site)
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    if args.check:
        actual = {p.relative_to(OUT).as_posix() for p in OUT.rglob("*") if p.is_file()} if OUT.exists() else set()
        expected = set(site.outputs)
        errors.extend("Missing generated file: " + name for name in sorted(expected - actual))
        errors.extend("Unexpected generated file: " + name for name in sorted(actual - expected))
        for name in sorted(expected & actual):
            if (OUT / name).read_bytes() != site.outputs[name]:
                errors.append("Stale generated file: " + name)
        if errors:
            print("\n".join(errors), file=sys.stderr)
            return 1
    else:
        OUT.mkdir(exist_ok=True)
        # Only this generated directory is managed by the generator.
        for path in OUT.rglob("*"):
            if path.is_file() and path.relative_to(OUT).as_posix() not in site.outputs:
                path.unlink()
        for name, data in site.outputs.items():
            target = OUT / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
    metrics = json.loads(site.outputs["generation.json"])
    print(("Site check passed" if args.check else "Site generated") + f': {len(site.outputs)} files, {metrics["module_count"]} project modules, {metrics["correspondence_records"]} result records, {metrics["exported_project_declarations"]:,} exported declarations, {metrics["direct_project_constant_reference_edges"]:,} direct project constant-reference edges, {metrics["search_entries"]} search entries.')
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
