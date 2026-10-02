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
from collections import defaultdict
import hashlib
import html
from html.parser import HTMLParser
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
NAV = [("Overview", "index.html"), ("Verify", "verify.html"), ("Proof route", "route.html"),
       ("Results", "results.html"), ("Modules", "modules.html"),
       ("Imports", "imports.html"), ("Documents", "docs/index.html"), ("About", "about.html")]
STAGES = [
    ("Actual channels and entropy", "Begin with finite density matrices, concrete Kraus channels, output ensembles, and entropy. The channel endpoints refer to these physical objects.",
     ["purity-entropy", "bell-entropy"],
     ["StateEnsembles", "QuantumHolevo", "BellOutput", "BlockBell"]),
    ("Free comparison and finite Haar estimates", "The free-group norm bound is proved. Actual Haar integration and finite matrix moment estimates supply the quantitative input, rather than an assumed strong-convergence theorem.",
     ["free-collins-youn", "haar-moment-range", "universal-factorization"],
     ["CollinsYounProduct", "HaarAveraging", "HaarWeingartenGram", "HaarIteratedExpectation"]),
    ("Repaired combinatorial counts", "Two intermediate estimates need correction. The source includes literal counterexamples and the replacements used by the channel construction; the original manuscript still needs these edits.",
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


def command(text: str) -> str:
    return '<div class="command"><button class="copy" type="button" aria-label="Copy command">Copy</button><pre><code>' + esc(text.rstrip()) + '</code></pre></div>'


class Site:
    def __init__(self) -> None:
        self.outputs: dict[str, bytes] = {}
        self.inputs: dict[str, str] = {}
        self.search: list[dict[str, str]] = []
        self.meta = json.loads(self.read("metadata/results.json"))
        self.results = self.meta["results"]
        self.result_by_id = {x["id"]: x for x in self.results}
        self.modules: dict[str, dict] = {}
        self.used_by: dict[str, list[str]] = defaultdict(list)
        self.module_results: dict[str, list[dict]] = defaultdict(list)
        self.headers: dict[str, tuple[str | None, int | None]] = {}
        self.docs: dict[str, str] = {}
        self.ci = json.loads(self.read("verification/github-actions-141f355.json"))
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
        for result in self.results:
            for ref in result["lean"]:
                module_name = ref["file"][:-5].replace("/", ".")
                if module_name not in self.modules:
                    raise ValueError("Result references unavailable module: " + ref["file"])
                self.module_results[module_name].append(result)
                self.headers[ref["declaration"]] = declaration_header(self.modules[module_name]["source"], ref["declaration"])
        doc_paths = ["README.md", "PROOF-PATH.md", "COPYRIGHT.md", "THIRD_PARTY_NOTICES.md", "verification/README.md", "ComparatorChallenges/README.md"]
        doc_paths += [p.relative_to(ROOT).as_posix() for p in sorted((ROOT / "docs").glob("*.md"))]
        for rel in doc_paths:
            self.docs[rel] = self.read(rel)
            self.emit("source/" + rel, self.docs[rel])
        source_paths = ["paper/nonadditivity.tex", "formalization.yaml", "metadata/results.json", "verification/github-actions-141f355.json", "verification/github-actions-141f355-excerpt.log", "Audit.lean", "All.lean", "Nonadditivity.lean", "lean-toolchain", "lake-manifest.json", "verification/lean/run.sh", "verification/comparator/run.sh", "requirements-validation.txt", "check.sh"]
        source_paths += [p.relative_to(ROOT).as_posix() for p in sorted((ROOT / "ComparatorChallenges").glob("*")) if p.suffix in {".lean", ".json"}]
        for rel in source_paths:
            self.emit("source/" + rel, self.read(rel))
        # Track the generator and its own assets in the deterministic manifest.
        for name in ["build.py", "site.css", "site.js", "README.md"]:
            rel = "tools/docs-site/" + name
            if (ROOT / rel).exists():
                self.read(rel)

    def read(self, rel: str) -> str:
        data = (ROOT / rel).read_bytes()
        self.inputs[rel] = hashlib.sha256(data).hexdigest()
        return data.decode("utf-8")

    def emit(self, rel: str, content: str | bytes) -> None:
        self.outputs[rel] = content.encode("utf-8") if isinstance(content, str) else content

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

    def page(self, path: str, title: str, content: str, active: str, wide: bool = False) -> None:
        root = "../" * (len(PurePosixPath(path).parts) - 1)
        nav = "".join(f'<a href="{root + url}"' + (' aria-current="page"' if label == active else "") + f'>{label}</a>' for label, url in NAV)
        footer = '<p>Reader documentation for exact Lean sources; the source and its declared context determine what is proved.</p>'
        footer += '<p>Lean 4.29.0-rc6 · Mathlib <code>f156f7ab…</code> · Only <code>propext</code>, <code>Classical.choice</code>, and <code>Quot.sound</code> permitted in solution dependencies.</p>'
        footer += '<p class="footer-links">' + self.link("about.html", "About these pages", path) + self.link("generation.json", "Generation record", path) + f'<a href="{REPO}">GitHub repository</a></p>'
        self.emit(path, f'''<!doctype html>
<!-- {COPYRIGHT} See COPYRIGHT.md for attribution. -->
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<meta name="description" content="A reader guide to Lean proofs of Holevo additivity gaps, exact source statements, and reproducible verification.">
<title>{esc(title)} · Holevo Additivity Gap</title><link rel="stylesheet" href="{root}assets/site.css"></head>
<body data-root="{root}"><header class="top"><div class="top-inner">
<a class="brand" href="{root}index.html">Holevo Additivity Gap <span>in Lean 4</span></a>
<nav aria-label="Main navigation">{nav}</nav>
<div class="search-wrap"><label class="hidden" for="site-search">Search results and modules</label><input id="site-search" type="search" placeholder="Search result names, exact declarations, paper labels, or modules…" autocomplete="off" spellcheck="false" aria-label="Search results and modules"><div id="search-results" class="search-results" hidden></div></div>
</div></header><main><article class="{'wide' if wide else 'prose'}">{content}</article></main>
<footer>{footer}</footer><script src="{root}assets/search-data.js"></script><script src="{root}assets/site.js"></script></body></html>
''')

    def card(self, result_id: str, page: str) -> str:
        result = self.result_by_id[result_id]
        return '<div class="card">' + self.tag(result["status"]) + '<h3>' + self.result_link(result_id, page) + '</h3><p>' + esc(result["notes"]) + '</p></div>'

    def build_overview(self) -> None:
        page = "index.html"
        content = '''<div class="hero"><div><p class="eyebrow">A reader guide to the formalization</p>
<h1>Unbounded Holevo additivity gaps,<br>in finite dimensions.</h1>
<p class="lead">Explore the channel constructions, the proof route, and the exact Lean statements accompanying Jinzhao Wang’s manuscript.</p>
<p>Actual finite CPTP channels exhibit large gaps between single-use Holevo information and information available across multiple uses. Operational capacity is defined using physical codes and then identified with regularized Holevo information.</p>
<div class="actions">'''
        content += self.link("verify.html", "Reproduce the checks", page, "button primary") + self.link("results/prescribed-dimensions.html", "Read the main theorem", page, "button") + self.link("route.html", "Follow the proof route", page, "button")
        content += '''</div></div><aside class="hero-note"><h2>What is established</h2>
<p>The principal formal endpoints have no unfinished solution proofs or project-specific axioms.</p>
<p>A full project-source rebuild, aggregate axiom audit, all 49 catalog declaration checks, and six local challenge statement checks passed in GitHub CI.</p>
<p><strong>Comparator and an independent kernel have not been run.</strong> The full manuscript is not formalized; two repaired counting arguments remain to be incorporated into the manuscript.</p>'''
        content += self.link("verify.html#evidence", "Read the evidence and trust limits →", page) + '</aside></div>'
        content += '<div class="numbers">' + ''.join(f'<div><b>{n}</b><span>{label}</span></div>' for n, label in [(len(self.modules), "modules: 366 proof files + 3 entry points"), (len(self.results), "manuscript correspondence records"), (len(self.headers), "mapped Lean declarations"), ("3", "standard axioms permitted")]) + '</div>'
        content += '<h2>Start with the results</h2><div class="cards">'
        for result_id in ["prescribed-dimensions", "operational-coding", "simultaneous-separation", "weyl-all-uses", "growing-family-cost", "correction-important-times"]:
            content += self.card(result_id, page)
        content += '</div><h2>The main formal statement</h2><p>This is the literal declaration header from <code>HaarPrescribedBound.lean</code>. Its ambient namespace, imports, and local settings remain visible on the full source page.</p>'
        main_ref = self.result_by_id["prescribed-dimensions"]["lean"][0]
        header, line = self.headers[main_ref["declaration"]]
        if header:
            content += command(header)
        content += '<p>' + self.link("results/prescribed-dimensions.html", "Scope, manuscript labels, and source context →", page) + '</p>'
        content += '<h2>How to read this project</h2><div class="cards">'
        for title, url, text in [("Proof route", "route.html", "A seven-stage reading order, with links to the endpoints and modules in each part of the argument."), ("Exact source", "modules.html", "Every proof module in full, with line anchors, source downloads, direct imports, and reverse import links."), ("Scope and corrections", "docs/docs--FORMALIZATION_STATUS.html", "Precisely what the formalization covers, which older interfaces remain conditional, and where the manuscript needs correction.")]:
            content += '<div class="card"><h3>' + self.link(url, title, page) + '</h3><p>' + esc(text) + '</p></div>'
        content += '</div><p class="small muted">English descriptions and the route are reading aids. Result correspondence is non-exhaustive and does not itself certify informal-to-formal equivalence. Import links describe modules, not a theorem-level dependency graph.</p>'
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
        content += '</tbody></table><p><a href="' + esc(self.ci["url"]) + '">Successful GitHub Actions run</a> · ' + self.link("source/verification/github-actions-141f355.json", "Machine-readable record", page) + ' · ' + self.link("source/verification/github-actions-141f355-excerpt.log", "Retained log excerpt", page) + '</p>'
        content += '<h2>What these checks certify</h2><p>The audit permits only <code>propext</code>, <code>Classical.choice</code>, and <code>Quot.sound</code> across all project declarations, including definitions with proof fields and private helpers. The six intentional expected-statement placeholders in isolated Comparator challenge files are excluded from the solution build.</p><p>Kernel acceptance concerns exactly the formal statements in their Lean context. Mathematical review must still assess their correspondence to the manuscript. The original manuscript has not been edited to incorporate the two repaired intermediate counting arguments.</p>'
        content += '<p>' + self.link(self.doc_url("docs/FORMALIZATION_STATUS.md"), "Formalization status", page) + ' · ' + self.link(self.doc_url("docs/CORRECTIONS.md"), "Manuscript corrections", page) + '</p>'
        self.page(page, "Verify", content, "Verify")

    def build_route(self) -> None:
        page = "route.html"
        content = '<p class="eyebrow">A guide to the argument</p><h1>The proof route.</h1><p class="lead">A reading order through the main construction, its repaired estimates, and the capacity consequences.</p><p>These stages summarize the repository’s proof map. They are not a mechanically extracted theorem-dependency graph. The module import catalog records exact direct imports separately.</p>'
        for n, (title, text, results, modules) in enumerate(STAGES, 1):
            content += f'<section class="route-stage" id="stage-{n}"><h2><span class="stage-number">{n}</span>{esc(title)}</h2><p>{esc(text)}</p><ul>'
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
        content = '<p class="eyebrow">Manuscript-to-Lean correspondence</p><h1>Result catalog.</h1><p class="lead">25 correspondence records connect manuscript labels to exact declarations, with scope and limitations attached.</p><p>This non-exhaustive catalog includes proved endpoints, corrected intermediate arguments, and broader statements whose formalization is not asserted. “Proved” describes the formal endpoint at its stated scope.</p>'
        content += '<input class="filter" aria-label="Filter result catalog" placeholder="Filter by result, paper label, or declaration…" data-filter=".catalog-item" data-status="catalog-status"><p class="small muted" id="catalog-status">25 correspondence records</p>'
        for result in self.results:
            terms = result["name"] + " " + " ".join(result["paper"]["labels"]) + " " + " ".join(x["declaration"] for x in result["lean"])
            content += '<section class="catalog-item" data-search="' + esc(terms) + '"><div class="catalog-top">' + self.tag(result["status"]) + '<span class="small muted">' + esc(result["correspondence"].replace("_", " ")) + '</span></div><h2>' + self.result_link(result["id"], page) + '</h2>'
            content += '<div class="label-list">' + ''.join('<code>' + esc(x) + '</code>' for x in result["paper"]["labels"]) + '</div><p>' + esc(result["notes"] or "See the linked formal declaration and its complete source context.") + '</p></section>'
            self.build_result(result)
        self.page(page, "Results", content, "Results")

    def build_result(self, result: dict) -> None:
        page = "results/" + result["id"] + ".html"
        content = '<div class="breadcrumb">' + self.link("results.html", "Result catalog", page) + ' / ' + esc(result["id"]) + '</div>'
        content += '<p class="eyebrow">' + esc(result["correspondence"].replace("_", " ")) + '</p><h1>' + esc(result["name"]) + '</h1>' + self.tag(result["status"])
        if result["notes"]:
            content += '<p class="lead">' + esc(result["notes"]) + '</p>'
        if result["status"] == "not_formalized":
            content += '<div class="note warning">No proof of the broader claim is asserted. Any listed predicates are definitions or conditional interfaces, not proofs that those predicates hold.</div>'
        content += '<h2>Manuscript correspondence</h2><div class="label-list">' + ''.join('<code>' + esc(x) + '</code>' for x in result["paper"]["labels"]) + '</div>'
        if result["paper"].get("locator"):
            content += '<p>' + esc(result["paper"]["locator"]) + '</p>'
        content += '<p class="small muted">The included manuscript is the preserved, uncorrected source. Correspondence entries are reading aids rather than an exhaustive statement-equivalence certificate.</p><p>' + self.link("source/paper/nonadditivity.tex", "Original manuscript source", page) + ' · ' + self.link("source/metadata/results.json", "Correspondence metadata", page) + '</p>'
        if result.get("comparator_config"):
            content += '<p class="small">Comparator configuration: ' + self.link("source/" + result["comparator_config"], '<code>' + esc(result["comparator_config"]) + '</code>', page) + '. End-to-end Comparator execution is pending.</p>'
        for n, ref in enumerate(result["lean"], 1):
            name = ref["declaration"]
            module_name = ref["file"][:-5].replace("/", ".")
            header, line = self.headers[name]
            anchor = f'declaration-{n}'
            source_url = self.module_url(module_name) + (f'#L{line}' if line else "")
            content += '<section class="declaration" id="' + anchor + '"><p class="eyebrow">' + esc(ref["role"].replace("_", " ")) + '</p><h2>' + esc(name) + '</h2>'
            if header:
                content += command(header)
                content += '<p class="source-context">Literal source header; namespace variables, local instances, imports, and notation are not expanded. Open the full module to read the surrounding context.</p>'
            else:
                content += '<p>A standalone header cannot be safely extracted by this documentation generator. Read the exact full module instead.</p>'
            content += '<p>' + self.link(source_url, "Exact source" + (f' at line {line}' if line else ""), page) + ' · <a href="' + REPO + '/blob/main/' + ref["file"] + (f'#L{line}' if line else "") + '">View on GitHub</a></p></section>'
            self.search.append({"title": name, "detail": result["name"] + " · " + ref["role"].replace("_", " "), "url": page + "#" + anchor, "search": (name + " " + result["name"] + " " + " ".join(result["paper"]["labels"])).lower()})
        if not result["lean"]:
            content += '<p>No formal declaration is attached to this broader correspondence entry.</p>'
        content += '<p>' + self.link("verify.html", "Verification and trust limits", page) + ' · ' + self.link(self.doc_url("docs/FORMALIZATION_STATUS.md"), "Full scope statement", page) + '</p>'
        self.search.append({"title": result["name"], "detail": result["status"].replace("_", " ") + " · " + ", ".join(result["paper"]["labels"]), "url": page, "search": (result["name"] + " " + result["id"] + " " + " ".join(result["paper"]["labels"])).lower()})
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
        content += '</div></div><p class="small muted">Relationships above come from literal import commands, not from references between individual declarations. Source text below is complete and unchanged.</p><h2 id="source">Full module</h2><pre class="source">'
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

    def resolve_doc_link(self, destination: str, source: str, page: str) -> str:
        parsed = urlsplit(destination)
        if parsed.scheme or destination.startswith("//"):
            return destination
        if destination.startswith("#"):
            return destination
        resolved = os.path.normpath(str(PurePosixPath(source).parent / unquote(parsed.path))).replace(os.sep, "/")
        root = "../" * (len(PurePosixPath(page).parts) - 1)
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
        text = re.sub(r"\[([^\]]+)\]\(([^)]+)\)", lambda m: hold('<a href="' + esc(self.resolve_doc_link(m.group(2), source, page)) + '">' + esc(m.group(1)) + '</a>'), text)
        text = esc(text)
        text = re.sub(r"\*\*(.+?)\*\*", r"<strong>\1</strong>", text)
        text = re.sub(r"(?<!\*)\*([^*]+)\*(?!\*)", r"<em>\1</em>", text)
        return re.sub("\x00(\\d+)\x00", lambda m: slots[int(m.group(1))], text)

    def render_markdown(self, source: str, text: str, page: str) -> str:
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
                level = min(len(heading.group(1)) + 1, 6)
                name = heading.group(2)
                slug = re.sub(r"[^\w\- ]", "", name.lower()).replace(" ", "-")
                used_ids[slug] += 1
                if used_ids[slug] > 1:
                    slug += "-" + str(used_ids[slug]-1)
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
            while i < len(lines) and lines[i].strip() and not re.match(r"^(?:#{1,6}\s|```|\s*[-*]\s|\s*\d+\.\s|>)", lines[i]):
                if i + 1 < len(lines) and "|" in lines[i] and re.match(r"^\s*\|?\s*:?-{3,}", lines[i+1]):
                    break
                paragraph.append(lines[i].strip())
                i += 1
            out.append('<p>' + self.inline_markdown(" ".join(paragraph), source, page) + '</p>')
        return "\n".join(out)

    def build_docs(self) -> None:
        page = "docs/index.html"
        content = '<p class="eyebrow">Repository prose and provenance</p><h1>Documents.</h1><p class="lead">The project’s status, corrections, architecture, verification evidence, and attribution.</p><p>These pages render the committed Markdown documents. Exact Markdown downloads remain available on every page; formulas in repository prose are preserved as text rather than reinterpreted as Lean statements.</p><div class="cards">'
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
        content = '<p class="eyebrow">Sources and trust</p><h1>About these pages.</h1><p class="lead">A deterministic reader site generated from this repository’s actual source files and result metadata.</p><p>The information architecture follows the reader-oriented <a href="https://tianyipeng.github.io/fermats-last-theorem/">Fermat’s Last Theorem documentation</a>: overview, route, searchable results, exact statements, source modules, and repository documents. The design, generator, and assets here are original project material.</p>'
        content += '<h2>What is shown, and how</h2><table class="about-table"><tbody>'
        for label, text in [("Result correspondence", "The 25 records and 49 exact declaration references are read from metadata/results.json. Status and scope notes are carried through unchanged."), ("Quoted headers", "A conservative lexical recognizer quotes a unique literal declaration header before its outer :=. It hides comments and strings while locating syntax, then quotes the original source text. Ambiguous syntax falls back to full source."), ("Source context", "A header does not expand namespace variables, implicit instances, notation, imports, or local settings. Each statement therefore links to the complete exact module, with line anchors and an original source download."), ("Import relationships", "Direct imports are read from literal import commands. Reverse links cover all 366 proof modules and three aggregate entry points. No theorem-level dependency graph or per-declaration citation graph is claimed."), ("Search", "Search matches result names, paper labels, all 49 mapped declaration names, all 366 proof module names, and three aggregate entry points. It does not index every internal helper declaration."), ("Repository documents", "A small offline Markdown renderer displays committed prose. Exact Markdown files are available when typography or formula syntax needs checking."), ("Verification evidence", "The retained successful GitHub CI run certifies a full project-source rebuild and Lean audit at its recorded commit. Comparator execution and independent-kernel verification remain pending."), ("Offline use", "Open html/index.html directly after cloning, or visit the GitHub Pages site. Search data is a local JavaScript asset, so no server, CDN, telemetry, or network request is required to browse."), ("Licensing", "No blanket open-source license has been selected for project-owned code or the manuscript. Copyright and original third-party attribution are preserved.")]:
            content += '<tr><td>' + esc(label) + '</td><td>' + esc(text) + '</td></tr>'
        content += '</tbody></table><h2>Rebuild the documentation</h2><p>Python 3 is the only dependency. From the repository root:</p>' + command('python3 tools/docs-site/build.py\npython3 tools/docs-site/build.py --check')
        content += '<p>The freshness check compares generated bytes and validates every local file link, HTML anchor, search target, and source download. It is a documentation check; proof verification uses the separate commands on the verification page.</p><p>The generator records input hashes, counts, and extraction results in ' + self.link("generation.json", "generation.json", page) + '. There are no build timestamps or local absolute paths in the generated site.</p>'
        content += '<p>' + self.link("verify.html", "Proof verification", page) + ' · ' + self.link(self.doc_url("COPYRIGHT.md"), "Copyright", page) + ' · ' + self.link(self.doc_url("THIRD_PARTY_NOTICES.md"), "Third-party notices", page) + '</p>'
        self.page(page, "About", content, "About")

    def generate(self) -> None:
        self.emit(".nojekyll", b"")
        for name in ["site.css", "site.js"]:
            self.emit("assets/" + name, (TOOLS / name).read_bytes())
        self.build_overview()
        self.build_verify()
        self.build_route()
        self.build_results()
        self.build_modules()
        self.build_imports()
        self.build_docs()
        self.build_about()
        self.search.sort(key=lambda x: ("Proof module" in x["detail"], x["title"].lower()))
        self.emit("assets/search-data.js", '// ' + COPYRIGHT + '\nwindow.HOLEVO_SEARCH = ' + json.dumps(self.search, ensure_ascii=False, separators=(",", ":")) + ';\n')
        self.emit("generation.json", pretty({
            "schema_version": 1, "generator": "tools/docs-site/build.py", "site": SITE,
            "module_count": len(self.modules), "proof_module_count": 366, "aggregate_entry_points": 3, "correspondence_records": len(self.results),
            "mapped_declarations": len(self.headers), "literal_headers_quoted": sum(header is not None for header, line in self.headers.values()),
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
    for rel, data in site.outputs.items():
        if rel.endswith(".html"):
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
    print(("Site check passed" if args.check else "Site generated") + f': {len(site.outputs)} files, {metrics["module_count"]} project modules, {metrics["correspondence_records"]} result records, {metrics["mapped_declarations"]} mapped declarations, {metrics["literal_headers_quoted"]} exact headers, {metrics["search_entries"]} search entries.')
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
