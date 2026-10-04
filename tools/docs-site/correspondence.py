# Copyright (c) 2026 the Nonadditivity project contributors.
# All rights reserved. See COPYRIGHT.md for licensing and attribution.
"""Locate labels in this release's revised LaTeX manuscript.

Only section and shared theorem numbering are exposed. Equation numbers are
deliberately omitted: their LaTeX counters depend on display-environment rules.
The source line and label remain authoritative for every location.
"""
from __future__ import annotations

import re


def manuscript_locations(source: str) -> dict[str, dict]:
    masked = re.sub(r"(?<!\\)%[^\n]*", lambda m: " " * len(m.group()), source)
    token = re.compile(
        r"\\appendix\b|"
        r"\\(?P<section>section|subsection)\{(?P<title>[^{}]*)\}|"
        r"\\begin\{(?P<begin>theorem|lemma|proposition|corollary|remark\*?|equation\*?|align\*?|proof)\}|"
        r"\\end\{(?P<end>theorem|lemma|proposition|corollary|remark\*?|equation\*?|align\*?|proof)\}|"
        r"\\label\{(?P<label>[^{}]+)\}"
    )
    locations = {}
    section = None
    subsection = None
    section_count = subsection_count = theorem_count = 0
    appendix = False
    environments = []
    for match in token.finditer(masked):
        line = source.count("\n", 0, match.start()) + 1
        if match.group() == r"\appendix":
            appendix = True
            section_count = 0
        elif match.group("section"):
            if match.group("section") == "section":
                section_count += 1
                subsection_count = theorem_count = 0
                number = chr(64 + section_count) if appendix else str(section_count)
                section = {"number": number, "title": match.group("title"), "line": line}
                subsection = None
            else:
                if section is None:
                    raise ValueError("Manuscript subsection has no enclosing section")
                subsection_count += 1
                subsection = {"number": section["number"] + "." + str(subsection_count),
                              "title": match.group("title"), "line": line}
        elif match.group("begin"):
            kind = match.group("begin")
            number = None
            if kind in {"theorem", "lemma", "proposition", "corollary", "remark"}:
                if section is None:
                    raise ValueError("Numbered manuscript statement has no section")
                theorem_count += 1
                number = section["number"] + "." + str(theorem_count)
            environments.append({"kind": kind, "number": number, "line": line})
        elif match.group("end"):
            if not environments or environments[-1]["kind"] != match.group("end"):
                raise ValueError("Unbalanced tracked manuscript environment at line " + str(line))
            environments.pop()
        else:
            label = match.group("label")
            if label in locations:
                raise ValueError("Duplicate manuscript label: " + label)
            environment = environments[-1] if environments else None
            record = {"label": label, "line": line, "section": section,
                      "subsection": subsection, "kind": "passage", "number": None}
            if label.startswith(("sec:", "app:")):
                heading = subsection or section
                if heading:
                    record.update(kind="section", number=heading["number"],
                                  title=heading["title"], line=heading["line"])
            elif environment:
                record.update(kind=environment["kind"], number=environment["number"])
                if environment["number"]:
                    record["line"] = environment["line"]
            locations[label] = record
    if environments:
        raise ValueError("Unclosed tracked manuscript environment")
    return locations


def validate_correspondence(data: dict, results: list[dict], locations: dict,
                            reader: dict) -> None:
    if data.get("schema_version") != 1:
        raise ValueError("Unsupported manuscript correspondence schema")
    entries = data["entries"]
    if [entry["result_id"] for entry in entries] != [result["id"] for result in results]:
        raise ValueError("Manuscript correspondence must cover each result once in catalog order")
    reader_ids = {group: {item["id"] for item in reader[group]}
                  for group in ("guides", "concepts", "stages")}
    for entry, result in zip(entries, results):
        if entry["statement_label"] not in result["paper"]["labels"]:
            raise ValueError("Primary manuscript label is not in result metadata: " + result["id"])
        for label in [entry["statement_label"], *result["paper"]["labels"],
                      *(item["label"] for item in entry["argument_labels"])]:
            if label not in locations:
                raise ValueError("Unknown manuscript correspondence label: " + label)
        for group, valid_ids in reader_ids.items():
            if len(set(entry[group])) != len(entry[group]) or not set(entry[group]) <= valid_ids:
                raise ValueError("Invalid correspondence reader links for " + result["id"])
        if not entry["statement_caption"].strip() or not entry["argument_labels"]:
            raise ValueError("Incomplete manuscript correspondence entry: " + result["id"])
