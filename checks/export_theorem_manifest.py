#!/usr/bin/env python3
"""Export actual Lean theorem metadata and bind it to frozen paper/source bytes.

Default execution imports ExactHoeffding and reads every mapped declaration.
Rows may name a separate Lean proposition contract; the exporter verifies its
exact environment type and proof dependencies. Other rows receive source/type
integrity checks only and still need statement-level semantic review. Arbitrary
TeX is not parsed as Lean, and no proof is constructed or accepted here.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import shlex
import subprocess
import sys
import os
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
ENVIRONMENTS = re.compile(
    r"\\begin\{(theorem|lemma|proposition|corollary)\}"
    r"(?:\[(.*?)\])?(.*?)\\end\{\1\}", re.S
)
SCHEMA = 1


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def read_json(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def source_path(root: Path, relative: str) -> Path:
    path = (root / relative).resolve()
    if not path.is_relative_to(root.resolve()) or not path.is_file():
        raise ValueError(f"missing or out-of-repository source: {relative}")
    return path


def qualify(name: str) -> str:
    return name if name.startswith("ExactHoeffding.") else "ExactHoeffding." + name


def paper_locations(root: Path, mapping: dict) -> tuple[dict, list]:
    path = source_path(root, mapping["source"])
    data = path.read_bytes()
    source = data.decode("utf-8")
    environments = {}
    for match in ENVIRONMENTS.finditer(source):
        kind, title, body = match.groups()
        title = re.sub(r"\s+", " ", title or "").strip()
        label = re.search(r"\\label\{([^}]+)\}", body)
        key = label.group(1) if label else "unlabeled:" + title
        if key in environments:
            raise ValueError(f"duplicate manuscript result: {key}")
        environments[key] = {
            "key": key, "kind": kind, "title": title,
            "start_line": source.count("\n", 0, match.start()) + 1,
            "end_line": source.count("\n", 0, match.end()) + 1,
            "statement_source_sha256": sha(match.group(0).encode("utf-8")),
        }
    rows, seen = [], set()
    lines = source.splitlines(keepends=True)
    for row in mapping["results"]:
        key = row["key"]
        if key in seen:
            raise ValueError(f"duplicate map key: {key}")
        seen.add(key)
        if row.get("paper_environment", True):
            if key not in environments:
                raise ValueError(f"mapped manuscript environment absent: {key}")
            location = environments[key]
            for field in ("kind", "title"):
                if row[field] != location[field]:
                    raise ValueError(f"changed manuscript {field}: {key}")
            if row["line"] != location["start_line"]:
                raise ValueError(f"stale manuscript line for {key}: {row['line']} != {location['start_line']}")
        else:
            line = row["line"]
            if not 1 <= line <= len(lines):
                raise ValueError(f"invalid supplemental source line: {key}")
            location = {"key": key, "kind": row["kind"], "title": row["title"],
                        "start_line": line, "end_line": line,
                        "statement_source_sha256": sha(lines[line - 1].encode("utf-8"))}
        contract = row.get("semantic_contract_declaration")
        if contract is not None and contract.removeprefix("ExactHoeffding.") not in {
                d["name"].removeprefix("ExactHoeffding.") for d in row["declarations"]}:
            raise ValueError(f"semantic contract is not among mapped declarations: {key}")
        rows.append({**location, "paper_environment": row.get("paper_environment", True),
                     "mapped_status": row["status"],
                     "semantic_contract_declaration": qualify(contract) if contract else None,
                     "declarations": [qualify(d["name"]) for d in row["declarations"]]})
    actual = {row["key"] for row in mapping["results"] if row.get("paper_environment", True)}
    if actual != set(environments):
        raise ValueError(f"unmapped manuscript environments: {sorted(set(environments) - actual)}")
    return {"file": mapping["source"], "sha256": sha(data), "line_count": len(lines)}, rows


def lean_source_record(root: Path, relative: str, name: str, ranges: dict | None) -> dict:
    path = source_path(root, relative)
    data = path.read_bytes()
    source = data.decode("utf-8")
    from generate_axiom_audit import uncomment
    uncommented = uncomment(source)
    unqualified = name.removeprefix("ExactHoeffding.")
    # This source check binds the environment declaration to the named file;
    # theorem kind and actual type are independently read from Lean's environment.
    token = re.compile(r"\b(?:theorem|lemma)\s+" + re.escape(unqualified) + r"(?=[\s(:{\[])")
    matches = list(token.finditer(uncommented))
    if len(matches) != 1:
        raise ValueError(f"expected one source declaration for {name} in {relative}, got {len(matches)}")
    name_line = uncommented.count("\n", 0, matches[0].start()) + 1
    source_lines = source.splitlines(keepends=True)
    start = sum(len(line) for line in source_lines[:name_line - 1])
    if ranges is not None:
        start_line, end_line = ranges["start_line"], ranges["end_line"]
        if not start_line <= name_line <= end_line:
            raise ValueError(f"Lean source range does not contain {name}: {ranges}")
        lines = source.splitlines(keepends=True)
        if not 1 <= start_line <= end_line <= len(lines):
            raise ValueError(f"invalid Lean source range for {name}")
        declaration_bytes = "".join(lines[start_line - 1:end_line]).encode("utf-8")
        binding = "Lean declaration source range, complete intersecting lines"
    else:
        # Older/imported olean files can omit declaration-range metadata. Keep a
        # precise signature anchor plus the whole-file hash, never invent ranges.
        end = source.find(":=", matches[0].end())
        if end < 0:
            raise ValueError(f"missing theorem signature terminator for {name}")
        end += 2
        start_line, end_line = name_line, source.count("\n", 0, end) + 1
        declaration_bytes = source[start:end].encode("utf-8")
        binding = "source signature anchor; imported olean has no declaration range"
    return {"file": relative, "file_sha256": sha(data), "declaration_line": name_line,
            "start_line": start_line, "end_line": end_line,
            "declaration_source_sha256": sha(declaration_bytes), "source_binding": binding}


def requested_declarations(mapping: dict) -> dict[str, str]:
    requested = {}
    for row in mapping["results"]:
        for declaration in row["declarations"]:
            name, file = qualify(declaration["name"]), declaration["file"]
            if name in requested and requested[name] != file:
                raise ValueError(f"conflicting declaration files: {name}")
            requested[name] = file
    if not requested:
        raise ValueError("no mapped declarations")
    return requested


def inspect_lean(root: Path, names: list[str], imports: list[str], command: str,
                 timeout: int) -> dict:
    for module in imports:
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.]*", module):
            raise ValueError(f"invalid Lean import: {module}")
    helper = (ROOT / "checks/TheoremManifest.lean").read_text(encoding="utf-8")
    with tempfile.TemporaryDirectory(prefix="theorem-manifest-") as tmp:
        temporary = Path(tmp)
        output = temporary / "lean.json"
        generated = temporary / "Export.lean"
        array = "#[" + ", ".join(json.dumps(n, ensure_ascii=False) for n in names) + "]"
        code = "\n".join("import " + module for module in imports) + "\n" + helper
        code += "\nrun_meta ExactHoeffdingAudit.exportTheoremManifest " + array
        code += " " + json.dumps(str(output)) + "\n"
        generated.write_text(code, encoding="utf-8")
        result = subprocess.run(shlex.split(command) + ["-j1", str(generated)], cwd=root,
                                text=True, capture_output=True, timeout=timeout)
        if result.returncode:
            raise ValueError("Lean declaration export failed:\n" + result.stdout + result.stderr)
        if not output.is_file():
            raise ValueError("Lean did not produce the requested environment metadata")
        return read_json(output)


def exporter_hashes() -> dict:
    return {name: sha((ROOT / "checks" / name).read_bytes()) for name in
            ("TheoremManifest.lean", "export_theorem_manifest.py", "generate_axiom_audit.py")}


def assemble(root: Path, map_path: Path, mapping: dict, raw: dict,
             imports: list[str], selected: bool) -> dict:
    paper, results = paper_locations(root, mapping)
    requested = requested_declarations(mapping)
    declarations = []
    names = set()
    for row in raw["declarations"]:
        name = row["name"]
        if name in names or name not in requested:
            raise ValueError(f"unexpected or duplicate Lean declaration: {name}")
        names.add(name)
        if row["kind"] != "theorem":
            raise ValueError(f"mapped declaration is not a theorem: {name}")
        unexpected = set(row["axioms"]) - ALLOWED_AXIOMS
        if unexpected:
            raise ValueError(f"disallowed axioms for {name}: {sorted(unexpected)}")
        expected_module = requested[name].removesuffix(".lean").replace("/", ".")
        if row["module"] != expected_module:
            raise ValueError(f"Lean module mismatch for {name}: {row['module']} != {expected_module}")
        source = lean_source_record(root, requested[name], name, row["lean_source_range"])
        if "⋯" in row["type_pretty"]:
            raise ValueError(f"truncated Lean pretty-printed type: {name}")
        expression = row.pop("type_expression")
        row["type_expression_sha256"] = sha(expression.encode("utf-8"))
        row["type_pretty_sha256"] = sha(row["type_pretty"].encode("utf-8"))
        row["source"] = source
        row["inspected_declaration_sha256"] = sha(json.dumps(row, ensure_ascii=False,
            sort_keys=True, separators=(",", ":")).encode("utf-8"))
        declarations.append(row)
    if names != set(requested):
        raise ValueError(f"missing Lean export declarations: {sorted(set(requested) - names)}")
    return {"schema_version": SCHEMA, "exporter": exporter_hashes(),
            "scope": "selected-test" if selected else "full-manuscript-map",
            "semantic_correspondence": "Rows with semantic_contract_declaration carry a checked Lean proposition contract; other rows bind frozen paper text to inspected Lean types but still require statement-level semantic review.",
            "lean_version": raw["lean_version"],
            "toolchain": (root / "lean-toolchain").read_text().strip(),
            "imports": imports, "allowed_axioms": sorted(ALLOWED_AXIOMS),
            "map": {"file": str(map_path.relative_to(root)), "sha256": sha(map_path.read_bytes())},
            "manuscript": paper, "lean_package_manifest_sha256": sha((root / "lake-manifest.json").read_bytes()) if (root / "lake-manifest.json").is_file() else None,
            "results": results, "declarations": sorted(declarations, key=lambda item: item["name"])}


def check_frozen(root: Path, map_path: Path, manifest: dict, mapping: dict) -> None:
    if manifest["schema_version"] != SCHEMA:
        raise ValueError("unsupported manifest schema")
    if manifest.get("exporter") != exporter_hashes():
        raise ValueError("frozen manifest exporter or Lean inspection helper changed")
    if manifest["imports"] != ["ExactHoeffding"]:
        raise ValueError("full manifest must inspect import ExactHoeffding")
    if manifest["toolchain"] != (root / "lean-toolchain").read_text().strip():
        raise ValueError("frozen Lean toolchain changed")
    package_manifest = root / "lake-manifest.json"
    package_hash = sha(package_manifest.read_bytes()) if package_manifest.is_file() else None
    if manifest["lean_package_manifest_sha256"] != package_hash:
        raise ValueError("frozen Lean dependency manifest changed")
    if manifest["scope"] != "full-manuscript-map":
        raise ValueError("selected-test manifest cannot certify the full manuscript map")
    if manifest["map"] != {"file": str(map_path.relative_to(root)), "sha256": sha(map_path.read_bytes())}:
        raise ValueError("frozen declaration map changed")
    paper, results = paper_locations(root, mapping)
    if paper != manifest["manuscript"] or results != manifest["results"]:
        raise ValueError("frozen manuscript bytes, line locations, or result statements changed")
    requested = requested_declarations(mapping)
    actual = {row["name"] for row in manifest["declarations"]}
    if actual != set(requested) or len(actual) != len(manifest["declarations"]):
        raise ValueError("manifest declaration coverage mismatch")
    for row in manifest["declarations"]:
        name = row["name"]
        declaration = {key: value for key, value in row.items() if key != "inspected_declaration_sha256"}
        digest = sha(json.dumps(declaration, ensure_ascii=False,
            sort_keys=True, separators=(",", ":")).encode("utf-8"))
        if digest != row["inspected_declaration_sha256"]:
            raise ValueError(f"manifest inspected declaration checksum mismatch: {name}")
        source = lean_source_record(root, requested[name], name, row["lean_source_range"])
        if source != row["source"]:
            raise ValueError(f"frozen Lean source, declaration hash, or line changed: {name}")
        if row["kind"] != "theorem" or set(row["axioms"]) - ALLOWED_AXIOMS:
            raise ValueError(f"invalid theorem or axioms in manifest: {name}")
        if not row["type_pretty"] or not row["proof_direct_dependencies"]:
            raise ValueError(f"missing inspected type or proof metadata: {name}")
        expected_module = requested[name].removesuffix(".lean").replace("/", ".")
        if row["module"] != expected_module:
            raise ValueError(f"manifest module mismatch: {name}")
        if sha(row["type_pretty"].encode("utf-8")) != row["type_pretty_sha256"]:
            raise ValueError(f"manifest type text checksum mismatch: {name}")
    print(f"PASS: frozen source, locations, and hashes for {len(results)} results / {len(actual)} Lean theorems")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--map", type=Path, default=Path("checks/manuscript_lean_map.json"))
    parser.add_argument("--output", type=Path, default=Path("submission/current/theorem_lean_manifest.json"))
    parser.add_argument("--lean-command", default="lake env lean", help="Lean command; appends -j1 and generated file")
    parser.add_argument("--timeout", type=int, default=600)
    parser.add_argument("--import-module", action="append", help="test import override; default ExactHoeffding")
    parser.add_argument("--name", action="append", help="select names for a visibly partial test manifest")
    parser.add_argument("--check", action="store_true", help="check frozen source/map metadata without rerunning Lean")
    parser.add_argument("--check-live", action="store_true", help="also re-export Lean metadata and compare every field")
    args = parser.parse_args()
    root = args.root.resolve()
    map_path = args.map if args.map.is_absolute() else root / args.map
    output = args.output if args.output.is_absolute() else root / args.output
    try:
        mapping = read_json(map_path)
        if args.check or args.check_live:
            if args.name or args.import_module:
                raise ValueError("full frozen checks do not accept partial names or import overrides")
            existing = read_json(output)
            check_frozen(root, map_path, existing, mapping)
            if not args.check_live:
                return 0
        imports = args.import_module or ["ExactHoeffding"]
        if args.name:
            selected = {qualify(name) for name in args.name}
            available = requested_declarations(mapping)
            if selected - set(available):
                raise ValueError(f"unmapped test declarations: {sorted(selected - set(available))}")
            mapping = {**mapping, "results": [{**row, "declarations": [d for d in row["declarations"]
                        if qualify(d["name"]) in selected]} for row in mapping["results"]]}
        requested = requested_declarations(mapping)
        raw = inspect_lean(root, sorted(requested), imports, args.lean_command, args.timeout)
        document = assemble(root, map_path, mapping, raw, imports, bool(args.name))
        if args.check_live:
            if document != existing:
                raise ValueError("live Lean types, dependencies, axioms, or source metadata differ from frozen manifest")
            print("PASS: live Lean environment metadata matches the frozen manifest")
        else:
            output.parent.mkdir(parents=True, exist_ok=True)
            with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=output.parent, delete=False) as file:
                pending = Path(file.name)
                try:
                    file.write(json.dumps(document, ensure_ascii=False, indent=2) + "\n")
                    file.flush()
                    os.fsync(file.fileno())
                except BaseException:
                    pending.unlink(missing_ok=True)
                    raise
            try:
                pending.replace(output)
            finally:
                pending.unlink(missing_ok=True)
            print(f"PASS: exported {len(document['declarations'])} real Lean theorems to {output}")
            print(document["semantic_correspondence"])
        return 0
    except (ValueError, OSError, KeyError, subprocess.TimeoutExpired) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
