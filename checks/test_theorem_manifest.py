#!/usr/bin/env python3
"""Regression tests for source-freeze gates; real Lean is tested by the exporter."""
import contextlib
import copy
import io
import json
import tempfile
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import export_theorem_manifest as manifest


class FrozenBindings(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        (self.root / "submission/current").mkdir(parents=True)
        (self.root / "ExactHoeffding").mkdir()
        (self.root / "checks").mkdir()
        self.paper = self.root / "submission/current/manuscript.tex"
        self.paper.write_text("\\begin{theorem}[A test]\\label{test}\nTrue.\n\\end{theorem}\n")
        (self.root / "lean-toolchain").write_text("test-toolchain\n")
        self.lean = self.root / "ExactHoeffding/Test.lean"
        self.lean.write_text("namespace ExactHoeffding\ntheorem t : True := by trivial\nend ExactHoeffding\n")
        self.mapping = {"source": "submission/current/manuscript.tex", "results": [{
            "key": "test", "kind": "theorem", "title": "A test", "line": 1,
            "paper_environment": True, "status": "Complete", "declarations": [
                {"name": "t", "file": "ExactHoeffding/Test.lean"}]}]}
        self.map_path = self.root / "checks/manuscript_lean_map.json"
        self.map_path.write_text(json.dumps(self.mapping))
        # Fixture metadata tests only the byte/location gate, never proof validity.
        raw = {"lean_version": "fixture", "declarations": [{
            "name": "ExactHoeffding.t", "kind": "theorem", "module": "ExactHoeffding.Test",
            "universe_parameters": [], "type_pretty": "True", "type_expression": "fixture",
            "proof_expression_hash64": "0", "type_dependencies": ["True"],
            "proof_direct_dependencies": ["True.intro"], "axioms": [],
            "lean_source_range": {"start_line": 2, "start_column": 0,
                                  "end_line": 2, "end_column": 29}}]}
        self.document = manifest.assemble(self.root, self.map_path, self.mapping, raw,
                                          ["ExactHoeffding"], False)

    def check(self, document=None):
        with contextlib.redirect_stdout(io.StringIO()):
            manifest.check_frozen(self.root, self.map_path, document or self.document, self.mapping)

    def test_unchanged_bindings(self):
        self.check()

    def test_manuscript_byte_change(self):
        self.paper.write_text(self.paper.read_text() + "% modified\n")
        with self.assertRaisesRegex(ValueError, "frozen manuscript"):
            self.check()

    def test_declaration_proof_change(self):
        self.lean.write_text(self.lean.read_text().replace("by trivial", "True.intro"))
        with self.assertRaisesRegex(ValueError, "frozen Lean source"):
            self.check()

    def test_stale_location(self):
        self.mapping["results"][0]["line"] = 2
        with self.assertRaisesRegex(ValueError, "stale manuscript line"):
            manifest.paper_locations(self.root, self.mapping)

    def test_partial_is_not_full(self):
        document = copy.deepcopy(self.document)
        document["scope"] = "selected-test"
        with self.assertRaisesRegex(ValueError, "selected-test"):
            self.check(document)

    def test_type_corruption(self):
        document = copy.deepcopy(self.document)
        document["declarations"][0]["type_pretty"] = "False"
        with self.assertRaisesRegex(ValueError, "inspected declaration checksum"):
            self.check(document)


if __name__ == "__main__":
    unittest.main()
