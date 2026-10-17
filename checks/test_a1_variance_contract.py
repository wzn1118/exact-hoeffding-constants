#!/usr/bin/env python3
"""Regression tests for the actual-law A1 variance-positivity contract."""
from __future__ import annotations

import copy
import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_a1_variance_contract import ROOT, audit_contract


class A1VarianceContractTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.mapping = json.loads((ROOT / "checks/manuscript_lean_map.json").read_text())
        cls.manifest = json.loads((ROOT / "submission/current/theorem_lean_manifest.json").read_text())

    def test_actual_law_api_derives_variance_positivity(self):
        audit_contract(self.mapping, self.manifest, ROOT)

    def test_rejects_explicit_positive_variance_premise(self):
        manifest = copy.deepcopy(self.manifest)
        row = next(d for d in manifest["declarations"] if d["name"].endswith("rawLegendreRate_ge_meanEnvelopeRight"))
        row["type_pretty"] += " (hvar : ∀ t, 0 < L.variance t)"
        with self.assertRaisesRegex(ValueError, "named premise"):
            audit_contract(self.mapping, manifest, ROOT)

    def test_rejects_missing_derived_variance_dependency(self):
        manifest = copy.deepcopy(self.manifest)
        row = next(d for d in manifest["declarations"] if d["name"].endswith("rawLegendreRate_ge_meanEnvelopeRight"))
        row["proof_direct_dependencies"].remove("ExactHoeffding.FiniteSupportLawData.variance_pos")
        with self.assertRaisesRegex(ValueError, "no longer uses the derived variance proof"):
            audit_contract(self.mapping, manifest, ROOT)

    def test_rejects_variance_proof_without_endpoint_mean_range(self):
        manifest = copy.deepcopy(self.manifest)
        row = next(d for d in manifest["declarations"] if d["name"].endswith("FiniteSupportLawData.variance_pos"))
        row["proof_direct_dependencies"].remove("ExactHoeffding.finiteSupportLawData_mean_mem_Ioo")
        with self.assertRaisesRegex(ValueError, "no longer uses the endpoint-supported"):
            audit_contract(self.mapping, manifest, ROOT)

    def test_rejects_missing_endpoint_mass_hypothesis(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "ExactHoeffding").mkdir()
            source = (ROOT / "ExactHoeffding/FiniteSupportTiltCurveOfLaw.lean").read_text()
            source = source.replace("  lo_weight_pos : 0 < weight loIndex\n", "")
            (root / "ExactHoeffding/FiniteSupportTiltCurveOfLaw.lean").write_text(source)
            (root / "ExactHoeffding/FiniteSupportLawCentering.lean").write_text(
                (ROOT / "ExactHoeffding/FiniteSupportLawCentering.lean").read_text())
            with self.assertRaisesRegex(ValueError, "finite-law assumptions"):
                audit_contract(self.mapping, self.manifest, root)


if __name__ == "__main__":
    unittest.main()
