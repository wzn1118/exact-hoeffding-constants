#!/usr/bin/env python3
"""Check the A:integration finite-law variance contract against Lean metadata.

This validates the exact A1 API boundary: the actual-law theorem signatures
contain no variance-positivity premise, their proof terms use the derived
endpoint-atom variance theorem, and the finite-law structure carries the
paper's endpoint assumptions. It does not claim to parse arbitrary TeX into
Lean propositions.
"""
from __future__ import annotations

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
VAR_POS = "ExactHoeffding.FiniteSupportLawData.variance_pos"
A1_CONTRACT = "ExactHoeffding.manuscript_A_integration_contract"
A1_CURVE_BRIDGE = "ExactHoeffding.finiteSupportLawData_toTiltCurve_of_endpoints"
A1_CONTRACT_COMPONENTS = (
    "ExactHoeffding.FiniteSupportLawData.rawLegendreRate_ge_meanEnvelopeRight",
    "ExactHoeffding.FiniteSupportLawData.rawLegendreRate_ge_meanEnvelopeLeft",
    "ExactHoeffding.FiniteSupportLawData.rawUpperTail_le_exp_neg_meanEnvelope",
    "ExactHoeffding.FiniteSupportLawData.rawLowerTail_le_exp_neg_meanEnvelope",
    "ExactHoeffding.FiniteSupportLawData.rawUpperTail_eq_sum",
    "ExactHoeffding.FiniteSupportLawData.rawLowerTail_eq_sum",
    "ExactHoeffding.FiniteSupportLawData.rawLegendreRate_gt_meanEnvelopeRight_of_interval",
    "ExactHoeffding.FiniteSupportLawData.rawLegendreRate_gt_meanEnvelopeLeft_of_interval",
    "ExactHoeffding.FiniteSupportLawData.rawLegendreRate_ge_meanEnvelopeRight_endpoint",
    "ExactHoeffding.FiniteSupportLawData.rawLegendreRate_ge_meanEnvelopeLeft_endpoint",
    "ExactHoeffding.FiniteSupportLawData.rawUpperTail_le_meanEnvelope_endpoint",
    "ExactHoeffding.FiniteSupportLawData.rawLowerTail_le_meanEnvelope_endpoint",
    "ExactHoeffding.FiniteSupportLawData.rawLegendreRate_gt_meanEnvelopeRight_endpoint_of_interval",
    "ExactHoeffding.FiniteSupportLawData.rawLegendreRate_gt_meanEnvelopeLeft_endpoint_of_interval",
)
A1_CORE = (
    "ExactHoeffding.FiniteSupportLawData.rawLegendreRate_ge_meanEnvelopeRight",
    "ExactHoeffding.FiniteSupportLawData.rawLegendreRate_ge_meanEnvelopeLeft",
    "ExactHoeffding.FiniteSupportLawData.rawLegendreRate_gt_meanEnvelopeRight",
    "ExactHoeffding.FiniteSupportLawData.rawLegendreRate_gt_meanEnvelopeLeft",
)
A1_REQUIRED_CONCLUSION_MARKERS = (
    "FiniteSupportLawData.variance",
    "FiniteSupportLawData.rawLegendreRate",
    "ContinuousOn",
    "Set.Ioo",
)
FINITE_LAW_FIELDS = (
    "support : Finset ι",
    "weight : ι → ℝ",
    "value : ι → ℝ",
    "weight_nonneg :",
    "weight_total :",
    "lo_hi_ne :",
    "lo_mem :",
    "hi_mem :",
    "lo_weight_pos :",
    "hi_weight_pos :",
    "lo_strict :",
    "hi_strict :",
)


def audit_contract(mapping: dict, manifest: dict, root: Path = ROOT) -> None:
    rows = {row["key"]: row for row in mapping["results"]}
    if "A:integration" not in rows:
        raise ValueError("missing A:integration manuscript row")
    a1_names = {"ExactHoeffding." + d["name"].removeprefix("ExactHoeffding.")
                for d in rows["A:integration"]["declarations"]}
    if rows["A:integration"].get("semantic_contract_declaration") != A1_CONTRACT:
        raise ValueError("A:integration is not bound to its typed Lean statement contract")
    if A1_CONTRACT not in a1_names:
        raise ValueError("A:integration contract declaration is absent from its result map")
    missing_a1 = set(A1_CORE) - a1_names
    if missing_a1:
        raise ValueError(f"A:integration omits actual-law rate theorems: {sorted(missing_a1)}")

    exported = {row["name"]: row for row in manifest["declarations"]}
    for decl in rows["A:integration"]["declarations"]:
        name = "ExactHoeffding." + decl["name"].removeprefix("ExactHoeffding.")
        theorem = exported.get(name)
        if theorem is None:
            raise ValueError(f"mapped A1 theorem absent from live Lean manifest: {name}")
        type_text = theorem["type_pretty"]
        if "hvar" in type_text or "hvariance" in type_text:
            raise ValueError(f"A1 map includes a theorem with a named premise for caller-supplied positive variance: {name}")
    for name in A1_CORE:
        if name not in exported:
            raise ValueError(f"A1 theorem absent from live Lean manifest: {name}")
        theorem = exported[name]
        type_text = theorem["type_pretty"]
        if "hvar" in type_text or "hvariance" in type_text:
            raise ValueError(f"A1 theorem exposes positive variance as a named premise: {name}")
        absent = [marker for marker in A1_REQUIRED_CONCLUSION_MARKERS
                  if marker not in type_text]
        if absent:
            raise ValueError(f"A1 theorem type lost expected actual-law terms {absent}: {name}")
        if VAR_POS not in theorem["proof_direct_dependencies"]:
            raise ValueError(f"A1 theorem no longer uses the derived variance proof: {name}")
        if name.endswith(("rawLegendreRate_ge_meanEnvelopeRight", "rawLegendreRate_ge_meanEnvelopeLeft")) and VAR_POS in theorem["type_dependencies"]:
            raise ValueError(f"non-strict A1 theorem unexpectedly exposes variance positivity in its type: {name}")
        bad_axioms = set(theorem["axioms"]) - ALLOWED_AXIOMS
        if bad_axioms:
            raise ValueError(f"A1 theorem has disallowed axioms {sorted(bad_axioms)}: {name}")

    contract = exported.get(A1_CONTRACT)
    if contract is None:
        raise ValueError("typed A:integration contract is absent from the live Lean manifest")
    contract_type = contract["type_pretty"]
    expected_type_parts = (
        "manuscriptA1RightVarianceGap", "manuscriptA1LeftVarianceGap",
        "FiniteSupportLawData.rawLegendreRate", "FiniteSupportLawData.rawUpperTail",
        "FiniteSupportLawData.rawLowerTail", "Filter.Tendsto",
    )
    absent_contract_parts = [part for part in expected_type_parts if part not in contract_type]
    if absent_contract_parts:
        raise ValueError(f"A:integration contract omits required clauses: {absent_contract_parts}")
    missing_components = set(A1_CONTRACT_COMPONENTS) - set(contract["proof_direct_dependencies"])
    if missing_components:
        raise ValueError(f"A:integration contract is not assembled from every required result: {sorted(missing_components)}")
    if set(contract["axioms"]) - ALLOWED_AXIOMS:
        raise ValueError("A:integration statement contract has disallowed axioms")

    mean_range_name = "ExactHoeffding.finiteSupportLawData_mean_mem_Ioo"
    mean_range = exported.get(mean_range_name)
    if mean_range is None:
        raise ValueError("endpoint-mass tilted-mean range lemma is absent from manifest")
    if not any(dep.endswith(".ExactHoeffding.law_mean_range")
               for dep in mean_range["proof_direct_dependencies"]):
        raise ValueError("tilted-mean interior theorem is not proved through the endpoint-range argument")

    # The range lemma delegates to a private proof helper. Check that helper's
    # actual source uses all endpoint and normalization fields, rather than
    # mistaking the wrapper's direct-dependency list for a transitive list.
    curve_source = (root / "ExactHoeffding/FiniteSupportTiltCurveOfLaw.lean").read_text(encoding="utf-8")
    helper_start = curve_source.find("private theorem law_mgf_pos")
    helper_end = curve_source.find("private theorem law_mean_atBot", helper_start)
    if helper_start < 0 or helper_end < 0:
        raise ValueError("endpoint-supported tilted-mean range proof helper is absent")
    helper = curve_source[helper_start:helper_end]
    required_endpoint_fields = (
        "lo_hi_ne", "lo_weight_pos", "hi_weight_pos", "lo_strict", "hi_strict",
        "weight_nonneg", "weight_total",
    )
    missing_endpoint_fields = [field for field in required_endpoint_fields if field not in helper]
    if missing_endpoint_fields:
        raise ValueError(f"tilted-mean range proof no longer uses the finite-law endpoint assumptions: {missing_endpoint_fields}")

    curve_bridge = exported.get(A1_CURVE_BRIDGE)
    if curve_bridge is None:
        raise ValueError("finite-law tilt-curve adapter is absent from manifest")
    if "hvar" in curve_bridge["type_pretty"] or "hvariance" in curve_bridge["type_pretty"]:
        raise ValueError("finite-law tilt-curve adapter still exposes positive variance as a caller premise")
    if VAR_POS not in curve_bridge["proof_direct_dependencies"]:
        raise ValueError("finite-law tilt-curve adapter does not derive positivity from FiniteSupportLawData")
    if set(curve_bridge["axioms"]) - ALLOWED_AXIOMS:
        raise ValueError("finite-law tilt-curve adapter has disallowed axioms")

    variance = exported.get(VAR_POS)
    if variance is None:
        raise ValueError("derived finite-law variance theorem is absent from manifest")
    if "FiniteSupportLawData.variance" not in variance["type_pretty"]:
        raise ValueError("derived variance theorem does not conclude positivity of the actual variance")
    if mean_range_name not in variance["proof_direct_dependencies"]:
        raise ValueError("derived variance theorem no longer uses the endpoint-supported interior tilted-mean proof")
    required_variance_fields = {
        "ExactHoeffding.FiniteSupportLawData.hi_mem",
        "ExactHoeffding.FiniteSupportLawData.hi_weight_pos",
        "ExactHoeffding.FiniteSupportLawData.weight_nonneg",
        "ExactHoeffding.FiniteSupportLawData.weight_total",
    }
    missing_variance_fields = required_variance_fields - set(variance["proof_direct_dependencies"])
    if missing_variance_fields:
        raise ValueError(f"strict variance proof lost its positive endpoint mass inputs: {sorted(missing_variance_fields)}")
    if set(variance["axioms"]) - ALLOWED_AXIOMS:
        raise ValueError("derived variance theorem has disallowed axioms")

    structure_file = root / "ExactHoeffding/FiniteSupportTiltCurveOfLaw.lean"
    source = structure_file.read_text(encoding="utf-8")
    start = source.find("structure FiniteSupportLawData")
    if start < 0:
        raise ValueError("FiniteSupportLawData structure is absent")
    block = source[start:source.find("\n\n", start)]
    absent_fields = [field for field in FINITE_LAW_FIELDS if field not in block]
    if absent_fields:
        raise ValueError(f"finite-law assumptions are missing from the structure: {absent_fields}")

    raw_def = (root / "ExactHoeffding/FiniteSupportLawCentering.lean").read_text(encoding="utf-8")
    for token in ("L.rawLogMGF", "sSup (Set.range", "finiteMGF L.support L.weight L.value t"):
        if token not in raw_def:
            raise ValueError(f"actual finite-law Legendre definition changed; missing {token!r}")


def main() -> int:
    mapping = json.loads((ROOT / "checks/manuscript_lean_map.json").read_text(encoding="utf-8"))
    manifest = json.loads((ROOT / "submission/current/theorem_lean_manifest.json").read_text(encoding="utf-8"))
    try:
        audit_contract(mapping, manifest)
    except (ValueError, KeyError, OSError) as error:
        print(f"FAIL: {error}")
        return 1
    print("PASS: A1 actual-law rate statements require no positive-variance premise; endpoint atom hypotheses yield variance_pos in the checked proof chain")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
