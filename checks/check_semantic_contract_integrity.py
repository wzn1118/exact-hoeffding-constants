#!/usr/bin/env python3
"""Audit typed theorem contracts and paper/Lean byte-level correspondence.

This checker verifies frozen paper statements and display formulas against their
SHA-256 records, validates manifest declaration/type fingerprints, checks that
Complete rows name a typed Lean contract, and applies a small, reviewed set of
required type-component markers.  It cannot prove that a TeX statement and a
Lean proposition are semantically equivalent; that translation still requires
mathematical review.  ``--live`` additionally asks Lean to re-export the mapped
declarations and compare the live environment to the frozen manifest.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
DISPLAY_PATTERN = re.compile(
    r"\\begin\{(equation\*?|align\*?|gather\*?|multline\*?)\}(.*?)\\end\{\1\}|\\\[(.*?)\\\]",
    re.S,
)

# These are explicit structural checks on the current Lean encodings, not a
# claim that token presence establishes equivalence.  Expand only after review
# against the corresponding TeX proposition and Lean declaration.
REQUIRED_TYPE_MARKERS: dict[str, tuple[str, ...]] = {
    "manuscript_exchangeability_constants_contract": (
        "exactExchangeableConstant", "manuscriptExchangeabilityConstantFormula",
        "IsExchangeableCoefficient", "IsLeast", "normalizedHypergeomProxy",
        "Real.artanh", "Tendsto",
    ),
    "manuscript_main_laplace_contract": (
        "hypergeomCenteredLogMGF", "hypergeomOptimalProxy", "bernoulliSharpBeta",
        "envelopeM", "envelopeScale", "scaledBernoulliLogLaplace",
    ),
    "manuscript_thm_curvature_contract": ("hypergeomTiltVariance",),
    "manuscript_cor_mgf_contract": ("hypergeomCenteredLogMGF", "hypergeomOptimalProxy"),
    "manuscript_cor_tail_contract": (
        "IsProbabilityMeasure", "FiniteExchangeableMeasure", "realCube",
        "manuscriptTailStatistic", "projectedWeightVariance", "Real.exp", "log", "sqrt",
    ),
    "manuscript_variational_full_contract": (
        "exactExchangeableConstant", "manuscriptVariationalMaximum",
        "IsExchangeableCoefficient", "Iff",
    ),
    "manuscript_A_integration_contract": (
        "FiniteSupportLawData", "manuscriptA1RightVarianceGap",
        "manuscriptA1LeftVarianceGap", "FiniteSupportLawData.rawLegendreRate",
        "FiniteSupportLawData.rawUpperTail", "FiniteSupportLawData.rawLowerTail",
    ),
    "manuscript_integer_two_sided_contract": (
        "canonicalPiecewiseRate", "hypergeomUpperDeviationMass",
        "hypergeomLowerDeviationMass", "hypergeomTwoSidedDeviationMass",
    ),
    "manuscript_A3_four_symmetric_binomial_KL_contract": (
        "fourBinomialKLRate2", "fourBinomialKLRate3", "fourBinomialKLRate4",
        "fourBinomialKLRateMax", "binomialKLRate", "binomialKLSlope",
        "fourBinomialKLRate2Slope", "fourBinomialKLRate3Slope",
        "fourBinomialKLRate4Slope",
    ),
    "manuscript_A4_exact_variance_bennett_bernstein_contract": (
        "hypergeomBennettRate", "hypergeomBernsteinRate", "hypergeomTiltVariance",
        "canonicalPiecewiseRate",
    ),
    "manuscript_A_factorial_full_contract": (
        "finiteIntegerTailMass", "finiteFactorialBound", "sInf",
        "hypergeomMass", "hypergeomKLRate", "canonicalPiecewiseRate",
    ),
    "manuscript_extra_A2_factorial_index_contract": (
        "hypergeomFactorialIndex",
    ),
    "manuscript_A_piecewise_contract": (
        "canonicalPiecewiseRate", "scaledKLRate", "hypergeomKLRate",
        "Real.exp",
    ),
    "manuscript_extra_A_piecewise_C2_contract": (
        "canonicalPiecewiseRate", "ContDiffOn", "deriv",
    ),
    "manuscript_integer_two_sided_contract": (
        "canonicalPiecewiseRate", "hypergeomUpperDeviationMass",
        "hypergeomLowerDeviationMass", "hypergeomTwoSidedDeviationMass",
    ),

    # The following profiles were individually checked against the frozen
    # manuscript environments and the corresponding aggregate contract types.
    # They deliberately use symbols present in the proposition type; proof
    # helper names remain in REQUIRED_PROOF_DEPENDENCIES below.
    "manuscript_main_laplace_full_contract": (
        "hypergeomCenteredLogMGF", "scaledBernoulliLogLaplace", "envelopeM",
        "envelopeScale", "hypergeomOptimalProxy", "bernoulliSharpBeta",
        "normalizedHypergeomProxy",
    ),
    "manuscript_prop_two_level_contract": (
        "sliceExponential", "Finset.image", "Finset.card",
    ),
    "manuscript_lem_PB_contract": (
        "hypergeomMGF", "hypergeomTiltMean", "hypergeomTiltVariance",
        "independentBernoulliMeasure",
    ),
    "manuscript_lem_branch_contract": (
        "stationaryPolynomial", "stationaryDen",
    ),
    "manuscript_extra_stationary_q0_radicals_contract": (
        "stationaryQZero",
    ),
    "manuscript_lem_universal_contract": ("sqrt", "abs"),
    "manuscript_lem_identity_contract": ("stationaryPolynomial",),
    "manuscript_prop_allinner_contract": (
        "hypergeomTiltVariance", "SupSet.sSup",
    ),
    "manuscript_prop_variance_parity_full_contract": (
        "exactExchangeableVarianceConstant", "parityVarianceConstant",
        "exactExchangeableConstant", "Even", "intervalIntegral",
    ),
    "manuscript_prop_explicit_extremizer_contract": (
        "uniformHammingMeasure", "FiniteExchangeableMeasure",
        "singleCoordinateContrast", "singleCoordinateBernoulli",
        "paritySharpConstant", "Tendsto",
    ),
    "manuscript_lem_threemass_contract": (
        "IsOptimalQuadraticProxy", "threeMassCenteredLog",
    ),
    "manuscript_prop_odd2_semantic_contract": (
        "manuscriptPropOdd2FiniteStatement", "manuscriptPropOdd2GapStatement",
    ),
    "manuscript_cor_two_bern_envelope_contract": (
        "hypergeomOptimalProxy", "bernoulliSharpBeta", "Real.instLT",
    ),
    "manuscript_odd_envelope_full_contract": (
        "hypergeomCenteredLogMGF", "scaledBernoulliLogLaplace", "envelopeM",
        "envelopeScale", "hypergeomOptimalProxy", "bernoulliSharpBeta",
        "imbalanceFactor", "oddHypergeomConstant",
    ),
    "manuscript_extra_Bernoulli_gap_display_identities_contract": (
        "bernoulliProxyGap", "bernoulliSharpBeta", "deriv", "Real.log",
    ),
    "manuscript_odd_lem_PB_full_contract": (
        "hypergeomTiltMeasure", "independentBernoulliMeasure",
        "hypergeomTiltMean", "hypergeomTiltVariance",
        "manuscriptHypergeomVarianceAtMean",
    ),
    "manuscript_odd_lem_ode_mean_contract": (
        "meanCurveHypergeomVarianceAtMean", "riccatiF", "deriv",
    ),
    "manuscript_odd_lem_barrier_mean_contract": (
        "meanCurveHypergeomVarianceAtMean", "varianceBarrier",
    ),
    "manuscript_odd_global_extremizer_contract": (
        "normalizedHypergeomProxy", "hypergeomVariationalConstant",
        "exactExchangeableConstant", "IsLeast", "Real.artanh",
    ),
    "manuscript_extra_B2_odd_central_full_contract": (
        "hypergeomCenteredLogMGF", "oddCentralSupportedTiltSum",
        "oddCentralSupportedProxy", "hypergeomOptimalProxy", "deriv",
    ),
    "manuscript_B_inputs_contract": (
        "hypergeomTiltVariance", "sharpCurvatureConstant",
        "hypergeomOptimalProxy", "envelopeM", "bernoulliSharpBeta",
    ),
    "manuscript_B_main_contract": (
        "hypergeomOptimalProxy", "individualMarginDelta",
        "individualMarginGap", "individualMarginW", "Iff",
    ),
    "manuscript_B_atanh_contract": ("Real.artanh", "Real.instLT"),
    "manuscript_B_individual_contract": (
        "hypergeomOptimalProxy", "individualMarginDelta",
        "individualMarginGap", "individualMarginW",
    ),
    "manuscript_extra_B1_individual_margin_contract": (
        "hypergeomOptimalProxy", "individualMarginDelta",
        "individualMarginGap", "individualMarginW",
    ),
    "manuscript_B_even_contract": (
        "hypergeomOptimalProxy", "hypergeomTiltVariance", "Iff",
    ),
    "manuscript_B_odd_contract": (
        "actualHypergeomProxy", "hypergeomCenteredLogMGF",
        "hypergeomCumulant2", "oddCentralSupportedProxy",
    ),
    "manuscript_B_small_contract": (
        "hypergeomOptimalProxy", "Real.log", "Iff",
    ),
    "manuscript_extra_A_Legendre_derivatives_full_contract": (
        "FiniteSupportLawData", "rawMeanInverse", "rawLegendreRate",
        "HasDerivAt", "deriv",
    ),
    "manuscript_extra_A_quadratic_chain_contract": (
        "canonicalPiecewiseRate", "scaledKLRate",
        "hypergeomUniformQuadraticVariance", "envelopeM", "envelopeScale",
    ),
    "manuscript_extra_A_scaled_rate_Taylor_contract": (
        "scaledKLRate", "AnalyticAt", "iteratedDeriv",
        "Asymptotics.IsBigO",
    ),
    "manuscript_thm_odd_expansion_contract": (
        "actualHypergeomProxy", "fixedImbalanceProxyTaylor4",
        "fixedImbalanceTiltTaylor3", "rescaledProxyExtension",
        "Asymptotics.IsBigO",
    ),
    "manuscript_cor_fixedm_gap_full_contract": (
        "oddHypergeomConstant", "normalizedHypergeomProxy",
        "Asymptotics.IsBigO", "Tendsto",
    ),
    "manuscript_extra_appendix_cumulant23_remainders_contract": (
        "hypergeomCumulant2", "hypergeomCumulant3",
        "hypergeomCumulant2Taylor", "hypergeomCumulant3Taylor",
        "realMarginMass", "scaledFalling", "Asymptotics.IsBigO",
    ),
    "manuscript_extra_appendix_proxy_uniform_Taylor_contract": (
        "rescaledProxyExtension", "hypergeomRescaledCumulant2",
        "hypergeomRescaledCumulant3", "hypergeomRescaledCumulant4",
        "hypergeomRescaledCumulant5", "hypergeomRescaledCumulant6",
        "Continuous",
    ),
}


# Proof-use checks are kept separate from proposition-shape checks.  These
# names occur in the kernel-checked proof dependency list, not necessarily in
# the pretty-printed proposition type (for example, an endpoint theorem may
# prove a conclusion without appearing in that conclusion's type).
REQUIRED_PROOF_DEPENDENCIES: dict[str, tuple[str, ...]] = {
    "manuscript_A_integration_contract": (
        "FiniteSupportLawData.variance_pos",
        "rawLegendreRate_gt_meanEnvelopeRight_endpoint_of_interval",
        "rawLegendreRate_gt_meanEnvelopeLeft_endpoint_of_interval",
    ),
    "manuscript_A_factorial_full_contract": (
        "Nat.descFactorial",
        "finiteFactorialBound_le_chernoff_inf",
        "hypergeomFactorialBound_lt_exp_neg_piecewiseRate",
    ),
    "manuscript_extra_A2_factorial_index_contract": (
        "hypergeomFactorialValue_index_min",
        "hypergeomFactorialBound_eq_ceiling_candidate",
    ),
}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_digest(value: Any) -> str:
    return sha(json.dumps(value, ensure_ascii=False, sort_keys=True,
                          separators=(",", ":")).encode("utf-8"))


def type_fingerprint(record: dict[str, Any]) -> str:
    """Return stable fingerprint over the inspected Lean type and audit fields."""
    keys = (
        "name", "module", "kind", "universe_parameters", "type_expression_sha256",
        "type_pretty_sha256", "type_dependencies", "proof_direct_dependencies", "axioms",
    )
    return canonical_digest({key: record.get(key) for key in keys})


def proof_dependency_closure(
    contract: dict[str, Any], declarations: dict[str, dict[str, Any]],
) -> set[str]:
    """Return the transitive proof-constant closure recorded by Lean export."""
    seen: set[str] = set()
    pending = list(contract.get("proof_direct_dependencies", []))
    while pending:
        name = pending.pop()
        if name in seen:
            continue
        seen.add(name)
        dependency = declarations.get(name)
        if dependency is not None:
            pending.extend(dependency.get("proof_direct_dependencies", []))
    return seen


def check_fingerprint(record: dict[str, Any]) -> None:
    pretty = record.get("type_pretty")
    if not isinstance(pretty, str) or not pretty:
        raise ValueError(f"missing pretty type for {record.get('name')}")
    if sha(pretty.encode("utf-8")) != record.get("type_pretty_sha256"):
        raise ValueError(f"Lean type pretty-print fingerprint mismatch: {record.get('name')}")
    expr_hash = record.get("type_expression_sha256")
    if not isinstance(expr_hash, str) or not re.fullmatch(r"[0-9a-f]{64}", expr_hash):
        raise ValueError(f"missing Lean expression hash: {record.get('name')}")
    declared = record.get("inspected_declaration_sha256")
    payload = {key: value for key, value in record.items()
               if key != "inspected_declaration_sha256"}
    if canonical_digest(payload) != declared:
        raise ValueError(f"inspected declaration fingerprint mismatch: {record.get('name')}")


def check_display_inventory(root: Path) -> int:
    source_path = root / "submission/current/manuscript.tex"
    inventory_path = root / "submission/current/display_formula_inventory.json"
    source_bytes = source_path.read_bytes()
    source = source_bytes.decode("utf-8")
    inventory = json.loads(inventory_path.read_text(encoding="utf-8"))
    if inventory.get("source") != "submission/current/manuscript.tex":
        raise ValueError("display inventory names a different manuscript")
    if inventory.get("source_sha256") != sha(source_bytes):
        raise ValueError("display inventory manuscript SHA-256 is stale")
    expected = []
    for index, match in enumerate(DISPLAY_PATTERN.finditer(source), 1):
        block = match.group()
        line = source.count("\n", 0, match.start()) + 1
        expected.append({
            "id": f"D{index}",
            "start_line": line,
            "end_line": source.count("\n", 0, match.end()) + 1,
            "environment": match.group(1) or "displaymath",
            "labels": re.findall(r"\\label\{([^}]+)\}", block),
            "tex": block,
            "sha256": sha(block.encode("utf-8")),
            "scope_review": "formal_status/display_formula_audit_current_20261018.md",
        })
    rows = inventory.get("displays")
    if inventory.get("display_count") != len(expected):
        raise ValueError("display inventory display_count is stale")
    if not isinstance(rows, list) or len(rows) != len(expected):
        raise ValueError("display inventory count differs from manuscript")
    fields = ("id", "start_line", "end_line", "environment", "labels", "tex", "sha256",
              "scope_review")
    for actual, wanted in zip(rows, expected):
        if any(actual.get(field) != wanted[field] for field in fields):
            raise ValueError(f"stale or altered display formula inventory row {wanted['id']}")
        if not (root / wanted["scope_review"]).is_file():
            raise ValueError(f"missing scope review for display formula {wanted['id']}")
    return len(expected)


def qualify(name: str) -> str:
    return name if name.startswith("ExactHoeffding.") else "ExactHoeffding." + name


def audit(root: Path, require_contracts: bool = False) -> tuple[list[str], dict[str, int]]:
    # Import canonical parser/checker so the paper statement digest has exactly
    # the same environment boundaries as the exporter used by the repo.
    sys.path.insert(0, str(root / "checks"))
    import export_theorem_manifest as exporter  # type: ignore
    exporter.ROOT = root
    from check_a1_variance_contract import audit_contract as audit_a1_variance_contract  # type: ignore

    map_path = root / "checks/manuscript_lean_map.json"
    manifest_path = root / "submission/current/theorem_lean_manifest.json"
    mapping = json.loads(map_path.read_text(encoding="utf-8"))
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    exporter.check_frozen(root, map_path, manifest, mapping)
    audit_a1_variance_contract(mapping, manifest, root)

    inventory_count = check_display_inventory(root)
    declaration_records = {d["name"]: d for d in manifest["declarations"]}
    if len(declaration_records) != len(manifest["declarations"]):
        raise ValueError("duplicate declaration in theorem manifest")
    for record in declaration_records.values():
        check_fingerprint(record)
        if record.get("kind") != "theorem":
            raise ValueError(f"mapped object is not a theorem: {record.get('name')}")
        unexpected = set(record.get("axioms", [])) - ALLOWED_AXIOMS
        if unexpected:
            raise ValueError(f"disallowed axioms in {record.get('name')}: {sorted(unexpected)}")

    mapped_results = {row["key"]: row for row in manifest["results"]}
    if len(mapped_results) != len(manifest["results"]):
        raise ValueError("duplicate result in theorem manifest")
    if set(mapped_results) != {row["key"] for row in mapping["results"]}:
        raise ValueError("map and theorem manifest result keys differ")

    errors: list[str] = []
    warnings: list[str] = []
    complete = typed = marked = 0
    fingerprint_set = set()
    for row in mapping["results"]:
        key = row["key"]
        frozen_row = mapped_results[key]
        if frozen_row.get("mapped_status") != row.get("status"):
            errors.append(f"{key}: mapped status differs from manifest")
        contract = row.get("semantic_contract_declaration")
        if row.get("status") == "Complete":
            complete += 1
            if not contract:
                warnings.append(f"{key}: Complete row has no standalone typed contract")
                continue
        if not contract:
            continue
        typed += 1
        fq_contract = qualify(contract)
        if frozen_row.get("semantic_contract_declaration") != fq_contract:
            errors.append(f"{key}: contract differs between map and frozen manifest")
            continue
        decl_names = {qualify(d["name"]) for d in row.get("declarations", [])}
        if fq_contract not in decl_names:
            errors.append(f"{key}: contract is not in its mapped declaration set")
            continue
        contract_record = declaration_records.get(fq_contract)
        if contract_record is None:
            errors.append(f"{key}: contract missing from inspected Lean environment")
            continue
        fingerprint_set.add(type_fingerprint(contract_record))
        forbidden = set(contract_record.get("axioms", [])) - ALLOWED_AXIOMS
        if forbidden:
            errors.append(f"{key}: contract has disallowed axioms {sorted(forbidden)}")
        # A proposition-level contract may inline the argument or depend on a
        # shared helper outside this row. Direct-dependency overlap is not a
        # semantic condition; source/type fingerprints and the axiom audit are.
        unqualified = fq_contract.removeprefix("ExactHoeffding.")
        markers = REQUIRED_TYPE_MARKERS.get(unqualified)
        if markers is None:
            warnings.append(f"{key}: no reviewed required-marker rule for {unqualified}")
        else:
            missing = [marker for marker in markers if marker not in contract_record["type_pretty"]]
            if missing:
                errors.append(f"{key}: Lean contract type is missing markers {missing}")
            else:
                marked += 1
        required_deps = REQUIRED_PROOF_DEPENDENCIES.get(unqualified, ())
        if required_deps:
            proof_deps = proof_dependency_closure(contract_record, declaration_records)
            missing_deps = [
                marker for marker in required_deps
                if not any(marker in dependency for dependency in proof_deps)
            ]
            if missing_deps:
                errors.append(f"{key}: kernel proof dependency list is missing {missing_deps}")

    if require_contracts:
        for warning in warnings:
            if "no standalone typed contract" in warning:
                errors.append(warning)
        uncovered_markers = [w for w in warnings if "no reviewed required-marker rule" in w]
        errors.extend(uncovered_markers)

    stats = {
        "paper_rows": len(mapping["results"]),
        "complete_rows": complete,
        "typed_contracts": typed,
        "marker_checked_contracts": marked,
        "unique_type_fingerprints": len(fingerprint_set),
        "display_formulas": inventory_count,
    }
    return errors + ["OPEN: " + warning for warning in warnings], stats


def self_test() -> None:
    sample = {
        "name": "ExactHoeffding.sample", "module": "ExactHoeffding.Sample", "kind": "theorem",
        "universe_parameters": [], "type_expression_sha256": "a" * 64,
        "type_pretty": "A → B", "type_dependencies": ["A", "B"],
        "proof_direct_dependencies": ["ExactHoeffding.base"], "axioms": [],
    }
    sample["type_pretty_sha256"] = sha(sample["type_pretty"].encode())
    sample["inspected_declaration_sha256"] = canonical_digest(sample)
    check_fingerprint(sample)
    original = type_fingerprint(sample)
    changed = dict(sample, type_pretty="A → C")
    changed["type_pretty_sha256"] = sha(changed["type_pretty"].encode())
    changed_payload = {k: v for k, v in changed.items() if k != "inspected_declaration_sha256"}
    changed["inspected_declaration_sha256"] = canonical_digest(changed_payload)
    assert type_fingerprint(changed) != original
    try:
        broken = dict(sample, type_pretty_sha256="0" * 64)
        check_fingerprint(broken)
    except ValueError:
        pass
    else:
        raise AssertionError("type pretty hash tampering was not detected")
    assert REQUIRED_TYPE_MARKERS["manuscript_cor_mgf_contract"] == (
        "hypergeomCenteredLogMGF", "hypergeomOptimalProxy")
    print("PASS: semantic-contract checker self-tests (fingerprint change/tamper, marker registry)")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--require-contracts", action="store_true",
                        help="fail when any Complete row lacks a typed contract or reviewed markers")
    parser.add_argument("--live", action="store_true",
                        help="re-export every mapped Lean declaration with the canonical exporter")
    parser.add_argument("--lean-command", default="lake env lean")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return 0
    root = args.root.resolve()
    try:
        open_notes, stats = audit(root, args.require_contracts)
        failures = [note for note in open_notes if not note.startswith("OPEN: ")]
        if failures:
            raise ValueError("\n".join(failures))
        if args.live:
            proc = subprocess.run(
                [sys.executable, str(root / "checks/export_theorem_manifest.py"),
                 "--root", str(root), "--check-live", "--lean-command", args.lean_command],
                cwd=root, text=True, capture_output=True, check=False,
            )
            if proc.returncode:
                raise ValueError("live Lean environment check failed:\n" + proc.stdout + proc.stderr)
            print(proc.stdout.rstrip())
        print("PASS: frozen statement SHA-256, Lean source/type fingerprints, permitted axiom set, and display inventory are internally consistent")
        print("COUNTS: " + json.dumps(stats, sort_keys=True))
        for note in open_notes:
            print(note)
        print("LIMIT: source/type hashes and required-token markers establish byte identity and selected structural features only; they do not prove TeX-to-Lean semantic equivalence. Each translation still needs mathematical review.")
        return 0
    except (ValueError, OSError, KeyError, json.JSONDecodeError, subprocess.SubprocessError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
