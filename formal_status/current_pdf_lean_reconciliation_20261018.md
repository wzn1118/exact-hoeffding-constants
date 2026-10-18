# Current PDF–Lean reconciliation — 18 October 2026

The canonical paper for this audit is the byte-identical source published on GitHub `main` at commit `91719272750df6103358d8daccc4de8526a0d101` (17 October 2026). The checked files are:

- `submission/current/manuscript.tex`: SHA-256 `617cce1f87272bd5d5d58e3d91342bba658bb490cb901643fb9436ecc6e2894b`;
- `submission/current/manuscript.pdf`: SHA-256 `df93908f10e3398066a3ceb5283aeccdf961b86913bbe7bd5a5e82b68897797c`.

The theorem map and live manifest bind this source to 49 rows: 35 theorem-class environments and 14 supplementary claims. Every row is marked `Complete`, has an explicit typed Lean contract, and is bound to the current source hash. The manifest contains 394 distinct mapped Lean theorem declarations and 240 inventoried display blocks. The concordance is regenerated at `submission/current/theorem_lean_concordance.md`.

## Results that remain reusable

- **`prop:odd2`.** The finite odd two-draw maximum covers every legal `0 ≤ k ≤ N`, both central equality cases, the zero boundary cases, the closed two-draw constant, and strict singleton comparison. The same mapped package proves the stated
  `L_N - L_N^(2) = 2/(3N^3) + O(N^-4)` expansion. The finite and asymptotic propositions are assembled by `manuscript_prop_odd2_semantic_contract` and `manuscript_prop_odd2_gap_asymptotic_contract` in `ExactHoeffding/ManuscriptTwoDrawContract.lean`.

- **`A:factorial`.** The corrected manuscript scope is now the one used by the Lean contract: positive denominator identities require `1 ≤ d ≤ min(k,m)` and `0 ≤ j ≤ d`; the strict supported comparison is stated for `μ < d ≤ m`; the exterior branch `d > m` is separately zero. The reflected lower-tail chain and the ceiling-index supplement are included. Earlier mappings that treated the quotient or strict comparison as unrestricted are obsolete; the corrected aggregate contract is `manuscript_A_factorial_full_contract` in `ExactHoeffding/ManuscriptA2Contract.lean`.

- **`cor:fixedm_gap`.** The fixed `m` central fourth-order expansion, the off-balance expansion for fixed `s ≥ 3`, and eventual strict separation are assembled in `manuscript_cor_fixedm_gap_full_contract` in `ExactHoeffding/ManuscriptSemanticAggregates.lean`. The sequence formulation is the exact Lean form of the fixed-parameter asymptotic statement.

- **A1, A3, A4, integer thresholds, the main Laplace theorem, the curvature theorem, the exchangeability identity, and the weighted tail corollary.** Their current typed contracts remain attached to the current source hash. The A1 finite-law interface derives strict tilted-variance positivity from the two distinct endpoint atoms with positive mass through `FiniteSupportLawData.variance_pos`; callers do not supply a free positive-variance axiom. Endpoint rate strictness is conditional on a finite one-sided integral limit and a positive-length variance gap, exactly as required by the displayed endpoint statement.

- **Recent wording changes.** The scaled-Bernoulli qualification for `m=2`, the explicit unique positive stationary root, the stated curvature equality cases, the `B:individual` deficit certificate, the `B:inputs` strictness scope, the quadratic-chain equality statement, and the explicit Bennett/Bernstein tail expressions are represented in the current contracts and declarations. They are not covered by the old 16–17 October concordance counts; the current map is the authority.

## Results whose old mapping cannot be reused

- The old A2 row and its denominator audit cannot be reused without the corrected `d` and `j` domains. The current aggregate contract supersedes it.
- The previous 46/49 status, the old 37-item register, the old 377-declaration count, the old 3,445-job audit, and the old manuscript SHA are historical records. They do not describe the current GitHub paper.
- The old baseline check that compared the paper to commit `8b75977b138205c4ba402000b25d226d55994682` was invalid after the GitHub paper publication. The baseline now protects Lean sources and pinned dependencies against that core commit while separately pinning the canonical paper to `91719272750df6103358d8daccc4de8526a0d101`.
- The seven earlier “direct dependency” failures were checker artifacts. A typed contract may prove its proposition through an inline proof or a shared helper; the revised checker audits the transitive kernel dependency closure and does not require an arbitrary same-row sibling edge.
- A source hash, a declaration name, or a token marker cannot decide TeX-to-Lean semantic equivalence. The 35 previously open marker profiles were individually reviewed against their frozen Lean contract types and are now registered in `checks/check_semantic_contract_integrity.py`; strict structural coverage is 49/49. The marker gate records reviewed type features and does not replace the mathematical statement review.

## Verification record

- `lake build ExactHoeffding`: passed, 3,454 jobs.
- Generated kernel audit: 2,028 public theorem declarations across 333 imported project modules; permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- Live theorem manifest: 394 mapped declarations, 49 result rows; source and type fingerprints match.
- Display inventory: 240 display blocks match the frozen current source.
- A1 regression checks: 11 tests passed.
- Baseline protection: passed against the protected Lean/dependency baseline and the current GitHub source hash.

The full concordance command passed:

```text
python3 checks/check_full_manuscript_concordance.py \
  --lean-command '/data/.toolchains/lean-4.33.0-linux/bin/lake env lean'
```

It reports 35 theorem-class environments, 14 supplementary claims, 49 typed contracts, and 2,028 kernel-side `#print axioms` records. The result is a structural and kernel audit; mathematical statement-level equivalence remains the reviewed contract listed above. The stricter `check_semantic_contract_integrity.py --require-contracts` mode now passes with 49/49 marker-checked contracts.
