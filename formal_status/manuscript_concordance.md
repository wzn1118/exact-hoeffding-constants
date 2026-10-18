# Current manuscript correspondence

## Current source and verification status — 18 October 2026

The canonical manuscript is the byte-identical GitHub `main` source at commit `91719272750df6103358d8daccc4de8526a0d101`. The current TeX SHA-256 is `617cce1f87272bd5d5d58e3d91342bba658bb490cb901643fb9436ecc6e2894b`; the current PDF SHA-256 is `21e5bf768f0dc7f80d69904ec7a64642c4adacfaa04d9514ea83a0d4f32550e8`.

The live map contains 49 rows (35 theorem-class environments and 14 supplementary claims), all marked `Complete`, with 49 typed proposition contracts and 394 distinct mapped Lean theorem declarations. The display inventory contains 240 blocks. `lake build ExactHoeffding` passed 3,454 jobs. The current manifest and concordance were regenerated from this source. The older counts and scope statements below are historical and are superseded by `formal_status/current_pdf_lean_reconciliation_20261018.md`.

The three previously reported scope items are now represented in current contracts: `prop:odd2` includes the cubic asymptotic gap, `A:factorial` uses the corrected denominator and supported-threshold domains, and `cor:fixedm_gap` uses the complete aggregate contract. A1 endpoint strictness is checked under finite one-sided limits and a positive-length variance gap; endpoint atoms derive strict tilted-variance positivity through `FiniteSupportLawData.variance_pos`.

The strict semantic-contract mode now has reviewed marker profiles for all 49 contracts. The ordinary and strict checkers report structural and kernel results; marker profiles do not infer arbitrary TeX-to-Lean semantic equivalence from hashes or token markers.

## Historical notes


The authoritative result register is [`submission/current/theorem_lean_concordance.md`](../submission/current/theorem_lean_concordance.md), generated from `checks/manuscript_lean_map.json`.

The full displayed-formula inventory is [`display_formula_inventory.json`](../submission/current/display_formula_inventory.json). Independent statement-scope reviews are in `display_formula_audit_AB.md`, `display_formula_audit_main_appendices.md`, and `a1_final_scope_audit_20261017.md`. Typed contract coverage and the remaining statement-translation gap are tracked in `semantic_contract_audit_20261017.md`. The exact inspected Lean declaration manifest records actual types, source bindings, dependencies, and allowed axioms.

At the earlier audit snapshot, A2 was scope-qualified while the paper still lacked the ordinary factorial fraction condition j≤N and the supported strict I/J condition d≤m. The current contract now includes both domains. The former Q-expansion remainder gap is covered by `rescaledProxyExtension_joint_uniform_taylor` in `ActualProxyUniformTaylor.lean`; B2 also classifies the deterministic sample boundaries and every maximizing tilt. The theorem-class and strict semantic-contract checkers now pass for all mapped rows. The display-formula inventory remains independently checked.


At the earlier audit snapshot, standalone typed Lean proposition contracts covered ten rows: `A:integration`, `extra:A3-four-binomial-KL`, `extra:A4-Bennett-Bernstein`, `thm:curvature`, `thm:main_laplace`, `cor:mgf`, and the integer/two-sided tail corollary. Their declarations and proof dependencies are checked against the full kernel/audit manifest. The A1 contract groups both rate bounds, actual finite weighted tails, interval strictness, and endpoint limits. Its finite-law assumptions include two distinct extremal support atoms of positive mass; `FiniteSupportLawData.variance_pos` derives strict tilted-variance positivity, and `finiteSupportLawData_toTiltCurve_of_endpoints` exposes no positive-variance caller premise. The A1 regression checker validates that proof chain. The register contains 49 items (35 theorem environments plus 14 supplements), 377 declaration references to 339 distinct Lean theorems. Each contract is a reviewed Lean transcription; hashes and declaration checks do not automatically prove equivalence with TeX. That historical snapshot predates the current 49-row aggregate contract register.
