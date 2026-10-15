# Formal verification record — 15 October 2026

**Exact Hoeffding Constants for Finite Exchangeable Sequences**  
**Zinan Wang**

## Mathematical coverage

The principal article and technical supplement contain 30 named theorem, lemma,
proposition and corollary statements. Their declaration-level mapping is in
`formal_status/manuscript_concordance.md`. The Lean development proves the
all-parameter hypergeometric curvature bound, the parity-uniform Laplace
comparison, the actual finite-exchangeability variational identity, the exact
least coefficients, weighted concentration, fourth-order optimized expansions,
fixed-sample extremizers, exact real-margin imbalance response, and compact
analytic contraction with a uniform optimized remainder.

The odd coefficient is

```
1 / ((N - 1) * artanh (1 / N)).
```

It is valid and least for actual exchangeable probability laws on the real cube.
Its hypergeometric extremizers range over every legal success count and sample
size; no growth regime of the sample size is excluded.

The parity variance proposition is stated for the actual supremum over laws and
nonzero zero-sum contrasts. The development proves its exact value, Hamming-law
attainment for every contrast, the strict odd variance gap and its integral and
fourth-order expansion. The explicit extremizer theorem gives the full Bernoulli
pushforward law, odd nonzero-tilt contact and even zero-tilt limiting equality.

## Kernel and dependencies

- Lean: `leanprover/lean4:v4.33.0`.
- Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`.
- Dependency revisions: `lake-manifest.json`.
- Entry point: `ExactHoeffding.lean`.
- Generated transitive axiom audit: `checks/full_closure_axioms.lean`.
- Permitted reported dependencies: `propext`, `Classical.choice`, `Quot.sound`.

The final audited declaration and module counts, with the raw per-theorem output,
are recorded in `checks/logs/full_closure/final_all_manuscript_umbrella_audit.log`
and `checks/logs/full_closure/final_all_manuscript_axioms.log`.

## Reproduction

```bash
lake exe cache get
lake build ExactHoeffding
lake env lean ExactHoeffding.lean
python3 checks/generate_axiom_audit.py --check
python3 checks/check_manuscript_concordance.py
lake env lean checks/full_closure_axioms.lean > lean_axioms.log
python3 checks/check_axiom_output.py lean_axioms.log
```

The independent mathematical computations and manuscript builds are reproduced
with `bash run_all.sh`. Their full execution is retained in
`checks/logs/run_all.log`; `checks/logs/math_test_report.json` indexes the tests.
The single-entry arXiv archive and publication archive are built in empty
directories and include explicit manifests and checksums. Original work remains
Copyright © 2026 Zinan Wang; third-party literature keeps its own attribution
and licenses.
