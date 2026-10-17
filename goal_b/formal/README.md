# Goal B Lean 4 source snapshot

The snapshot contains the Lean 4 formalization of the finite-sample extremizer theorem. The toolchain and Mathlib version are pinned in `lean-toolchain` and `lake-manifest.json`.

```bash
lake exe cache get
lake build ExactHoeffding
lake env lean checks/full_closure_axioms.lean
```

The main Goal B theorem is in `ExactHoeffding/GoalBFixedSample.lean`. The project-wide theorem audit is in `checks/full_closure_axioms.lean`, and the Goal B-specific audit is in `checks/goal_b_fixed_sample_axioms.lean`.

[Unified paper](../../submission/current/manuscript.pdf) · [Current theorem–Lean correspondence](../../submission/current/theorem_lean_concordance.md)
