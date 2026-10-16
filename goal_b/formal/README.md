# Formal source snapshot

This directory is a complete source snapshot of the Lean project used for the
Goal B theorem. From this directory, with Lean 4.33.0 and the pinned
`lake-manifest.json`, run:

```text
lake exe cache get
lake build ExactHoeffding
lake env lean checks/full_closure_axioms.lean
```

The Goal B assembly is in `ExactHoeffding/GoalBFixedSample.lean`; its dedicated
axiom audit is `checks/goal_b_fixed_sample_axioms.lean`.
