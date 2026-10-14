# Analysis-closure status

## Baseline

- Worktree: `/data/lean_worktrees/analysis-closure`
- Branch: `formal/analysis-closure-20261015`
- Baseline: `e5621798df470fc7381a7462d377f8568b06c53c`
- Lean executable: `/data/.toolchains/lean-4.33.0-linux/bin/lean`
- Lake executable: `/data/.toolchains/lean-4.33.0-linux/bin/lake`
- Shared `.lake/packages` is the read-only link to the already-built control Mathlib cache. No `lake update` or `lake cache` operation is used.

## First delivered module

`ExactHoeffding/BernoulliKL.lean` defines `bernoulliKL`,
`bernoulliCenteredLogMGF`, and `bernoulliFenchelTilt`, and proves:

- centered Bernoulli log-MGF equals zero at `t = 0`;
- the MGF at the nondegenerate Fenchel tilt is exactly `(1-p)/(1-x)`;
- the interior Fenchel identity for `0 < p,x < 1`;
- the totalized endpoint identities `KL(0 || p) = -log(1-p)` and
  `KL(1 || p) = -log p`.

This is an exact Bernoulli rate identity, not a claim about the unresolved
finite-population crossing comparison or the global optimal quadratic proxy.

## Verification record

The fixed 4.33.0 target build passed:

```text
PATH=/data/.toolchains/lean-4.33.0-linux/bin:$PATH lake build ExactHoeffding.BernoulliKL
Build completed successfully (1950 jobs).
```

The first invocation timed out while preparing the inherited library cache;
the bounded retry compiled only the requested target after `Basic` and
`Laplace` were available. The axioms audit was run with
`lake env lean /dev/stdin` importing this module and reported:

```text
'ExactHoeffding.bernoulli_fenchel_identity' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'ExactHoeffding.bernoulliKL_zero_endpoint' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, `sorry`, `admit`, or extra axiom is present in this module.

## Remaining scope

- Complete the nondegenerate Bernoulli optimal quadratic upper bound, including
  the balanced case `p = 1/2` and equality at `t = 0`.
- Keep the Riccati/Laplace crossing comparison separate from the main theorem;
  no unproved crossing lemma may be used as an assumption of a claimed result.
- Preserve the finite-population parity, Jacobi, support, and ordinary-moment
  gaps as external dependencies owned by the other workstreams.
