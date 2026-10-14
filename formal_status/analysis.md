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
  `KL(1 || p) = -log p`;
- `bernoulliKL_nonneg` for the nondegenerate interior, proved from
  `Real.log_le_sub_one_of_pos` applied to the two reciprocal ratios;
- the global Fenchel upper bound
  `x*t - log(1-p+p*exp t) <= bernoulliKL p x` for every `0 <= x <= 1`,
  with separate kernel proofs for `x = 0`, `0 < x < 1`, and `x = 1`.

This is an exact Bernoulli rate identity, not a claim about the unresolved
finite-population crossing comparison or the global optimal quadratic proxy.

## Verification record

The fixed 4.33.0 direct module build passed after the scoped target build was
resource-bound by concurrent repository work:

```text
PATH=/data/.toolchains/lean-4.33.0-linux/bin:$PATH \
  LEAN_PATH=<local .lake/build/lib/lean plus read-only control package paths> \
  lean -j 1 -o .lake/build/lib/lean/ExactHoeffding/BernoulliKL.olean \
  -i .lake/build/lib/lean/ExactHoeffding/BernoulliKL.ilean \
  ExactHoeffding/BernoulliKL.lean
exit=0; only unused endpoint-parameter linter warnings
```

The initial `lake build ExactHoeffding.BernoulliKL` attempt was bounded at
180 seconds and stopped without a success claim; no dependency update or
cache operation was used. The successful direct build above uses the same
fixed Lean 4.33.0 kernel and the read-only control package cache. The axioms
audit imported the generated local `.olean` and reported:

```text
'ExactHoeffding.bernoulli_fenchel_identity' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'ExactHoeffding.bernoulliKL_zero_endpoint' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'ExactHoeffding.bernoulliKL_nonneg' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'ExactHoeffding.bernoulli_fenchel_upper' depends on axioms:
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
