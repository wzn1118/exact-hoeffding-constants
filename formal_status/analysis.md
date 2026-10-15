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

## Balanced quadratic proxy

`ExactHoeffding/BernoulliProxy.lean` now proves, without assuming the
two-contact comparison, the balanced case

```text
bernoulliCenteredLogMGF (1/2) t <= (1/4) * t^2 / 2
```

by the exact factorization
`bernoulliMGF (1/2) t = exp (t/2) * cosh (t/2)` and Mathlib's
`Real.cosh_le_exp_half_sq`.  It also proves the exact equality statement at
`t = 0`.  The non-balanced extension is recorded below.

The fixed 4.33.0 direct module build was run serially under
`/data/hoeffding_full_20261015/lean_compile.lock`:

```text
flock -w 900 /data/hoeffding_full_20261015/lean_compile.lock \
  .../lean -j 1 -o .lake/build/lib/lean/ExactHoeffding/BernoulliProxy.olean \
  -i .lake/build/lib/lean/ExactHoeffding/BernoulliProxy.ilean \
  ExactHoeffding/BernoulliProxy.lean
exit=0
```

The subsequent audit of the generated `.olean` reported:

```text
'ExactHoeffding.bernoulli_half_quadratic_bound' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'ExactHoeffding.bernoulli_half_quadratic_bound_at_zero' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, `sorry`, `admit`, or extra axiom is present in this module.

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

## Checked sub-half extension (2026-10-15)

- Commit: `d3ee261fef212d15935a55e63d0d293a3a8e8dc7`.
- Paper location: `source/manuscript.tex`, Appendix `app:bernoulli`, formula
  `eq:bernproxy`; equivalent squared-coordinate proof as in
  `docs/odd_population_proof_zh.md`.
- Statement: `bernoulli_quadratic_bound_lt_half (p) (0 < p) (p < 1/2) (t)`
  proves `bernoulliCenteredLogMGF p t <=
  ((1-2*p)/(2*log((1-p)/p))) * t^2/2` for every real tilt `t`.
- Proof: exact shifted `log cosh` representation, proved concavity of `tanh`
  on `Ici 0`, antitonicity of `tanh(x)/x` on `Ioi 0`, and the shared generic
  `even_tangent_square_of_deriv_ratio_antitone`. No tangent inequality or
  Bernoulli upper bound is assumed in the theorem.
- External checked dependency: `ExactHoeffding.TwoDrawProxy`, worker commit
  `03f6e5adc2ced2d45f3026d74c5795d8d4e3f177`, integrated by root as `6495d3a`.
  Only existing `.olean` artifacts were copied into the private build; their
  sources are not duplicated in this branch.
- Build: fixed Lean 4.33.0, `lean -j1 -o
  .lake/build/lib/lean/ExactHoeffding/BernoulliProxy.olean -i
  .lake/build/lib/lean/ExactHoeffding/BernoulliProxy.ilean
  ExactHoeffding/BernoulliProxy.lean`, serialized by `flock
  /data/hoeffding_full_20261015/lean_compile.lock` with no lock-wait timeout.
  The resulting `.olean` was imported successfully for the axioms audit.
  Compile log: `/data/hoeffding_full_20261015/evidence/bernoulli_proxy_subhalf.log`;
  only the unused `zero_div` simp-argument warning remains. This is a direct
  module kernel build, not a new claim of a full `lake build` on this old
  branch.
- The subsequent lock-protected `lean -j1 --stdin` audit printed the same
  axiom list for `bernoulli_quadratic_bound_lt_half`,
  `bernoulli_log_cosh_tangent_square`, and `bernoulli_tanh_ratio_antitone`:
  `[propext, Classical.choice, Quot.sound]`. There is no `sorryAx`.

## Checked closed-interval sharp proxy (2026-10-15)

`ExactHoeffding/BernoulliOptimal.lean` proves the sharp global quadratic
bound and its leastness for every `0 <= p <= 1`:

```text
bernoulli_sharp_quadratic_bound (p) (0 <= p) (p <= 1) :
  IsQuadraticProxy (bernoulliCenteredLogMGF p) (bernoulliSharpBeta p)

bernoulli_sharp_quadratic_optimal (p) (0 <= p) (p <= 1) :
  IsOptimalQuadraticProxy (bernoulliCenteredLogMGF p) (bernoulliSharpBeta p)
```

- `bernoulliSharpBeta` is `1/4` at balance and
  `(1-2*p)/(2*log((1-p)/p))` otherwise, with proved value zero at both
  deterministic endpoints.
- MGF reflection supplies the upper-half bound. At every non-balanced
  interior parameter, the tilt `2*log((1-p)/p)` is nonzero and attains
  equality; this proves leastness without assuming any desired bound.
- The balanced lower bound reuses the checked actual hypergeometric
  quotient limit at `N=2, k=1, m=1`, the balanced zero-tilt variance formula,
  and the exact singleton identity. The dependency
  `ExactHoeffding.SingletonOptimalProxy` was integrated by root as
  `c38b5d6`; `ExactHoeffding.VarianceOptimality` as `8dc68b3`.
  These modules do not import `BernoulliOptimal`, so there is no cycle.
- Existing dependency artifacts were copied only to this worktree's private
  build. No shared package, other worktree source, or umbrella was edited.
- Verification: Lean 4.33.0, private `LEAN_PATH`, shared `flock` without a
  lock-wait timeout, and `timeout 600 lean -j1 -o ... -i ...
  ExactHoeffding/BernoulliOptimal.lean`. The complete module compilation
  started at `2026-10-15T06:51:47Z` and returned `lean_exit_code=0`.
  Log: `/data/hoeffding_full_20261015/evidence/bernoulli_optimal4.log`.
  Only two `unnecessarySeqFocus` linter warnings remain.
- No extra per-module axioms audit was queued; the new module's audit is
  root-owned as requested. Its source contains no `sorry`, `admit`, `axiom`,
  `native_decide`, or `unsafe` declaration. This is a direct module kernel
  build, not a claim that the full historical branch was rebuilt.

## Remaining scope

- The finite-population odd-exact optimization and integration into the
  manuscript's main theorem remain root-owned work. The closed-interval
  Bernoulli result alone is not reported as that full theorem.
- The earlier Riccati/Jacobi/support/moment gaps are external workstreams;
  this status file does not certify their closure.
