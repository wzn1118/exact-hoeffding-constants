# Moment and symmetry formalization status

Worktree: `/data/lean_worktrees/moments-closure`  
Branch: `formal/moments-closure-20261015`  
Base: `e5621798df470fc7381a7462d377f8568b06c53c`  
Lean toolchain: Lean 4.33.0 with the worktree's existing mathlib dependencies.

## Verified and committed

- `921ccbea31546f2810ae933e1700137782d7e8a4`: totalized PMF, exact support,
  support equivalence, and finite-range mass normalization in
  `ExactHoeffding/Support.lean`.
- `f8fb917634af15bd4bfe4c1c0154750d109dcb50`: complete mean, second
  factorial moment, raw second moment, and variance in
  `ExactHoeffding/OrdinaryMomentsComplete.lean`. The variance formula is
  proved for `N ≥ 2`; `N = 0,1` are handled by the actual degenerate cases.
- `bc23ae47112b132e05d3642ddc078be47f687909`: PMF transposition and finite
  MGF transposition in `ExactHoeffding/Symmetries.lean`.
- `f309fa3`: success-complement PMF and MGF identities in
  `ExactHoeffding/Symmetries.lean`; the MGF proof reindexes the finite sum
  directly with `Finset.sum_range_reflect`.
- `85746ae`: sample-complement MGF identity, derived by transposition,
  success-complement, then transposition back.

Each listed module was built with exit code 0 using the Lean 4.33.0 toolchain
and the shared compile lock. `#print axioms` on the support, ordinary-moment,
and transposition theorems showed only `[propext, Classical.choice,
Quot.sound]`. The six symmetry declarations, including both complement MGF
identities, were also audited and have exactly that same axiom list.

## Verified symmetry identities

The success-complement identity uses `Finset.sum_range_reflect`, explicit
natural-index normalization by `omega`, and a local cast normalization for
the exponential identity. Two intermediate builds exposed and resolved
rewrite-direction/index/cast mismatches; the final build has no Lean errors.
The sample-complement identity is also kernel-checked. No umbrella imports or
pre-existing project files have been changed.

## General factorial moments

`ExactHoeffding/GeneralFactorialMoments.lean` adds the all-degree finite-sum
identity with an explicit `q ≤ m` guard, followed by the normalized
`E[(H)_q]` formula guarded by `q ≤ N`. It is newly added and is awaiting its
`q ≤ N` formula. The module build completed successfully with exit code 0
under the shared compile lock. The finite-sum proof is over `ℕ`, using the
descending-factorial shift and Vandermonde normalization; no real division is
used until the normalized expectation theorem.

## Reproduction

From the worktree root:

```sh
flock -x /data/hoeffding_full_20261015/lean_compile.lock -c \
  'PATH=/data/.toolchains/lean-4.33.0-linux/bin:$PATH lake build ExactHoeffding.Support'
flock -x /data/hoeffding_full_20261015/lean_compile.lock -c \
  'PATH=/data/.toolchains/lean-4.33.0-linux/bin:$PATH lake build ExactHoeffding.OrdinaryMomentsComplete'
flock -x /data/hoeffding_full_20261015/lean_compile.lock -c \
  'PATH=/data/.toolchains/lean-4.33.0-linux/bin:$PATH lake build ExactHoeffding.Symmetries'
```

Do not run `lake update` or write to shared `.lake/packages` dependencies.

## Actual MGF derivatives and fixed-parameter Taylor expansion

`ExactHoeffding/Cumulants.lean` was committed as
`8058f72868484b8f8d681694dcd621f5c34f6694`; the coordinator reports its
integration as `c342d19`. Its raw-moment and cumulant formulas are reused,
not restated as derivative assumptions.

The owned modules `ExactHoeffding/MGFDerivatives.lean` and
`ExactHoeffding/LogMGFTaylor.lean` both compiled successfully with exit code
0 on 2026-10-15. The derivative module was immediately committed as
`380e1d7c637534f2427dd6d4a6a38520ddaa3b65` before compiling the Taylor module.
The following are kernel-checked deliverables:

- Every iterated derivative of the actual finite exponential sum equals
  its unnormalized tilted raw moment; at zero it equals the raw moment.
- For nonnegative normalized finite weights, the first four actual
  iterated derivatives of the log-MGF at zero equal the ordinary cumulants.
- For all valid hypergeometric parameters `k ≤ N`, `m ≤ N`, including
  `N = 0,1`, specialize those derivative identities to the actual finite MGF.
- Identify the fourth Taylor polynomial and prove its Peano `o(t^4)`
  remainder as `t → 0`, for each fixed `(N,k,m)`.
- For each nonzero real `t`, express the remainder as the actual fifth
  derivative at an intermediate `u ∈ uIoo 0 t`, times `t^5 / 120`.

Public entry points include `finiteMGF_iteratedDeriv`,
`finiteMGF_iteratedDeriv_zero`, `hypergeomMGF_iteratedDeriv_zero`,
`finiteLogMGF_deriv1_zero_cumulant` through
`finiteLogMGF_deriv4_zero_cumulant`, and
`hypergeom_logMGF_deriv1_zero` through `hypergeom_logMGF_deriv4_zero`.
The remainder theorems are `hypergeom_logMGF_taylor4_isLittleO` and
`hypergeom_logMGF_taylor4_lagrange`; `hypergeom_logMGF_taylor4_eq` identifies
the actual Taylor polynomial with the ordinary-cumulant polynomial.

The general finite-MGF derivative formula does not require nonnegative or
normalized weights. Logarithmic derivatives use only nonnegativity and
normalization to prove strict positivity, not a derivative or cumulant
conclusion as an assumption. The hypergeometric log-MGF and Taylor results
assume only `k ≤ N` and `m ≤ N`, with no positive-population restriction.

This is a fixed-distribution expansion. It does not assert uniformity in
`N`, exchange limits or suprema, identify optimizing parameters, or prove
the paper's separate `N → ∞` globally optimized asymptotic expansion.

The successful build uses Lean 4.33.0, a single shared lock, and a timeout
inside the lock (so waiting for the lock does not consume the timeout):

```sh
export PATH=/data/.toolchains/lean-4.33.0-linux/bin:$PATH
export LEAN_PATH="$PWD/.lake/build/lib/lean"
for package in .lake/packages/*; do
  export LEAN_PATH="$LEAN_PATH:$PWD/$package/.lake/build/lib/lean"
done
flock -x /data/hoeffding_full_20261015/lean_compile.lock -c \
  'timeout 600 lean -j 1 -o .lake/build/lib/lean/ExactHoeffding/MGFDerivatives.olean ExactHoeffding/MGFDerivatives.lean'
flock -x /data/hoeffding_full_20261015/lean_compile.lock -c \
  'timeout 600 lean -j 1 -o .lake/build/lib/lean/ExactHoeffding/LogMGFTaylor.olean ExactHoeffding/LogMGFTaylor.lean'
```

The combined build attempt 8 timed out with exit code 124 and an empty
diagnostic log; it did not certify a theorem. Splitting off the derivative
module reduces the imports needed to validate that part independently.
Attempt 9 exposed one redundant `ring` after `field_simp` had already
closed the goal. Removing that tactic and an unused `norm_num` resolved
the diagnostic without changing a theorem statement or adding assumptions.

Successful sequential diagnostic log:
`.lake/build/logmgf-taylor-build-10.log`. It records
`derivatives_exit_code=0` and `taylor_exit_code=0`, with compilation starts
at `2026-10-15T13:24:07Z` and `2026-10-15T13:24:17Z`, respectively.
The source policy scan for `sorry`, `admit`, `axiom`, and `native_decide`,
and `git diff --check`, also returned exit code 0.
No standalone `#print` audit is run for this module; the coordinator owns
the final combined audit.

## Actual inverse-population optimizer closure (2026-10-15)

All modules below are new owned files in `moments-closure`, on
`formal/moments-closure-20261015`. No root umbrella, other worker module,
or finite-population Bernoulli comparison is changed. In particular,
`HighCumulants.lean` and `FinitePopulationBernoulliEnvelope.lean` remain
outside this worker's ownership.

The continuation is the actual factorial-basis MGF with independent real
inverse population `e`, not a numerical proxy or a fixed-law tilt Taylor
series. For `N >= 2`, `k <= N`, `1 <= m <= N`, and
`2 * (k : Real) + s = N`, it agrees at `e = 1/N` with the finite
hypergeometric law. The removable value of `Q(e,0)` is proved equal to
the actual variance; for `t != 0` it is exactly
`2 * log(centeredHypergeomMGF N k m t) / t^2`.

### Committed kernel-checked modules

| Commit | Module | Successful build log under `.lake/build/` |
| --- | --- | --- |
| `2a375de` | `RescaledFactorialFamily` | `rescaled-factorial-family-build-3.log` |
| `c0af066` | `RescaledMGFBridge` | `rescaled-mgf-bridge-build-2.log` |
| `d2c31b6` | `AnalyticQuotientKernels` | `analytic-quotient-kernels-build-2.log` |
| `1ef0f03` | `RescaledProxyAnalytic` | `rescaled-proxy-analytic-build-2.log` |
| `619f965` | `RescaledQLimit` | `rescaled-q-limit-build-3.log` |
| `2edcfd7` | `LimitProxyStrict` | `limit-proxy-strict-build-7.log` |
| `1bf9dbd` | `RescaledActualProxy` | `rescaled-actual-proxy-build-3.log` |
| `932ce6a` | `RescaledCompactConvergence` | `rescaled-compact-convergence-build-4.log` |
| `30e2d95` | `ActualProxyTail` | `actual-proxy-tail-build-2.log` |
| `89a2bc1` | `ActualOptimizerLocalization` | `actual-optimizer-localization-build-7.log` |
| `41c9f11` | `LimitProxyCurvature` | `limit-proxy-curvature-build-2.log` |
| `927f34b` | `AnalyticTiltPartial` | `analytic-tilt-partial-build-2.log` |
| `5dabb00` | `RescaledUniformConcavity` | `rescaled-uniform-concavity-build-1.log` |
| `988ac9f` | `ActualUniqueOptimizer` | `actual-unique-optimizer-build-1.log` |
| `1bee98a` | `AnalyticImplicitTilt` | `analytic-implicit-tilt-build-3.log` |
| `a6ae366` | `RescaledAnalyticOptimizer` | `rescaled-analytic-optimizer-build-2.log` |
| `f64cd63` | `RescaledTiltCoefficient` | `rescaled-tilt-coefficient-build-3.log` |
| `d8fe091` | `RescaledMixedDerivative` | `rescaled-mixed-derivative-build-2.log` |
| `e701509` | `AnalyticOptimizerLeading` | `analytic-optimizer-leading-build-2.log` |
| `6cd7a66` | `RescaledOptimumLeading` | `rescaled-optimum-leading-build-2.log` |
| `74f24db` | `ActualAnalyticAsymptotics` | `actual-analytic-asymptotics-build-3.log` |
| `35d0551` | `ActualOptimizerPopulationLimit` | `actual-optimizer-population-limit-build-1.log` |
| `e9b4a4e` | `AnalyticCurveSecondDerivative` | `analytic-curve-second-derivative-build-2.log` |
| `2c89348` | `RescaledVarianceSecond` | `rescaled-variance-second-build-2.log` |
| `e8b0cd0` | `RescaledOptimumSecond` | `rescaled-optimum-second-build-2.log` |
| `6bac0f7` | `NormalizedOptimumSecond` | `normalized-optimum-second-build-2.log` |
| `85ac836` | `ActualOptimumSecondExpansion` | `actual-optimum-second-expansion-build-1.log` |
| `25aabea` | `ActualNormalizedAsymptotics` | `actual-normalized-asymptotics-build-2.log` |

Each listed proof module was compiled with Lean 4.33.0, `-j 1`, and exit
code 0. Earlier failed build attempts are not certificates; the table
records the successful final log for each module.
All new compilations use the exclusive lock
`/data/hoeffding_full_20261015/lean_compile.lock` and `timeout 600` inside
the lock. No standalone `#print` or extra audit compilation is run.

### Actual proved mathematical scope

- Joint real analyticity of the explicit removable `Q` near `(0,0)` and
  along the entire limiting axis `(0,t)`; compact uniform convergence
  includes zero tilt.
- Strict limiting inequality `Q(0,t) < Q(0,0) = m/4` for `m > 0`,
  `t != 0`, plus the actual support tail `Q_N(t) <= 2*m/abs(t)`.
- Uniform localization of all actual global maxima, proved rather than
  assumed, and existence and uniqueness for all sufficiently large
  admissible integer populations. Arbitrary subsequences `N(n) -> infinity`
  are covered, so odd-population applications do not use a vacuous
  all-integers fixed-parity premise.
- Actual limiting Hessian `Q_tt(0,0) = -m/48` and actual mixed derivative
  `Q_et(0,0) = m*s/12`.
- An analytic implicit critical branch is constructed using the analytic
  inverse theorem and identified with the actual unique global optimizer.
  No maximizer, optimizer continuity, or derivative formula is assumed.
- The same optimizing branch satisfies `tau(0)=0`, `tau'(0)=4*s`,
  `tau(e)=4*s*e+e^2*T(e)` with `T` analytic near zero, and hence an
  actual `O(e^2)` remainder. For `s > 0`, its actual optimizing tilt is
  positive eventually along every admissible population subsequence, with
  `tau(1/N)/(1/N) -> 4*s`.
- The normalized optimized value is analytic, equals one at zero, has
  derivative one there, and has second derivative `2*(1-s^2/3)` at zero.
  It is exactly `1+e+(1-s^2/3)*e^2+e^3*U(e)` for `U` analytic near zero,
  with an actual `O(e^3)` remainder. The proof differentiates the actual
  analytic optimizing curve and computes its Hessian; it does not assume
  a derivative-of-supremum formula.
- `actualHypergeomProxy_normalized_optimum_second_along` specializes this
  to the actual normalization `4*N*Q_N(t*)/(m*(N-m))` along every
  admissible integer sequence tending to infinity. It simultaneously
  supplies the same positive analytic unique global optimizing branch
  when `s > 0`. There is no assumption selecting an optimizer.

Thus this is a genuine globally optimized expansion in inverse population,
not the earlier fixed-distribution Taylor theorem. The arithmetic domain
is fixed `m > 0`, fixed real `s` (positive for positivity), eventual
`N >= 2`, `k <= N`, `m <= N`, and `2*k+s=N`. The normalization bridge
uses eventual `N > m`, which follows from the population limit.

### Remaining coefficient work (not certified here)

The explicit tilt coefficients at orders `e^2,e^3` and normalized optimal
value coefficients at orders `e^3,e^4` in `source/new_results.tex`
have not yet been asserted as Lean theorems by these modules. The normalized
`e^2` coefficient is now proved, not just hidden in an analytic remainder.
The next tilt coefficient needs the next actual derivatives of the
critical equation, including the inverse-population derivative of
`Q_tt(e,0)` (the actual fourth-cumulant continuation); the subsequent
coefficients require the higher derivatives as well. The fourth-order
expansion and its `O(e^5)` remainder remain open until these actual
derivative/coefficient computations are kernel-checked.
The coordinator's high-cumulant work is not duplicated or inferred from
uncompiled statements.

### Reproduce a newly proved module

For example, after its committed imports are built in the same local
build directory:

```sh
export PATH=/data/.toolchains/lean-4.33.0-linux/bin:$PATH
export LEAN_PATH="$PWD/.lake/build/lib/lean"
for package in .lake/packages/*; do
  export LEAN_PATH="$LEAN_PATH:$PWD/$package/.lake/build/lib/lean"
done
flock -x /data/hoeffding_full_20261015/lean_compile.lock -c \
  'timeout 600 lean -j 1 -o .lake/build/lib/lean/ExactHoeffding/ActualNormalizedAsymptotics.olean ExactHoeffding/ActualNormalizedAsymptotics.lean'
```

The last command completed with exit code 0; the final log also records
`lean_exit_code=0`. Each intermediate module was independently compiled
and committed before compiling its dependent modules. Source-policy and
whitespace checks do not trigger any extra Lean import or audit.
