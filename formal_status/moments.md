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
