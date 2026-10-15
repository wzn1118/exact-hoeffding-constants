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
