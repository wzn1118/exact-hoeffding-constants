# Jacobi Closure Status

Updated: 2026-10-15. Owner: Jacobi closure worktree.

## Scope

This branch starts from `e562179` on `formal/jacobi-closure-20261015`.
The first checked block covers the normalized parameters from
`source/manuscript.tex`, section `sec:jacobi`:

```text
k = j,  m = j + h,  N = 2*j + h + r,  j,h,r >= 0.
```

`ExactHoeffding/Jacobi.lean` defines the real polynomial `jacobiPGF` with
the division-free integer coefficients

```text
choose j i * descFactorial (j+h) i * descFactorial (r+j) (j-i).
```

## Checked in this block

- The normalized margins satisfy the finite-population inequalities required
  by the hypergeometric model.
- The factorial form of each coefficient is proved, including the exact
  `(r+j)! / (r+i)!` factor for `i <= j`.
- Coefficients are positive on the full support `0 <= i <= j`.
- The real polynomial coefficient formula, support bound, nonzeroness,
  constant coefficient, degree coefficient, and adjacent coefficient
  recurrence are kernel-checked.
- Lean 4.33 targeted checks passed: `lake env lean
  ExactHoeffding/Jacobi.lean` and `lake build ExactHoeffding.Jacobi` both
  exited with code `0`.
- `#print axioms` passed for the normalization, factorial-form, positivity,
  coefficient, support, and recurrence declarations. The outputs contain
  only `propext`, `Quot.sound`, and, for finite polynomial sums,
  `Classical.choice`.

## Rodrigues Root Progress

`ExactHoeffding/JacobiRoots.lean` now proves a genuine real-rootedness result
for the endpoint-removed Rodrigues polynomial; it does not assume a Jacobi
root theorem. For a split real polynomial, `card_roots_le_derivative` and the
exact degree drop show its derivative is split. Iterating this for
`X^(h+j) * (X-1)^(r+j)`, then removing the provable endpoint factors `X^h`
and `(X-1)^r`, proves `jacobiRodrigues j h r` splits.

The targeted check used Lean 4.33.0 and the existing mathlib build artifacts:
`lean -j 1 ExactHoeffding/JacobiRoots.lean`; it exited with code `0`. This was
a direct file check, not a full project build. `#print axioms` for these new
declarations is still pending and is not claimed here.

## Hypergeometric Connection

`jacobiPGF_eval_eq_scaled_hypergeomPolynomial` now proves, for every real `z`,
that the Jacobi coefficient polynomial evaluates to

```text
((j+h)! (r+j)! / (j+h+r)!) * hypergeomPolynomial (2*j+h+r) j (j+h) z.
```

The proof establishes coefficient equality over the entire support, including
the zero tail, then identifies the finite sums. A direct Lean 4.33.0 check
compiled `ExactHoeffding/Jacobi.lean` to its targeted `.olean` with exit code
`0`. The `#print axioms` output for the scaled coefficient lemmas and the
full-evaluation identity contains only `propext`, `Classical.choice`, and
`Quot.sound`; no `sorryAx` is present. This was a targeted direct Lean check,
not a full project build.

## Checked Mobius Bridge

`ExactHoeffding/JacobiMobius.lean` now proves the explicit Leibniz expansion,
the exact degree `j` of the Rodrigues quotient, and the polynomial identity

```text
jacobiPGF j h r = (jacobiRodrigues j h r).reverse.comp (C 1 - X).
```

This connects the already checked actual hypergeometric coefficients to the
split Rodrigues quotient without assuming a root or factorization theorem.
The targeted Lean 4.33.0 command, using this worktree's private build path,
was `flock /data/hoeffding_full_20261015/lean_compile.lock timeout 600 lean
-j1 -o .lake/build/lib/lean/ExactHoeffding/JacobiMobius.olean
ExactHoeffding/JacobiMobius.lean`. The lock had no wait timeout. The real
exit code was `0`; `/tmp/jacobi-mobius-lean4.log` records that result and
the three `#print axioms` checks, each containing only `propext`,
`Classical.choice`, and `Quot.sound`.

The splitting transport, negative roots, and tilted product factorization
are still pending the separate `JacobiFactorization.lean` check.

## Deliberately not claimed

This block does not assert Jacobi orthogonality, simple roots, negative roots
of `jacobiPGF`, a product factorization, or the tilted Poisson-binomial
representation. Splitting has not yet been transported through the checked
Mobius identity and must not yet be presented as splitting of the PGF.

## Sources

- `source/manuscript.tex`, `sec:reductions` and `sec:jacobi` (especially
  equation `eq:jacobi` and the factorization `eq:factor`).
- `source/odd_uniform.tex`, the proof of `odd:lem:PB`.


## Simple roots of the actual PGF

`ExactHoeffding/JacobiSimpleRoots.lean` proves the coefficient recurrence form of
the second-order Jacobi differential equation for the actual canonical PGF.
Using the negative-root location and polynomial root multiplicity divisibility,
it proves that every real root has nonzero derivative and hence that the root
multiset has no repetitions. The checked module is compiled at commit
`4c5a347`; the targeted Lean invocation exited with code `0` (only unused-simp
and unused-tactic linter warnings). This closes the actual-PGF simple-root
claim. Standard Jacobi normalization and the corresponding `(-1,1)`
localization remain separate statements.
