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
`flock /data/hoeffding_full_20261015/lean_compile.lock lean -j 1
ExactHoeffding/JacobiRoots.lean`; it exited with code `0`. This was a direct
file check, not a full project build. `#print axioms` for these new declarations
is still pending and is not claimed here.

This is not yet the PGF root theorem or the Poisson-binomial factorization.
The nearest proof gap is the explicit Leibniz expansion of the Rodrigues
derivative and the polynomial identity connecting its reverse composed with
`1-X` to `jacobiPGF`. Until that bridge and its splitting transport are proved,
the original `jacobiPGF` has no real-rootedness claim in Lean.

## Deliberately not claimed

This block does not assert Jacobi orthogonality, simple roots, negative roots
of `jacobiPGF`, a product factorization, or the tilted Poisson-binomial
representation. Splitting is established only for the separately defined
Rodrigues quotient above; it must not be presented as splitting of the PGF.

## Sources

- `source/manuscript.tex`, `sec:reductions` and `sec:jacobi` (especially
  equation `eq:jacobi` and the factorization `eq:factor`).
- `source/odd_uniform.tex`, the proof of `odd:lem:PB`.
