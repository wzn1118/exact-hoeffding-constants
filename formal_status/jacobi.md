# Jacobi Closure Status

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

## Deliberately not claimed

This block does not assert Jacobi orthogonality, real/simple roots, negative
roots of `jacobiPGF`, a product factorization, or the tilted
Poisson-binomial representation. Those claims require the next modules and
must not be introduced as assumptions.

## Sources

- `source/manuscript.tex`, `sec:reductions` and `sec:jacobi`.
- `source/odd_uniform.tex`, the proof of `odd:lem:PB`.
