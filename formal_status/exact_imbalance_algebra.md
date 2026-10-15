# Continuous-margin exact imbalance algebra

Owned source: `ExactHoeffding/ExactImbalanceAlgebra.lean`.

The module defines the real-margin falling-factorial family with `e = 1/N`,
its raw moments through degree four, and the second, third, and fourth cumulant
polynomials.  For every `N >= 5`, Lean proves the closed formulas for all real
margins `d`; these are algebraic identities for the factorial continuation and
do not assert an optimizer or an analytic global-maximizer theorem.

The module also defines

- `D(N,m) = N^2 - N - 3m(N-m)`;
- the finite-imbalance coefficients `T(N,m)` and `A(N,m)`;
- positivity of `D` for `N >= 5`, `2 <= m`, and `2m <= N`;
- the equivalent closed form for `A` used in the manuscript;
- the strict inequality `A(N,m) - N/(3(N-1)) > 0` in the same range;
- the centered fourth-cumulant identity
  `κ4(0) = -m(N-m)D / (8(N-3)(N-1)^2)`.

The exact formulas are proved by expanding the finite factorial basis and
clearing only the displayed nonzero denominators.  There is no `sorry`,
`admit`, `axiom`, or `native_decide` in the module.

Verification: `/data/hoeffding_full_20261015/evidence/exact_imbalance11.log`
returned `lean_exit_code=0` under the shared `flock`, inner `timeout 600`, and
`lean -j 1`.  The remaining diagnostics are tactic linter warnings only.
