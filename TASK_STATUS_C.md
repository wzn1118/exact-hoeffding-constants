# Finite Chernoff bridge status, 15 October 2026

`ExactHoeffding.finite_markov_exp_bound` proves a finite weighted exponential
Markov inequality for nonnegative weights, nonnegative tilt and an event on
which the values exceed an explicit threshold. It does not require normalized
weights; with normalization it is the usual finite probability tail bound.

The exact source was compiled and included in the integration's complete
library build. `checks/lean_axioms.lean` reports only `propext`,
`Classical.choice`, `Quot.sound` for this theorem.

Evidence: `research/tail_bounds/evidence/lean_integrated_build.log`,
`lean_umbrella.log`, `lean_axioms.log`.

The optimizer-to-KL identity, its endpoint limits, Riccati barrier and complete
hypergeometric instantiation remain open kernel proof obligations. They are
not replaced by a conditional MGF hypothesis in a purported final theorem.
