> Historical finite-Chernoff workstream record. The final integrated branch supersedes the interim status below; the authoritative records are `formal_status/full_closure.md`, `formal_status/manuscript_concordance.md`, and the final closure audit logs.

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

At the time of this snapshot, the optimizer-to-KL identity, endpoint limits,
Riccati barrier and hypergeometric instantiation were open obligations. They are
completed in the integrated branch and audited through the final umbrella.
