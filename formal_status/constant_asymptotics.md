# First-order exact-constant asymptotics

`ExactHoeffding/ConstantAsymptotics.lean` proves the manuscript's population
limit for the exact finite-exchangeability constant:

`N * (exactExchangeableConstant N - 1) → 1` as `N → ∞` through all natural
population sizes.

The proof first bounds the convex logarithmic-odds secant by its endpoint
derivative. This gives `1-d² ≤ imbalanceFactor d`, hence
`(N+1)/N ≤ oddHypergeomConstant N` for every `N ≥ 2`. Together with the
already proved upper bound, the parity coefficient satisfies

`1 ≤ N * (paritySharpConstant N - 1) ≤ N/(N-1)`.

The squeeze theorem supplies the limit across both parities. The proven
identity between `paritySharpConstant` and the least coefficient over actual
exchangeable cube laws then gives the end-to-end limit. No optimizer,
Taylor remainder, or asymptotic assertion is assumed.

This file concerns the first-order population limit in the main theorem.
The separate fourth-order optimized-proxy appendices require their own
formalization.

Compilation evidence: `/data/hoeffding_full_20261015/evidence/constant_asymptotics1.log`.
The locked check started at `2026-10-15T13:20:20+00:00` and completed with
`lean_exit_code=0`, using Lean 4.33.0 with `timeout 600 lean -j 1` and the
private worktree cache. Only tactic-style linter warnings were emitted.
The root integration performs the common axioms audit; this worktree did
not enqueue an additional audit.

Public theorems include `oddHypergeomConstant_first_order_limit`,
`paritySharpConstant_first_order_limit`, and
`exactExchangeableConstant_first_order_limit`. The finite bounds are exposed
as `oddHypergeomConstant_first_order_lower` and
`paritySharpConstant_first_order_bounds`.
