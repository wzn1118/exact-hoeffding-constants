# Piecewise KL tail bounds

**Zinan Wang, 15 October 2026.** Copyright (c) 2026 Zinan Wang. All rights reserved.

Read [the six-page research note](minimum_variance_tail.pdf) and its
[LaTeX source](minimum_variance_tail.tex). The note integrates the pointwise
minimum of the manuscript's quadratic variance envelope and the classical
Poisson--binomial envelope. It gives explicit switching points and proves
strict improvements over four symmetry-related binomial KL bounds and the
exact-variance Bennett/Bernstein comparisons on its stated domain.

The optimized factorial-moment bound is stronger than this MGF-based tail
bound at integer thresholds. [The literature audit](literature_audit.md)
records the precise comparison and attribution boundaries, including which
primary texts were inspected.

## Reproduction

Run `python3 checks/verify_piecewise_kl.py` from the repository root.
The frozen matrix is `research/tail_bounds/benchmark_cases.json`; output is
`checks/results/piecewise_kl_matrix.csv` and its JSON summary. Exact tails and
factorial bounds use integer counts and rational arithmetic. Transcendental
comparisons use 70 decimal digits. This finite check supplements the written
proof; it does not supply a Lean proof of the analytic theorem.

The figure can be regenerated with `python3 checks/plot_piecewise_kl.py`
(Matplotlib required). It reads the frozen CSV without recomputing results.
The figure shows negative logarithms, so larger values are stronger bounds.

The associated Lean development now includes `ExactHoeffding/PiecewiseKL.lean`.
It proves the full quadratic envelope difference, positivity and localization of
both switching points on the stated parameter domain, the exact central-region
iff, contact formulas, and the strict three-branch comparison theorem. The
module is imported by `ExactHoeffding.lean`; its declarations are included in the full imported-closure axiom audit.

`ExactHoeffding/PiecewiseKLEndToEnd.lean` closes the ordinary binomial KL
branch for the actual canonical hypergeometric law: the tilted
Poisson--binomial representation gives the true-support variance envelope,
the Riccati comparison gives the log-Laplace inequality, and finite
exponential Markov plus the Bernoulli Fenchel identity gives the explicit upper
tail bound.

`ExactHoeffding/PiecewiseKLFull.lean` proves the stitched Riccati comparison,
its reflected lower-tail counterpart, both Fenchel contact identities, and
the actual hypergeometric upper and lower piecewise KL tails on the closed
support. The theorem domain is exactly `3 ≤ m ≤ k`, `2*k ≤ N`, `2*m < N`;
both population parities are included. Endpoints use continuity of the explicit
KL rate and monotonicity of finite tail events.

`ExactHoeffding/PiecewiseKLComparison.lean` proves the first and second
KL derivatives and instantiates the comparison for the actual envelopes:
`J > I_B` away from the mean, `J ≥ I_P`, and `J = I_P` exactly on the closed
central interval. The exterior strict inequalities include both support
endpoints.

`ExactHoeffding/PiecewiseKLStrict.lean` defines the actual finite-support
Legendre supremum and retains a positive contact gap along each exterior
branch. Its endpoint arguments compare the signed Fenchel expressions before
taking one-sided limits. The public assembly theorem is
`hypergeom_piecewise_kl_end_to_end`.

The Lean development uses kernel-checked symbolic and analytic proofs.
The Python matrix remains a separate reproducibility check. For exact
statement-to-declaration coverage, see [the concordance](lean_concordance.md).
