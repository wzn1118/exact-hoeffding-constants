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

The associated Lean additions prove finite Poisson--binomial variance algebra,
reciprocal-envelope comparison and the three symmetry-envelope differences.
The Jacobi factorization, sharp hypergeometric curvature, mean-dependent
quadratic barrier and complete exchangeability theorem remain open Lean
obligations. See `LEAN_PROOF_STATUS.md` and `proof_gap_register.md`.
