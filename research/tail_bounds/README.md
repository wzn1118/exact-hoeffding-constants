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
module is imported by `ExactHoeffding.lean`; its declarations use only
`propext`, `Classical.choice`, and `Quot.sound`.

`ExactHoeffding/PiecewiseKLEndToEnd.lean` closes the ordinary binomial KL
branch for the actual canonical hypergeometric law: the tilted
Poisson--binomial representation gives the true-support variance envelope,
the Riccati comparison gives the log-Laplace inequality, and finite
exponential Markov plus the Bernoulli Fenchel identity gives the explicit upper
tail bound.

The remaining analytic input is the outer tangent-branch identification:
turning the reciprocal-curvature integral along the actual inverse tilted-mean
coordinate into the closed tangent-corrected formula in `piecewiseKLRate`.
The ordinary binomial branch and its actual hypergeometric tail bound are
already proved in `PiecewiseKLEndToEnd.lean`; the numerical verifier is used
only for reproducibility checks.
