# Piecewise KL concentration bounds

**Zinan Wang** — The University of Manchester<br>
**Xinhao Yang** — University of Southern California

The piecewise relative-entropy rate is obtained by integrating the pointwise minimum of the Poisson–binomial mean–variance envelope and the refined quadratic hypergeometric envelope. On
`3 ≤ m ≤ k`, `2k ≤ N` and `2m < N`, the resulting three-branch rate `J` bounds both tails of the actual finite hypergeometric law, including the support endpoints, and satisfies `I > J > I_B` away from the mean.

[Unified Main+A+B paper](../../submission/current/manuscript.pdf) · [Research note source](minimum_variance_tail.tex) · [Theorem correspondence](lean_concordance.md)

## Lean 4 proof chain

- `PiecewiseKL.lean` proves the variance-envelope switching points, positivity and contact identities.
- `PiecewiseKLEndToEnd.lean` connects the actual tilted hypergeometric law to the Bernoulli envelope and Chernoff exponent.
- `PiecewiseKLFull.lean` proves both closed-support tails through the stitched Riccati comparison.
- `PiecewiseKLComparison.lean` proves strict binomial KL improvement and the exact central equality interval against the scaled KL rate.
- `PiecewiseKLStrict.lean` proves the strict comparison with the actual finite Legendre rate and assembles `hypergeom_piecewise_kl_end_to_end`.
- `PiecewiseKLFourRates.lean` compares four sampling/complementation KL rates.
- `HypergeomBennettBernstein.lean`, `BernsteinKernel.lean` and `HypergeomBernsteinComparison.lean` prove the exact-variance Bennett and Bernstein comparisons.
- `FiniteSupportMeanEnvelope.lean` and `FiniteSupportTiltCurveOfLaw.lean` formalize the general finite-support integration interface.
- `FactorialChernoffExact.lean` and `ManuscriptIntegerTails.lean` establish the integer-threshold refinements and exact factorial-moment bounds.

These modules are part of the umbrella [`ExactHoeffding.lean`](../../ExactHoeffding.lean), with theorem types indexed in [the unified concordance](../../submission/current/theorem_lean_concordance.md).

## Numerical verification

From the repository root, run:

```bash
python3 checks/verify_piecewise_kl.py
python3 checks/plot_piecewise_kl.py
```

The first command evaluates the frozen [parameter matrix](benchmark_cases.json), with exact integer/rational arithmetic for the finite tails and factorial moments and 70-digit decimal arithmetic for transcendental comparisons. The verification suite records 292 parameter–threshold checks, endpoint integrations, symmetry comparisons and variance-scale benchmarks. The plotting script renders the corresponding rate comparisons from the generated CSV.

[Verification record](lean_validation.md) · [Literature notes](literature_audit.md) · [Complete reproducibility archive](../../submission/current/complete-reproducibility.zip)
