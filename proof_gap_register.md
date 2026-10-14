# Proof Gap Register B

| ID | Gap | Current boundary | Required evidence | Status |
| --- | --- | --- | --- | --- |
| B-G-001 | Jacobi real-rootedness and positive-root factorization | No Lean interface currently connects the hypergeometric polynomial to Jacobi zeros. | A kernel-checked root-localization/factorization theorem with all parameter hypotheses. | Open; retained as a conditional gap |
| B-G-002 | Hypergeometric tilted law as a Poisson-binomial sum | The existing Lean code has finite masses and tilted moments, but no factorization into Bernoulli factors. | A theorem taking an explicit positive-root factorization as input, or a full Jacobi formalization. | Open; not assumed as an unconditional theorem |
| B-G-003 | Poisson-binomial mean-variance constraint | Finite Bernoulli-list algebra is proved by `finite_mean_variance_bound`; `poissonBinomial_variance_bound` exposes it with `0 ≤ pᵢ ≤ 1`. This is not a hypergeometric representation theorem. | `lake build ExactHoeffding.PoissonBinomial` and `#print axioms` under Lean 4.33.0. | Closed for the finite-list inequality; Jacobi admissibility remains B-G-001/002 |
| B-G-004 | Sharp all-tilt hypergeometric curvature upper bound | Existing `CurvatureNonnegative` proves only the lower bound `0 ≤ ψ''`; `CurvatureBridge` is conditional. | Stationary-branch argument, boundary cases, and polynomial positivity certificate. | Open |
| B-G-005 | Odd constant pointwise curvature shortcut | `source/auxiliary_curvature.tex` records an exact counterexample to the constant odd proxy pointwise bound. | Any future theorem must use the mean-dependent barrier/integrated argument, not that false shortcut. | Closed as a route; obstruction documented |
| B-G-006 | Full package verification and dependency refresh | Integrated library builds with Lean 4.33.0; dependency revisions are locked in lake-manifest.json. | research/tail_bounds/evidence/lean_integrated_build.log and lean_axioms.log | Closed for the integrated library; the analytic gaps above remain open |

## Complete proof-chain status

| Obligation | Current verified portion | Remaining obligation |
| --- | --- | --- |
| L1 | Normalization, factorial moments, positive-margin mean, finite MGF derivatives | Full support/symmetry API, all ordinary-moment edge cases and permutation sampling |
| L2 | Finite Bernoulli-list variance inequality | Jacobi roots and actual hypergeometric factorization |
| L3 | Exact tilted variance identity and nonnegative curvature | Sharp upper curvature with stationary certificates |
| L4 | Written variance-envelope and Laplace proof | Kernel-checked Riccati comparison and strictness |
| L5 | Singleton nonzero-tilt lower-bound equality | Bernoulli global upper proxy, three-mass theorem, parity extrema |
| L6 | Centering and contrast algebra | Finite exchangeable measure and two-level variational reduction |
| L7 | Finite exponential Markov; reciprocal/symmetry envelope algebra | KL optimization, inverse-mean integration and hypergeometric specialization |
| L8 | No unconditional top-level sharp constant theorem | Compose all prerequisite proofs with original quantifiers |

The piecewise tail note proves an analytic consequence of the existing
variance bounds. Its `I''=1/V` integration, switching-root theorem and strict
tail comparisons are not yet kernel-certified. Numerical checks do not
change this status. No coverage percentage is assigned to incomplete proof
obligations without a weighted inventory of the actual statements.

No gap above is hidden behind `sorry`, `admit`, an extra axiom, `opaque`, or
`unsafe` code.
