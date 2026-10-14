# Proof Gap Register B

| ID | Gap | Current boundary | Required evidence | Status |
| --- | --- | --- | --- | --- |
| B-G-001 | Jacobi real-rootedness and positive-root factorization | No Lean interface currently connects the hypergeometric polynomial to Jacobi zeros. | A kernel-checked root-localization/factorization theorem with all parameter hypotheses. | Open; retained as a conditional gap |
| B-G-002 | Hypergeometric tilted law as a Poisson-binomial sum | The existing Lean code has finite masses and tilted moments, but no factorization into Bernoulli factors. | A theorem taking an explicit positive-root factorization as input, or a full Jacobi formalization. | Open; not assumed as an unconditional theorem |
| B-G-003 | Poisson-binomial mean-variance constraint | Finite Bernoulli-list algebra is proved by `finite_mean_variance_bound`; `poissonBinomial_variance_bound` exposes it with `0 ≤ pᵢ ≤ 1`. This is not a hypergeometric representation theorem. | `lake build ExactHoeffding.PoissonBinomial` and `#print axioms` under Lean 4.33.0. | Closed for the finite-list inequality; Jacobi admissibility remains B-G-001/002 |
| B-G-004 | Sharp all-tilt hypergeometric curvature upper bound | Existing `CurvatureNonnegative` proves only the lower bound `0 ≤ ψ''`; `CurvatureBridge` is conditional. | Stationary-branch argument, boundary cases, and polynomial positivity certificate. | Open |
| B-G-005 | Odd constant pointwise curvature shortcut | `source/auxiliary_curvature.tex` records an exact counterexample to the constant odd proxy pointwise bound. | Any future theorem must use the mean-dependent barrier/integrated argument, not that false shortcut. | Closed as a route; obstruction documented |
| B-G-006 | Full package verification and dependency refresh | Scoped module is verified under Lean 4.33.0; bounded `lake update` timed out while refreshing remote refs, and the full umbrella build was stopped during broad `Mathlib` import processing. | Control worktree performs the full build and umbrella entry-point check after cherry-pick. | Integration verification deferred; scoped theorem is not blocked |

No gap above is hidden behind `sorry`, `admit`, an extra axiom, `opaque`, or
`unsafe` code.
