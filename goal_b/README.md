# Fixed-sample hypergeometric extremizers (Goal B)

**Balanced Populations Maximize the Optimal Sub-Gaussian Proxy for Hypergeometric Sampling at Every Finite Size**

**Zinan Wang** — The University of Manchester<br>
**Xinhao Yang** — University of Southern California

For every finite population `N ≥ 2` and sample size `1 ≤ m < N`, the optimal sub-Gaussian proxy is maximized at the central marked-population counts `⌊N/2⌋` and `⌈N/2⌉`. The result includes the equality classification and explicit positive off-center gap bounds.

The Goal B source is [`paper/main.tex`](paper/main.tex); the [unified Main+A+B manuscript](../submission/current/manuscript.pdf) contains the current publication version. The original derivation is preserved in [the dated research note](../research/goal_B_all_finite_fixed_sample_extremizers.md).

## Formal proofs

- [`GoalBFixedSample.lean`](../ExactHoeffding/GoalBFixedSample.lean) proves the exact all-finite extremizer theorem, even/odd gap bounds and cubic artanh inequality.
- [`GoalBIndividualMargin.lean`](../ExactHoeffding/GoalBIndividualMargin.lean) proves the two-branch individual-margin certificate and its monotonicity.
- [`GoalBOddVariation.lean`](../ExactHoeffding/GoalBOddVariation.lean) establishes the odd central finite-sum representation and nonzero maximizing-tilt stationary equation.
- [`OddCentralStrict.lean`](../ExactHoeffding/OddCentralStrict.lean) establishes strict comparison with the ordinary central variance.

All modules are imported by [`ExactHoeffding.lean`](../ExactHoeffding.lean) and included in the [project-wide axiom audit](../checks/full_closure_axioms.lean).

## Numerical certificates and reproduction

Install Python 3.10 or later, NumPy, SciPy and a LaTeX distribution with AMS packages and microtype.

```bash
python3 -m pip install -r goal_b/requirements.txt
python3 goal_b/code/verify_goal_b.py --maxN 60 --numericN 18 --output goal_b/checks/verification.json
bash goal_b/build.sh
```

The independent certificate suite reports **67,570 exact rational off-center gap checks** for `N ≤ 60`, **1,560 directly optimized numerical checks** for `N ≤ 18`, and **18 odd-population one-/two-draw checks**. The all-finite theorem is certified separately by the Lean kernel. The [Goal B workflow](../.github/workflows/goal-b-paper.yml) builds the paper and verification artifacts.

[Independent audit](checks/independent_audit.md) · [Lean reproduction notes](checks/lean_tasks.md) · [Complete reproducibility archive](../submission/current/complete-reproducibility.zip)
