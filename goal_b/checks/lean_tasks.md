# Goal B Lean verification record

The fixed-sample all-finite assembly is now encoded in
`ExactHoeffding/GoalBFixedSample.lean` and imported by `ExactHoeffding.lean`.
The target module and the umbrella import both use the pinned Lean 4.33.0 /
Mathlib environment.

## Kernel-checked results

The new module proves, for every legal finite population and every fixed
sample size:

1. `real_artanh_cubic_lower` and `imbalanceFactor_cubic_upper` give the
   cubic Bernoulli margin bound on the complete open domain.
2. `odd_imbalance_factor_offcenter_lt` and
   `even_imbalance_factor_offcenter_gap` give the parity-specific scalar
   separation.
3. `odd_normalized_proxy_reduced_fixed_sample_gap` and
   `even_normalized_proxy_reduced_fixed_sample_gap` handle the two reduced
   sectors (`m <= k` and `k < m`).
4. `odd_normalized_proxy_fixed_sample_extremizers` and
   `even_normalized_proxy_fixed_sample_extremizers` classify the central
   success counts, including all equality cases.
5. `hypergeomOptimalProxy_fixed_sample_extremizers` transfers the result to
   the paper's unnormalized optimal proxy for every `N >= 2`.
6. `odd_normalized_proxy_fixed_sample_gap`,
   `even_normalized_proxy_fixed_sample_gap`,
   `hypergeomOptimalProxy_fixed_sample_gap_odd`, and
   `hypergeomOptimalProxy_fixed_sample_gap_even` prove the explicit
   finite-size margins stated in the manuscript.

The dedicated audit file
`checks/goal_b_fixed_sample_axioms.lean` prints the dependencies of every
new public theorem. The output contains only Lean's standard foundational
axioms (`propext`, `Classical.choice`, and `Quot.sound`); there are no
`sorry`, `admit`, custom `axiom`, `unsafe`, or `native_decide` placeholders.
The generated umbrella audit in `checks/full_closure_axioms.lean` includes the
same declarations.

## Deliberate scope of the remaining value statements

The odd central value is represented in the paper by its exact finite-sum
one-variable optimization. The formalized theorem identifies its maximizing
success counts and proves the explicit off-center gaps; it does not introduce
an elementary closed form for arbitrary odd `N,m`, nor a uniqueness theorem
for the optimizing tilt. The one- and two-draw closed forms remain stated and
checked in the paper and computational certificate package.

## Reproducible commands

```text
lake build ExactHoeffding.GoalBFixedSample
lake build ExactHoeffding
lake env lean checks/goal_b_fixed_sample_axioms.lean
lake env lean checks/full_closure_axioms.lean
```
