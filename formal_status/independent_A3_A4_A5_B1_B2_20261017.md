# Independent scope review: A3, A4, A5, B1, B2

Reviewed read-only at `/data/odd_proxy/github_publication/exact-hoeffding-constants`.
Snapshot HEAD: `8b75977b138205c4ba402000b25d226d55994682`.
Frozen manuscript SHA256: `b1bb1e3df8d8b651c4872692a8b0f4424541b4e9b3a5576d39a2be485d26e23f`.
Date: 2026-10-17 UTC. This review checks source types and proof scope; it runs no compiler or axiom audit and does not modify the reviewed tree.

## A3: four binomial KL rates (manuscript lines 1474–1500)

`PiecewiseKLFourRates.lean` defines the three transformed rates and all four reciprocal-curvature envelopes exactly as displayed in the manuscript. `bernoulliKL` has parameter-first arguments, so the Lean definitions agree with the paper's `D(argument || parameter)` convention.

- `fourBinomialKLRate_comparisons`: for real `N>0`, `m>0`, `m≤k≤N/2`, `2m<N`, and every `v∈[0,m]`, proves `R2,R3,R4≤R1`. It proves the stronger equality classifications: `R2=R1` iff `v=mk/N` or `k=m`; `R3=R1` and `R4=R1` iff `v=mk/N`.
- `fourBinomialKLRateMax_eq_R1`: the maximum of all four displayed rates is exactly R1 on the same closed interval.
- `canonicalPiecewiseRate_strict_improves_fourBinomialKLRateMax`: adds `m≥3`, and proves strict improvement by J at every supported `v≠mk/N`, including `v=0,m`.
- Private lemmas `rate2_hasDerivAt`, `rate3_hasDerivAt`, `rate4_hasDerivAt` and their slope counterparts establish the displayed derivative and reciprocal-curvature formulas on their differentiability domains; `envelope2_gap`, `envelope3_gap`, `envelope4_gap` prove the three displayed algebraic differences. Center values and slopes vanish by the exact rational-argument identities and `bernoulliFenchelTilt p p=0`.

The paper's integer domain `N≥7`, `3≤m≤k≤floor(N/2)`, `2m<N` is contained in these hypotheses. No unsupported endpoint or strictness extension was found. The analytic rate-comparison declarations do not postulate a probability bound: actual hypergeometric probability bounds come from `PiecewiseKLFull.lean` and A5 below. Their combination also yields each of the weaker four classical exponents.

## A4: exact-variance Bennett/Bernstein (lines 1542–1558)

The actual module is `HypergeomBennettBernstein.lean`; no `BennettBernsteinCorrect.lean` exists in this reviewed tree.

- `hypergeomBennettRate_lt_canonicalPiecewiseRate_upper`: integer canonical domain `3≤m≤k`, `2k≤N`, `2m<N`, and `μ<v≤m`.
- `hypergeomBennettRate_lt_canonicalPiecewiseRate_lower`: same parameter domain and `0≤v<μ`.
- `hypergeomBennettRate` uses exactly `v0=M*(k/N)*(1-k/N)` and absolute raw displacement `|v-μ|`, as in the paper. Thus both support endpoints are covered and zero displacement is excluded from the strict statement.
- The proof establishes the paper's stronger intermediate strict comparison directly with the scaled rate IP, using private `scaledKLRate_strict_bennett_right` / `scaledKLRate_strict_bennett_left` and local `hb'`; it then composes with `IP≤J`. This intermediate comparison is proved, rather than assumed, but has no separate public hypergeometric-IP wrapper.
- `bennettKernel_ge_bernsteinKernel`, `bernsteinRate_le_bennettRate_kernel` in `BernsteinKernel.lean`, and `bernsteinRate_le_bennettRate` in `HypergeomBernsteinComparison.lean`, prove the standard nonnegative-displacement kernel comparison.
- `hypergeomBernsteinRate_lt_canonicalPiecewiseRate_upper` / `_lower` in `BernsteinKernel.lean` give strict J comparisons on the same closed supported tails.
- `bennettRate_contact_at_zero`, `scaledKLRate_contact_at_mean`, `hypergeomBennettRate_at_mean`, `hypergeomBennettBernsteinRates_at_mean` in `BennettMeanEndpoint.lean` cover the zero values and derivative contacts at the center; the Bernstein and J center values are also in `hypergeomBernsteinRate_at_mean`.

No mathematical range gap was found. Packaging issue at the time of review: `BennettMeanEndpoint.lean` is present and imported by the umbrella but is still untracked in the reviewed main working tree. It must be included in the eventual commit/archive for a clean-checkout reproduction.

## A5: integer/two-sided events (lines 1465–1471)

`ManuscriptIntegerTails.lean` defines all three probabilities as indicator sums against the actual normalized hypergeometric masses, not as abstract tail functions supplied by a caller.

- `hypergeomUpperDeviationMass_eq_ceil_tail` and `hypergeomLowerDeviationMass_eq_floor_tail` prove the exact ceiling/floor event conversions.
- `hypergeomTwoSidedDeviationMass_eq_sum` proves the disjoint upper/lower decomposition for `x>0`.
- `hypergeom_integer_upper_deviation_piecewise_kl` and `hypergeom_integer_lower_deviation_piecewise_kl` prove the exact displayed cutoff formulas: upper threshold above m gives zero, lower threshold below zero gives zero; equality at support endpoints is included.
- `hypergeom_integer_two_sided_deviation_piecewise_kl` proves the sum capped by one, using actual mass normalization.

All three bounds use precisely the canonical integer domain and `x>0`. The closed tail inputs `hypergeom_upper_tail_piecewise_kl` / `hypergeom_lower_tail_piecewise_kl` in `PiecewiseKLFull.lean` explicitly handle v=m and v=0. No gap found.

## B1: individual-margin certificate (lines 1219–1238)

`individualMarginM`, `individualMarginW`, `individualMarginGap`, and `individualMarginDelta` in `GoalBIndividualMargin.lean` agree with the paper's M, W, G and parity-dependent Delta. The G branch condition is exactly `min(m,N-m)≤min(k,N-k)`; branch one uses the original symmetric sample scale M, and branch two uses the reduced population margin product.

- `hypergeomOptimalProxy_le_individualMarginGap`: for every `N≥2`, `0<k,m<N`, excluding both central success counts, proves actual `S≤W-G`.
- `individualMarginGap_ge_parityDelta_all`: on the same full integer domain proves `G≥Delta`, with both parity branches. The noncentral domain is empty for N=2,3, as stated in the paper.
- The proof invokes actual success/sample-complement proxy identities, not a hypothesis that the rates respect complement reduction.
- `individualMargin_first_branch_gap_mono` and `_mono_reduced` prove nondecreasing dependence on imbalance.

Precision qualification: the paper says G “increases” with `|N-2k|`. If this word means nondecreasing, the named declarations match exactly. If it is intended as strictly increasing at distinct imbalances, the existing public declarations prove only `≤`, although strictness follows from the explicit positive-M rational formula. There is no public strict-monotonicity theorem in this module. This is a declaration-strength nuance, not a defect in either G inequality.

## B2: odd central finite-sum optimization (lines 1256–1290)

- `oddCentral_logMGF_eq_finite_sum` identifies the actual centered CGF with the logarithm of the finite hypergeometric sum. The Lean range `0..m` agrees with the paper's true-support summation because support-external masses vanish; natural subtraction is only used inside this bounded range.
- `oddCentral_actualProxy_zero_is_variance` supplies the zero-tilt value. The variance formulas and positive fixed-m normalization identify it with W.
- `odd_fixed_sample_max_strict` in `OddCentralStrict.lean` gives the complete central-success-count maximum classification and strict gap above the variance benchmark; its normalized proxy differs from S by a fixed positive scalar independent of k.
- `oddCentral_nonzero_maximizer_stationary` and `oddCentral_every_nonzero_maximizer_stationary` prove `t*ψ'(t)=2*ψ(t)` for every nonzero global maximizer, with no uniqueness assumption.
- `oddCentral_nonzero_maximizer_realizes_optimalProxy` identifies any such maximizer with the actual optimal proxy.
- `oddCentral_exists_nonzero_optimal_tilt_stationary` in `OddCentralOptimalTilt.lean` proves existence and contact for every `n>0`, `0<m<2n+1`. It obtains an actual global maximum from `actualHypergeomProxy_exists_global_max` and excludes zero by `hypergeomOptimalProxy_odd_center_gt_variance`. Its exact existential type records equality to the actual supremum; global maximality follows immediately from `actualHypergeomProxy_le_optimalProxy`.

The domain exactly matches N=2n+1≥3 and 1≤m<N. No m=0,N or N=1 nondegenerate claim is made. Zero is handled by continuous completion; the two infinite tilt ends are handled by the global-existence proof. No uniqueness or positive-sign claim is made for arbitrary fixed m. No gap found.

## Integration notes

1. Include the currently untracked `BennettMeanEndpoint.lean` in the final commit/archive.
2. If strict monotonicity is intended in B1, expose its strict rational-form consequence; otherwise the existing nondecreasing statement is already present.
3. A4's direct IP-vs-Bennett result is present inside proved private lemmas and the actual hypergeometric proof. A public direct-IP wrapper is optional API completeness, not a missing mathematical proof.
4. No new module, compile job, axiom audit, manuscript edit, or root-tree mutation was performed by this review.
