# Display-formula audit: fixed-sample proxies and piecewise KL

> Historical source binding: this review was performed against the 17 October source snapshot `b1bb1e3df8d8b651c4872692a8b0f4424541b4e9b3a5576d39a2be485d26e23f` at commit `8b75977b138205c4ba402000b25d226d55994682`. Its original line numbers and display IDs are historical. For the current 240-display source binding, use `formal_status/display_formula_audit_current_20261018.md`; that report preserves the prior review scope and records the five current-source deltas.


Date: 2026-10-17. Read-only inspection of the active root working tree at
`/data/odd_proxy/github_publication/exact-hoeffding-constants`.
Base commit: `8b75977b138205c4ba402000b25d226d55994682`.
Frozen `submission/current/manuscript.tex` SHA256:
`b1bb1e3df8d8b651c4872692a8b0f4424541b4e9b3a5576d39a2be485d26e23f`.
The root tree contained pending integration changes; this report does not
assert those changes have passed a new build or axiom audit. No root source,
manuscript, or build output was changed for this review.

## Method and status vocabulary

The inventory below covers all 53 display blocks beginning on lines 1075–1596:
24 in B and 29 in A. The two-label `align` block at line 1330 has two separate
inequalities, so this means 54 formula units if that block is split. `D148`–
`D200` are document-order identifiers obtained by matching equation/align/
gather/multline environments and `\[...\]` blocks; they are not theorem IDs.
Inline mathematical assertions associated with those displays are audited
separately below. Definitions are not counted as proved theorems.

- **Definition**: the display fixes notation or a mathematical object.
- **Covered**: an actual statement of the required conclusion was located.
- **Parent proof**: an algebraic display occurs inside a proved result; the
  exact local proof step is identified instead of substituting a similar lemma.
- **Partial**: a stronger statement in the prose/display is not the conclusion
  of the located declarations. The proved portion and missing portion are stated.
- **Scope correction**: an ordinary mathematical expression in the frozen
  manuscript needs an explicit domain qualification; the valid branches have
  actual Lean interfaces.

All declaration names below have namespace **`ExactHoeffding`**. For example,
`hypergeomOptimalProxy_le_curvature` denotes the full declaration
`ExactHoeffding.hypergeomOptimalProxy_le_curvature`. A notation such as
`FiniteSupportLawData.rawUpperTail_eq_sum` denotes
`ExactHoeffding.FiniteSupportLawData.rawUpperTail_eq_sum`.
Paths in the tables are under `ExactHoeffding/`. Private declarations are
explicitly marked: their source names identify the proof location, not a
stable exported API. No declaration-existence checker can by itself certify
semantic agreement of a theorem with the paper.

Throughout B, the domain is `N≥2`, `0<k<N`, `0<m<N`. Throughout A, the
canonical domain is `3≤m≤k`, `2*k≤N`, `2*m<N` (hence `N≥7`). Nat complements
are interpreted as ordinary subtraction only under the corresponding legal
margin hypotheses.

## B: every displayed formula

| ID / location / label | Mathematical content | Exact declaration and source | Scope, endpoints, strictness |
|---|---|---|---|
| D148 L1075 `B:pmf` | Actual hypergeometric masses and true support | **Definition + Covered**: `hypergeomMass` / `Hypergeometric.lean`; `hypergeomSupport_iff`, `hypergeomMass_ne_zero_iff`, `hypergeomPMFValue_ne_zero_iff` / `Support.lean` | These are actual finite masses, not an abstract curve. Valid margins; support is `max(0,k+m−N)…min(k,m)`, including both endpoints. |
| D149 L1081 `B:variance` | Ordinary variance and sample scale M | **Covered**: `hypergeomTiltVariance_zero` / `ZeroTiltMoments.lean`; `hypergeom_cumulant2_complete` / `Cumulants.lean`. M is `individualMarginM` / `GoalBIndividualMargin.lean` | Exact formula for legal margins, including degeneracies in the general theorem; regrouping the factors into M is field algebra. |
| D150 L1087 `B:proxy` | Centered log-MGF and least quadratic proxy | **Definition**: `hypergeomCenteredLogMGF` / `HypergeometricLaplace.lean`; `optimalProxy`, `hypergeomOptimalProxy` / `OptimalProxy.lean` | Supremum is over nonzero real tilts. The extension at zero is a separate result, not built into this supremum definition. |
| D151 L1095 `B:W` | W and its parity formulas | **Definition + Parent proof**: `individualMarginW`; `individualMarginGap_ge_parityDelta_all` / `GoalBIndividualMargin.lean`, local `hW` in each parity branch | The even and odd `hW` identities expand Nat floor/complements using `omega`, casts, `field_simp`, `ring`. No separate public W-parity theorem. |
| D152 L1104 `B:C` | Actual optimal proxy ≤ sharp curvature constant | **Covered**: `hypergeomOptimalProxy_le_curvature` / `OptimalProxy.lean` | All legal margins; the definition `sharpCurvatureConstant` is exactly the displayed min/(4(N−1)). B avoids denominator N−1=0. |
| D153 L1110 `B:B` | Scaled Bernoulli proxy comparison | **Covered**: `hypergeomOptimalProxy_singleton_subhalf` / `SingletonOptimalProxy.lean`; `normalizedHypergeomProxy_inner_lt_bernoulli` / `OddHypergeomExtremizers.lean`; `normalizedHypergeomProxy_reduced_le_bernoulli` / `GoalBIndividualMargin.lean`; also `hypergeom_proxy_lt_scaled_bernoulli_subhalf` / `FinitePopulationBernoulliEnvelope.lean` | Singleton equality and strict `m≥2` are separately proved. Normalization is positive in B and explicitly cancelled. No equality is inferred merely from the nonstrict wrapper. |
| D154 L1121 `B:argmax` | All maximizing counts are the two nearest central counts | **Covered**: `hypergeomOptimalProxy_fixed_sample_extremizers` / `GoalBFixedSample.lean` | Full B domain. Its conclusion is domination plus the exact equality iff `k=N/2 ∨ k=N−N/2`; this is the finite argmax characterization. Even duplicate centers and N=2,3 are included. |
| D155 L1126 `B:delta` | Parity gap Δ | **Definition**: `individualMarginDelta` / `GoalBIndividualMargin.lean` | The display itself defines Δ. Positive denominators and numerator for admissible N,m give Δ>0. No separate exported unconditional `individualMarginDelta_pos` was located; see inline inventory. |
| D156 L1134 `B:strict` | Uniform quantified offcentral deficit | **Covered, with elementary composition**: `hypergeomOptimalProxy_fixed_sample_gap_even`, `hypergeomOptimalProxy_fixed_sample_gap_odd` / `GoalBFixedSample.lean`; central lower bound `hypergeomOptimalProxy_ge_variance` / `OptimalProxy.lean`; variance identity D149 | First inequality has the exact parity Δ. Middle strict inequality additionally uses Δ>0. Last is the actual zero-tilt variance lower bound. The current theorems export first inequality and extremizer strictness separately, not this four-term conjunction. |
| D157 L1143 `B:Bdeficit` | Cubic artanh lower bound and reciprocal bound | **Covered for displayed ≥/≤**: `real_artanh_cubic_lower`, `imbalanceFactor_cubic_upper` / `GoalBFixedSample.lean` | First theorem permits 0≤d<1; second 0<d<1. Conversion `logOdds d=2 artanh d` is proved inside the second. **Partial for the extra sentence claiming strict cubic inequality**: first theorem concludes only `d+d³/3≤artanh d`; its monotonicity proof uses nonnegative derivative and does not export `<`. |
| D158 L1164 `B:cap1` | First-branch actual proxy cap | **Covered**: `hypergeomOptimalProxy_reduced_first_branch`; `hypergeomOptimalProxy_le_individualMargin_cap` / `GoalBIndividualMargin.lean` | Reduced `mbar≤kbar`, offcentral `2*kbar<N`; second theorem transports both complements to the original actual proxy. |
| D159 L1169 unlabelled | Even first-branch cap and rational identity W−Δ | **Parent proof**: `even_imbalance_factor_offcenter_gap` / `GoalBFixedSample.lean`, locals `hfactor'`, `htarget`; `individualGap_even_first_algebra` (private) / `GoalBIndividualMargin.lean` | Uses imbalance d≥2/N and positive M. Equality of the rational expressions is proved with `field_simp; ring`; the actual-proxy conclusion is `hypergeomOptimalProxy_fixed_sample_gap_even`. |
| D160 L1176 unlabelled | Odd first-branch cap and rational identity W−Δ | **Parent proof**: `odd_imbalance_factor_offcenter_gap` / `GoalBFixedSample.lean`, locals `hfactor'`, `htarget`; `individualGap_odd_first_algebra` (private) / `GoalBIndividualMargin.lean` | Uses d≥3/N; actual-proxy conclusion is `hypergeomOptimalProxy_fixed_sample_gap_odd`. Rational identity is explicitly kernel-checked field algebra. |
| D161 L1185 `B:cap2` | Curvature cap in branch kbar<mbar | **Covered**: `hypergeomOptimalProxy_reduced_second_branch`; `hypergeomOptimalProxy_le_individualMargin_cap` / `GoalBIndividualMargin.lean` | Actual reduced masses, transposition/complementation. Strict branch condition implies which product is the min. |
| D162 L1190 `B:disc` | Exact discrete product difference; ≥1 even / ≥2 odd | **Parent proof**: `even_normalized_proxy_reduced_fixed_sample_gap`, `odd_normalized_proxy_reduced_fixed_sample_gap` / `GoalBFixedSample.lean`, locals `hid`, `hprod1`/`hprod2`, `hgap` | `ring` proves identity. Nat separation and parity prove the positive lower bound before multiplying/scaling the actual curvature theorem. |
| D163 L1196 unlabelled | Even second-branch intermediate chain with strict `1/[4(N−1)]>Δ` | **Partial / Parent proof**: `individualGap_even_second_algebra` (private) / `GoalBIndividualMargin.lean`, locals `hgap`, `hprod'`, `hsimple`; actual final deficit theorem as D156 | Current local `hsimple` proves **≥**, not the displayed strict `>`. The final required `S≤W−Δ` is proved. Do not label the literal strict intermediate inequality as an exported result or as a dependency of the final theorem. |
| D164 L1202 unlabelled | Odd second-branch intermediate chain through 7/[16(N−1)] and strict >Δ | **Partial / Parent proof**: `individualGap_odd_second_algebra` (private) / `GoalBIndividualMargin.lean`, locals `hgap`, `hpm`, `hgap'`, `hdelta`, `hsmall` | Exact lower estimate ≥7/[16(N−1)] is a local result; current `hdelta` gives Δ≤1/[8(N−1)], and `hsmall` uses nonstrict ≤. The final deficit is proved. The literal strict `>` and adjacent prose `Δ<1/[8(N−1)]` are not the conclusions of these locals. |
| D165 L1223 unlabelled (`B:individual`) | Two-branch G, G≥Δ, actual S≤W−G and first-branch monotonicity | **Definition + Covered**: `individualMarginGap`; `hypergeomOptimalProxy_le_individualMarginGap`; `individualMarginGap_ge_parityDelta_all` / `GoalBIndividualMargin.lean`; `individualMarginGap_strict_mono_reduced` / `IndividualMarginStrictMono.lean` | Exact actual-proxy formulas, full B domain, both noncentral exclusions. Strict monotonicity is proved after reduction `k≤N/2`, first-branch `mbar≤k1`, positive sample scale. Complement symmetry interprets it as monotonicity in |N−2k|. The new strict module closes the earlier nonstrict-only API. |
| D166 L1244 unlabelled (`B:even`) | Maximum M/4 at even central count, equal ordinary variance | **Covered**: `hypergeomOptimalProxy_balanced_marks` / `OptimalProxy.lean`; `hypergeomOptimalProxy_fixed_sample_extremizers_even` / `GoalBFixedSample.lean` | Central actual least proxy is exact sharpCurvatureConstant; `hypergeomTiltVariance_zero_balanced_marks` / `VarianceOptimality.lean` identifies it with M/4. All 0<m<N. |
| D167 L1258 unlabelled (`B:odd`) | Odd maximizing actual proxy strictly exceeds W | **Covered**: `hypergeomOptimalProxy_odd_center_gt_variance`, `odd_fixed_sample_max_strict` / `OddCentralStrict.lean`; fixed-sample extremizers D154 | All n>0 and 0<m<2n+1; reduction by sample complement handles m>n. This is a strict actual proxy theorem, not just the lower variance estimate. |
| D168 L1263 unlabelled | Odd-central finite-sum variational function including zero | **Definition + Covered actual sum; presentation truncation not exported**: `oddCentralFiniteTiltSum`, `oddCentral_logMGF_eq_finite_sum`, `oddCentral_actualProxy_zero_is_variance` / `GoalBOddVariation.lean`; `actualHypergeomProxy` / `RescaledActualProxy.lean`; optimizer `oddCentral_exists_nonzero_optimal_tilt_stationary` / `OddCentralOptimalTilt.lean` | Lean sum is range 0…m with actual masses; D148 proves that unsupported terms vanish. No separate theorem with exactly the manuscript's truncated lower/upper summation indices was found. The probability object and all nonzero/zero branches are the actual ones; a final explicit sum-restriction wrapper would close literal notation agreement. No uniqueness assumption. |
| D169 L1279 unlabelled | Odd-central third cumulant formula and positivity after m≤n reduction | **Covered formula + Parent proof of strictness**: `hypergeom_cumulant3_standard` / `Cumulants.lean`; `hypergeomOptimalProxy_odd_center_gt_variance` / `OddCentralStrict.lean` | Formula requires N≥3, legal margins. Positivity is after complement reduction m≤n; it is not asserted for unreduced m>n. Actual strictness proof uses the exact derivative of `rescaledProxyExtension` at zero and proves it nonzero, rather than assuming the cumulant sign. |
| D170 L1295 unlabelled (`B:small`) | Odd one-draw and one-from-end maximum closed form | **Covered by composition**: `hypergeomOptimalProxy_singleton_subhalf` / `SingletonOptimalProxy.lean`; `hypergeomOptimalProxy_fixed_sample_extremizers_odd` / `GoalBFixedSample.lean`; `hypergeomOptimalProxy_sample_complement` / `OptimalProxy.lean` | Set N=2n+1,k=n, n>0. Singleton formula simplifies to the displayed fraction; complement gives m=N−1. No standalone combined closed-form corollary was located. |
| D171 L1299 unlabelled (`B:small`) | Odd two-draw and two-from-end maximum closed form | **Covered by composition**: `hypergeomOptimalProxy_two_draw` / `OptimalProxy.lean`; `hypergeom_two_draw_odd_max_value` / `TwoDrawComparison.lean`; `odd_normalized_proxy_two_draw_value`, `odd_normalized_proxy_two_from_end_value` / `FixedSampleExtrema.lean`; D154 and sample complement | n≥2 (N≥5). Formula `(n+1)/(n−1)=(N+1)/(N−3)` uses positive denominators. The three-mass theorem is an exact proxy theorem; it is not being substituted for an unproved hypergeometric specialization. |

## A: every displayed formula

| ID / location / label | Mathematical content | Exact declaration and source | Scope, endpoints, strictness |
|---|---|---|---|
| D172 L1316 `A:domain` | Canonical domain | **Definition / hypotheses** | Lean Nat API uses `3≤m`, `m≤k`, `2*k≤N`, `2*m<N`; N≥7 follows. Real rate-comparison APIs use the corresponding real inequalities. |
| D173 L1320 unlabelled | Parameters p,q,μ,M,a,d | **Definition**: `envelopeM`, `envelopeScale` / `RiccatiCertificates.lean`; centered mean and fraction are explicit lets in `hypergeom_kl_riccati_data` / `PiecewiseKLFull.lean` | Positivity/nonzero denominators follow from D172 in actual proofs. No theorem is needed merely to define p,q,μ,d. |
| D174a L1330 `A:PB` | Actual tilted variance ≤ u(m−u)/m | **Covered**: `canonical_hypergeom_variance_le_binomial_envelope` / `PiecewiseKLEndToEnd.lean`; second component of `hypergeom_kl_riccati_data` / `PiecewiseKLFull.lean` | Valid all real tilts on canonical domain. Uses actual Bernoulli real-root representation, via `hypergeom_tilted_true_support_mean_variance_bound` / `BernoulliMGFGeometry.lean`; degree is m after canonical true-support lemma. |
| D174b L1330 `A:barrier` | Actual tilted variance ≤ P and exact contact | **Covered**: `hypergeomTiltVariance_barrier_canonical` / `HypergeometricBarrier.lean`; first component `hypergeom_kl_riccati_data` / `PiecewiseKLFull.lean` | Actual canonical distribution, all t, equality iff t=0. Mean map strictness converts t=0 to u=μ. No variance comparison is assumed as an external oracle. |
| D175 L1343 unlabelled | Binary KL with continuous endpoint values | **Definition + Covered endpoints**: `bernoulliKL`, `bernoulliKL_zero_endpoint`, `bernoulliKL_one_endpoint` / `BernoulliKL.lean`; `bernoulliKL_continuous` / `PiecewiseKLFull.lean` | 0<p<1, θ∈[0,1]. Totalized `Real.log` in definition is reconciled with the ordinary continuous endpoints by these statements. |
| D176 L1355 unlabelled (`A:integration`) | Definition of two-sided envelope integral; true I≥J and strictness | **Definition + Covered**: `FiniteSupportLawData.rawLegendreRate_ge_meanEnvelopeRight`, `...Left`, `...gt_meanEnvelopeRight`, `...gt_meanEnvelopeLeft` / `FiniteSupportLawIntegration.lean`; exact mean-interval strict version `...gt_meanEnvelopeRight_of_interval`, `...Left_of_interval` / `FiniteSupportLawMeanGap.lean` | Actual finite weighted law, mass total one, distinct positive endpoint atoms and no other endpoint index; arbitrary finite law can be represented by its distinct support values. Q only continuous and positive on the **open support**, true variance≤Q for all tilts. Interior target includes the mean for nonstrict comparison. Finite endpoint limits handled by `...rawLegendreRate_ge_meanEnvelopeRight_endpoint`, `...Left_endpoint` / `FiniteSupportLawEndpointIntegration.lean`; strict endpoint interval versions by `...rawLegendreRate_gt_meanEnvelopeRight_endpoint_of_interval`, `...Left_endpoint_of_interval` / `FiniteSupportLawRawEndpointStrict.lean`. |
| D177 L1363 unlabelled | Actual upper/lower finite-law tails ≤ exp(−JQ) | **Covered**: `FiniteSupportLawData.rawUpperTail_le_exp_neg_meanEnvelope`, `...rawLowerTail_le_exp_neg_meanEnvelope`; exact event identities `...rawUpperTail_eq_sum`, `...rawLowerTail_eq_sum` / `FiniteSupportLawIntegration.lean` | Upper μ≤v<h; lower l<v≤μ. Endpoints with finite one-sided limits: `...rawUpperTail_le_meanEnvelope_endpoint`, `...rawLowerTail_le_meanEnvelope_endpoint` / `FiniteSupportLawEndpointIntegration.lean`; strict interval endpoint wrappers in `FiniteSupportLawRawEndpointStrict.lean`. Outside support JQ is not defined; these formulas are read on the declared support domain. |
| D178 L1386 `A:IP` | Scaled KL rate definition and curvature | **Definition + Covered derivatives**: `scaledKLRate` / `PiecewiseKLFull.lean`; `scaledKLRate_hasDerivAt`, `scaledKLSlope_hasDerivAt`, `scaledKLSlope_hasDerivAt_canonical`, `scaledKL_denominator_identity` / `PiecewiseKLComparison.lean` | Actual formula valid θ∈(0,1), which is proved even at v=0,m under A-domain; derivative is 1/P. Zero value/slope: `scaledKLRate_contact_at_mean` / `BennettMeanEndpoint.lean`. |
| D179 L1391 unlabelled | Identity 1−am/M=N(m−1)/((N−2)(N−m))>0 | **Parent proof**: `envelope_scaled_mark_lt_one` / `PiecewiseKLFull.lean` | Exact field identity appears inside its `field_simp` proof as `(N−2)(N−m)−(N−2m)(N−1)=N(m−1)`. Public conclusion is am/M<1. `scaledKL_argument_mem_Ioo` proves θ∈(0,1) on closed support. |
| D180 L1396 `A:IB` | Ordinary binomial KL rate | **Definition**: `binomialKLRate` / `PiecewiseKLFull.lean`; derivatives `binomialKLRate_hasDerivAt`, `binomialKLSlope_hasDerivAt` / `PiecewiseKLComparison.lean` | Endpoints use continuous KL values, not finite maximizing Bernoulli tilts. This rate is **not** the actual hypergeometric Legendre rate `hypergeomKLRate`. |
| D181 L1401 unlabelled | All-tilt actual scaled Bernoulli log-MGF bound | **Covered**: `hypergeom_laplace_envelope`, `hypergeom_laplace_envelope_equality_iff` / `LaplaceEnvelopeTheorem.lean` | A-domain, all real t, equality exactly t=0; strict at every nonzero tilt. Fenchel optimizer/formula: `scaledBernoulliMean_at_fenchel`, `scaledBernoulliLogLaplace_at_fenchel` / `PiecewiseKLFull.lean`; endpoint Bernoulli Fenchel upper inequalities: `bernoulli_fenchel_upper_zero`, `...one` / `BernoulliKL.lean`. |
| D182 L1412 unlabelled | c,h,b | **Definition**: `klSwitchC`, `klSwitchH`, `klSwitchB` in piecewise-KL definitions | `klSwitchC_pos`, `klSwitchB_pos` / `PiecewiseKL.lean` establish the strict assumptions needed for the roots, not an extra premise supplied by the caller. |
| D183 L1417 `A:switch` | Quadratic crossing roots and location | **Definition + Covered**: `varianceSwitchRootMinus`, `varianceSwitchRootPlus`, `varianceSwitchMinus`, `varianceSwitchPlus`; `kl_switching_points_full_domain`, `kl_quadratic_envelope_le_binomial_iff` / `PiecewiseKL.lean` | Full A-domain. Proves 0<r−<μ<r+<m, and exact comparison regions including contacts. |
| D184 L1423 `A:J` | Tangent-stitched piecewise J | **Definition + Covered contacts, partial smoothness prose**: `canonicalPiecewiseRate`, `outerKLRate` / `PiecewiseKLFull.lean`; `piecewiseKLRate` / `PiecewiseKL.lean`; `piecewiseKLRate_left_contact`, `...right_contact` / `PiecewiseKL.lean`; `canonicalPiecewiseRate_continuous` / `PiecewiseKLFull.lean` | Branch expressions are exact definitions. **No `ContDiffOn ℝ 2`/equivalent theorem establishing the manuscript's twice-continuously-differentiable assertion across the two switches was located.** Branch derivatives and value contacts alone are not an exported C² result. |
| D185 L1435 `A:strict` | Actual I>J>IB, J≥IP, with exact IP contact region | **Covered**: `hypergeom_piecewise_kl_end_to_end`, `hypergeomKLRate_strict_piecewise` / `PiecewiseKLStrict.lean`; `canonicalPiecewiseRate_strict_improves_binomial`, `canonicalPiecewiseRate_quadratic_comparison` / `PiecewiseKLComparison.lean` | Actual hypergeometric `hypergeomKLRate`, entire closed support, v≠μ. Exact J=IP iff r−≤v≤r+; strict outside. The word `quadratic` in the last declaration refers to the quadratic **variance envelope P**, not the uniform Gaussian rate in D192. |
| D186 L1443 unlabelled | Explicit positive expansion of c | **Covered**: `klSwitchC_expansion`, `klSwitchC_pos` / `PiecewiseKL.lean` | Exact denominator hypotheses and A-domain positivity. No numerical or CAS certificate is substituted. |
| D187 L1477 unlabelled align | Four symmetric binomial KL rates | **Definition**: `binomialKLRate`, `fourBinomialKLRate2`, `...3`, `...4` / `PiecewiseKLFourRates.lean` | Current canonical range is A-domain. The displayed transformations are definitions, not a general comparison theorem over all possible unordered margins. |
| D188 L1485 unlabelled | Reciprocal-second-derivative envelopes B1…B4 | **Definition + Parent proof**: `fourBinomialEnvelope1`…`4`; private `rate2_hasDerivAt`, `rate2_slope_hasDerivAt`, `rate3_hasDerivAt`, `rate3_slope_hasDerivAt`, `rate4_hasDerivAt`, `rate4_slope_hasDerivAt` / `PiecewiseKLFourRates.lean`; R1 derivatives as D180 | Second-derivative identities are interior statements. At support endpoints Bernoulli slopes can diverge; rate comparison is instead extended by continuity, not by falsely claiming finite endpoint derivatives. |
| D189 L1491 unlabelled align | Three exact envelope differences and signs | **Parent proof**: private `envelope2_gap`, `envelope3_gap`, `envelope4_gap` / `PiecewiseKLFourRates.lean` | Algebra identities are used inside the corresponding `fourRate*_lt_R1` proofs; nonnegative coefficients follow from m≤k≤N/2 and 2m<N. Public `fourBinomialKLRate_comparisons` exports strict/equality classification; it is not merely an envelope comparison. |
| D190 L1504 unlabelled | Parity κN, uniform proxy V*=MκN/4 | **Definition + Covered uniform coefficient**: `paritySharpConstant`, `exact_finite_exchangeability_constants` / `ExactParityConstants.lean`; `odd_normalized_proxy_all_upper` / `OddHypergeomExtremizers.lean`; `normalizedHypergeomProxy_universal_upper` / `NormalizedProxy.lean` | Conversion between normalized proxy and κN is positive-factor algebra. Individual Bernoulli Mβ≤V* requires the Bernoulli fraction monotonicity and lattice center, rather than actual proxy≤V* alone; see D192 missing wrapper. |
| D191 L1512 unlabelled | β with balanced value | **Definition + Covered**: `bernoulliSharpBeta`, `bernoulliSharpBeta_eq_formula`, `bernoulliSharpBeta_half` / `BernoulliOptimal.lean`; `bernoulli_sharp_quadratic_bound`, `...optimal` same file | All p∈[0,1] in whole-domain theorem; in A-domain 0<p≤1/2. Endpoints p=0,1 are explicitly treated in that module but not needed in A. |
| D192 L1517 `A:quadratic` | J≥IP≥x²/(2Mβ)≥x²/(2V*) and equality descriptions | **Partial**: first inequality and exact central equality region are `canonicalPiecewiseRate_quadratic_comparison` / `PiecewiseKLComparison.lean`. `bernoulli_sharp_quadratic_bound` / `BernoulliOptimal.lean` and `bernoulli_fenchel_identity` / `BernoulliKL.lean` provide ingredients, not the stated rate-conjugation theorem. | **No current declaration was located whose conclusion is the middle IP≥x²/(2Mβ) rate inequality, the all-lattice Mβ≤V* wrapper, or the nonzero θ=1−p/final odd-center equality classification for this rate chain.** `bernoulliSharpBeta_le_quarter`, `...strictMono_subhalf` / `BernoulliSharpBounds.lean` and `bernoulli_quadratic_strict_away_contacts` / `JointBinomialOptimizer.lean` are relevant ingredients only. Must not call the complete displayed chain kernel closed by citing the first inequality. |
| D193 L1532 unlabelled | Fourth-order expansion of IP at μ, remainder O(x⁵) | **Not located** | No scaled-KL rate Taylor theorem with these coefficients/remainder was found. `hypergeom_logMGF_taylor4_isLittleO` / `LogMGFTaylor.lean` is a theorem about the **actual log-MGF as a function of tilt**, not about IP as a function of target mean, so it does not cover this display. A Taylor/cumulant module for ψ cannot be mapped here. |
| D194 L1549 unlabelled | P(μ±s)<v0+s; strict IP>Bennett, then Bernstein | **Parent proof + Covered rates**: private `scaledKLRate_strict_bennett_right`, `...left`, public `hypergeomBennettRate_lt_scaledKLRate_upper`, `...lower`, `hypergeomBennettRate_lt_canonicalPiecewiseRate_upper`, `...lower` / `HypergeomBennettBernstein.lean`; `bennettKernel_ge_bernsteinKernel`, `bernsteinRate_le_bennettRate_kernel`, `hypergeomBernsteinRate_lt_canonicalPiecewiseRate_upper`, `...lower` / `BernsteinKernel.lean` | Supported nonzero deviations, including v=0,m; real scalar identities appear in the private comparisons and are used in the integrated proof. `hypergeomBennettBernsteinRates_at_mean` / `BennettMeanEndpoint.lean` gives zero endpoint contact. No strict assertion at zero. |
| D195 L1563 unlabelled (`A:factorial`) | Optimized factorial-moment bound Fd | **Definition**: `finiteBinomialMoment`, `finiteFactorialCandidate`, `finiteFactorialBound` / `FactorialChernoff.lean` | Finite set of arbitrary natural-valued outcomes with nonnegative weights. Denominators choose(d,j)>0 for every admissible 0≤j≤d. The generic API even permits d=0. |
| D196 L1567 unlabelled | Actual tail≤Fd≤exact positive-tilt Chernoff infimum | **Covered**: `finiteIntegerTailMass_le_factorialBound`, `finiteFactorialBound_le_chernoff_tilt`, `finiteFactorialBound_le_chernoff_inf` / `FactorialChernoff.lean` | General finite natural-valued law. No binomial approximation or KL rate is used. All d, including outside support and at mean; the bounded-support hypothesis is represented by an actual finite sum. Weights need only be nonnegative; normalization is unnecessary for the algebra. Direction is factorial bound **≤** exact Chernoff infimum. |
| D197 L1572 unlabelled | Hypergeometric candidate as falling-factorial ratio | **Scope correction**: `hypergeom_factorial_candidate_formula_of_degree_le_population`; `hypergeom_factorial_candidate_eq_zero_of_population_lt_degree` / `FactorialChernoffExact.lean`; exact binomial moments `hypergeom_binomialMoment` / `FactorialChernoff.lean` | Ordinary fraction valid for 0≤j≤d and **j≤N**; no d≤m restriction is needed for this identity. For j>N the actual moment candidate is zero; the displayed ordinary fraction has denominator zero. Example within A-domain: N=7,k=m=3,d=j=8 gives actual candidate 0 and an ordinary 0/0 RHS. Lean total division is not a paper convention. |
| D198 L1578 unlabelled | Actual upper tail≤Fd≤exp(−actual I(d))<exp(−J(d)); reflected lower tail | **Covered on corrected support scope**: `hypergeomFactorialBound_le_exp_neg_KLRate`, `hypergeomFactorialBound_lt_exp_neg_piecewiseRate` / `FactorialChernoffExact.lean`, plus generic actual tail≤F; `hypergeom_lower_factorial_chernoff_end_to_end` / `FactorialChernoffLower.lean` | Upper requires μ<d≤m; d=m included. `hypergeomKLRate` is actual log-MGF Legendre rate, **not binomial KL**. Lower applies to actual reflected values m−i with the original masses and gives original 0≤d<μ, including d=0. No invalid canonical complement assumption is used. The frozen sentence only says d>μ: for d>m its J(d) is outside the declared [0,m] domain. Correct exterior branch is exact zero tail=F=Chernoff inf, see below. |
| D199 L1586 unlabelled proof | Binomial-basis PGF comparison | **Parent proof**: `finiteFactorialBound_le_chernoff_tilt` / `FactorialChernoff.lean`, locals `hlow`, `hpartial`, `hprod`; `finiteBinomialMoment_truncated_pgf`, `choose_binomial_polynomial_trunc_le` same file | Exact finite identity/inequality with z=eᵗ−1≥0. Finite truncation j≤d is bounded by the full PGF termwise and then normalized. No analytic infinite-series interchange is assumed. |
| D200 L1596 unlabelled | Valid ceiling minimizer j*, tie and endpoint | **Covered**: `hypergeomFactorialIndex_denominator_pos`, `...numerator_pos`, `...mem`, `hypergeomFactorialValue_succ_le_iff`, `hypergeomFactorialValue_index_min`, `hypergeomFactorialBound_eq_ceiling_candidate`, `hypergeomFactorialValue_succ_eq_of_integral_cutoff`, `hypergeomFactorialBound_eq_adjacent_candidates`, `hypergeomFactorialIndex_eq_endpoint` / `FactorialMinimizer.lean` | Strict supported upper threshold, d>0, d≤m,k, k+m≤N, km<Nd. All apply under A-domain. Membership is 1≤j*≤d. Ratio test requires j+1≤d; integer cutoff ties both admissible neighbors and both attain F. At d=min(k,m), j*=d. No claim that j* is unique or applies below/at mean. |

## Associated inline statements and exact gaps

1. **Continuity, zero limit and infinite-tilt tails in B.**
   `hypergeom_centered_quadratic_limit` / `VarianceOptimality.lean`,
   `hypergeomProxyQuotient_continuous`, `hypergeomProxyQuotient_tendsto_atTop`,
   `hypergeomProxyQuotient_tendsto_atBot` / `ProxyQuotient.lean` prove the
   continuous extension and canonical tilt limits. `actualHypergeomProxy_eq_hypergeomProxyQuotient`
   and complement/transpose theorems in `GoalBOddGlobal.lean` transport to all
   actual legal nondegenerate margins. `actualHypergeomProxy_tail_bound` /
   `ActualProxyTail.lean` also supplies an all-margin upper tail bound.
   The zero value agrees with ordinary variance through D149, not a new definition.
2. **B complement invariance.** Actual statements
   `hypergeomOptimalProxy_success_complement`,
   `hypergeomOptimalProxy_sample_complement`, `hypergeomOptimalProxy_transpose`
   / `OptimalProxy.lean` are exact, legal-margin symmetries.
3. **B1 is closed as an actual proxy result.** D165 has the full G formula,
   both branches, G≥Δ, complement reduction and strict first-branch
   monotonicity. Do not replace it with only parity-uniform gap D156.
   A new public Δ>0 and four-term-chain wrapper would improve exact statement
   coverage, though positivity is elementary and extremizer strictness is
   already proved. Literal proof-only strict constants in D163–164 and the
   strict cubic sentence in D157 remain separate coverage items.
4. **B2 optimizer and boundary status.**
   `oddCentral_exists_nonzero_optimal_tilt_stationary` /
   `OddCentralOptimalTilt.lean` proves existence of a finite nonzero attaining
   tilt for n>0,0<m<2n+1. `oddCentral_every_nonzero_maximizer_stationary`
   proves the equation for **every** maximizing nonzero tilt;
   `oddCentral_nonzero_maximizer_realizes_optimalProxy` /
   `GoalBOddVariation.lean` identifies the actual least proxy. No uniqueness
   premise or conclusion is present. m=0,N are outside the B proposition;
   zero tilt is excluded from attaining the odd nondegenerate maximum by the
   strict actual variance gap. D168 still needs an exported exact
   support-truncation equality if every printed summation limit is to appear
   literally in a Lean theorem.
5. **B proof Taylor sentence.**
   `hypergeom_logMGF_taylor4_eq`, `hypergeom_logMGF_taylor4_isLittleO`,
   `hypergeom_logMGF_taylor4_lagrange` / `LogMGFTaylor.lean` prove actual ψ
   coefficients and remainder before centering/dividing by t².
   `OddCentralStrict.lean` instead uses
   `rescaledProxyExtension_deriv_tilt_zero` / `RescaledMixedDerivative.lean`
   plus `exists_proxy_gt_zero_tilt_of_deriv_ne_zero` (private) to prove the
   actual strict conclusion. No exported theorem with the exact displayed
   proxy expansion `W+κ3*t/3+O(t²)` was found; its parent strict theorem
   has a valid independent kernel proof.
6. **A support and mean map.**
   `hypergeomMass_pos_of_margins`,
   `hypergeomTiltMean_mem_Ioo_of_margins`,
   `hypergeomTiltVariance_pos_of_margins` /
   `HypergeometricODEMargins.lean`, positive-variance derivative and the
   endpoint limits / `HypergeometricEndpoints.lean` establish the actual
   mean-coordinate setting. Generic actual-law monotonicity is
   `FiniteSupportLawData.rawTiltMean_strictMono` /
   `FiniteSupportLawRawCalculus.lean`; `finiteSupportMeanInverse_unique` /
   `FiniteSupportMeanEnvelope.lean` proves existence and uniqueness of the
   inverse at every strictly supported mean. There is no need to postulate
   an onto mean map as an independent hypergeometric assumption.
7. **A1 endpoint normalization.** The finite-law interfaces assume distinct
   support values at both extremal indices. An arbitrary finite-support
   probability measure is represented canonically by one atom per value;
   endpoint rate is then exactly −log of the endpoint mass.
   `FiniteSupportLawData.rawLegendreRate_hi`, `...lo` /
   `FiniteSupportLawMeanGap.lean` state those actual endpoint formulas.
   Open-support continuity/positivity and finite one-sided J limits are
   exactly the manuscript assumptions, not endpoint positivity of Q.
   Strict interval conditions are now direct raw-coordinate wrappers for
   both interior and support-endpoint targets. Their new code was inspected
   only; this report does not report an independent compilation result.
8. **A four-rate equality classification.**
   `fourBinomialKLRate_comparisons` / `PiecewiseKLFourRates.lean` proves
   R2≤R1 with equality iff v=μ or k=m; R3≤R1 and R4≤R1 each have equality
   iff v=μ. `fourBinomialKLRateMax_eq_R1` and
   `canonicalPiecewiseRate_strict_improves_fourBinomialKLRateMax` in the same
   file include support endpoints and the strict v≠μ condition. The
   canonical ordering hypotheses are essential; this report does not
   assert R1 dominates after arbitrary unnormalized margin permutations.
9. **A2 complete valid exterior branch.**
   `hypergeom_factorial_chernoff_support_exterior_end_to_end` /
   `FactorialSupportExterior.lean` proves, for any legal N,k,m including
   degeneracies and integer d>min(k,m), that actual upper-tail mass,
   optimized factorial bound and exact nonnegative-tilt Chernoff infimum
   all equal zero. Its proof uses actual support, nonnegative candidates,
   and `hypergeomChernoffCandidate_arbitrarily_small_of_supportUpper_lt`.
   It does not falsely identify the unbounded real sSup with an extended
   real infinity or evaluate the piecewise J outside its declared domain.
10. **A2 ties, mean and degenerate thresholds.** Generic D196 is unrestricted
    in d. A-domain strict KL D198 excludes the mean; equality/at-mean does
    not inherit `< exp(−J)`. The explicit minimizing ceiling D200 is only
    for supported strict upper thresholds. Endpoint d=min(k,m) and
    admissible integral ties are now direct actual-F theorems, while d
    above support has the zero result in item 9. Zero/all-success or
    zero/full-sample laws fall under the generic finite-sum comparisons
    and the exterior theorem, not A-domain strictness or D200.
11. **A quadratic section remains a separate gap.** D192's first inequality
    is closed. Conjugating the sharp Bernoulli quadratic bound to IP,
    the discrete parity bound on Mβ, and exact rate equality conditions
    have no located final theorem. These are not theorems about the
    actual ψ proxy merely because they use the same constant. The
    fourth-order **rate** expansion D193 is also not the ψ Taylor result.
12. **A smoothness section remains a separate gap.** C² across the two
    switches in D184 has not been established by an exact declaration.
    Continuity and individual branch derivatives are present. To close
    the prose claim, glue first and second derivatives at both switches
    using P=B there, on the support interior. Do not cite global
    `Continuous canonicalPiecewiseRate` as if it concluded C².

## Explicit scope issues in the frozen manuscript

The two substantive domain omissions already documented in
`formal_status/a2_factorial_denominator_audit.md` remain:

- D197 needs `j≤N` for an ordinary falling-factorial fraction, or a separate
  explicit zero branch when `j>N`. With N=7,k=m=3,d=j=8, the ordinary RHS
  is undefined. This does not refute the actual optimized-factorial or
  exact-Chernoff inequalities.
- D198 needs `d≤m` in A-domain before using I(d),J(d) as the supported
  rate functions. With N=7,k=m=3,d=4, d>μ but J(4) is outside the stated
  domain [0,3], even though all j≤d satisfy j≤N. The exterior correct
  result is tail=F=exact Chernoff inf=0. This is distinct from the first
  denominator issue.

No manuscript edit is made here. Closing the valid mathematical branches
in Lean does not authorize a claim that the literal unqualified displays
are already exact whole-domain statements.

## Required follow-up before a display-complete claim

1. Export and kernel-check the D192 rate chain and its actual equality
   conditions, with the parity/lattice Bernoulli coefficient comparison.
2. Prove D193's rate-variable Taylor expansion with the specified O(x⁵)
   remainder; do not substitute an MGF Taylor theorem.
3. Prove C² gluing of J at r− and r+, or explicitly scope the existing
   theorem correspondence to its currently proved continuity/branch facts.
4. Prove/export the strict scalar artanh sentence D157. If literal proof
   display coverage is required, export the strict elementary intermediate
   comparisons D163–164 and exact truncated sum in D168 as well.
5. Reconcile the two frozen A2 statement-domain omissions before claiming
   semantic coverage of every displayed ordinary formula.
6. Run the single integrated pinned-toolchain build, trusted-kernel audit
   and allowed-axiom audit on the final merged tree. No new compilation
   or axiom result is claimed by this source-only audit.
