# Frozen manuscript: display-formula audit, main proof and appendices

> Historical source binding: this review was performed against the 17 October source snapshot `b1bb1e3df8d8b651c4872692a8b0f4424541b4e9b3a5576d39a2be485d26e23f` at commit `8b75977b138205c4ba402000b25d226d55994682`. Its original line numbers and display IDs are historical. For the current 240-display source binding, use `formal_status/display_formula_audit_current_20261018.md`; that report preserves the prior review scope and records the five current-source deltas.


Date: 2026-10-17 (UTC). Read-only inspection of the publication tree; no compilation, axiom audit, or modification of that tree was performed.

- Inspected tree: `/data/odd_proxy/github_publication/exact-hoeffding-constants`.
- Inspected HEAD: `8b75977b138205c4ba402000b25d226d55994682`.
- Frozen source: `submission/current/manuscript.tex`, 1897 lines.
- Frozen-source SHA256: `b1bb1e3df8d8b651c4872692a8b0f4424541b4e9b3a5576d39a2be485d26e23f`.
- Scope: lines 1–1100 and 1610–1897. Lines 1101–1609 are outside this review. Module references below are to `ExactHoeffding/<module>.lean` in the inspected tree, namespace `ExactHoeffding` unless stated otherwise.

## Reading key and conclusion

**D** means a definition or coordinate choice, not a proved mathematical assertion. **T** means an exact theorem or an exact theorem with the indicated change of coordinates. **P** means a proof-intermediate identity or inequality; its coverage is specified separately. **W** means the substantive result is proved, but the displayed intermediate formula does not have a public conclusion in the displayed form. This is not a claim that a final theorem is missing. A theorem name alone is not accepted as evidence: domains, actual-law bridges and conclusion shapes were inspected.

The exact parity constant, all-parameter sharp curvature, actual Jacobi-to-Bernoulli representation, real-domain stationary comparison, Riccati barrier certificate and actual globally optimized fourth-order expansion have substantive theorem statements. The principal remaining **display-level export** issues are the auxiliary radical `q₀` inequalities, the explicit public formula for the positive stationary root, the complete printed Taylor-remainder statements for the second and third cumulants and the tilt-Taylor expansion, and the particular Bernoulli-gap reflection/second-derivative proof. These should not be conflated with missing proofs of the sharp constant or fourth-order optimized theorem.

## 1. Main constants, law and reduction

| Frozen formula / line | Kind | Exact Lean correspondence and scope |
|---|---|---|
| `eq:exchange-intro` / 46 | D/T | Defines the admissible coefficient problem. Actual uniform bound and leastness: `paritySharpConstant_is_valid`, `paritySharpConstant_is_least` (`ExactParityConstants`); the measure-level exchangeability problem is the existing `IsExchangeableCoefficient` API, not an assumed hypergeometric reduction. |
| `eq:hypergeom` / 88 | D/T | `hypergeomCount`, `hypergeomMass` (`Hypergeometric`) define the binomial quotient. `hypergeomSupport_iff`, `hypergeomSupport_bounds`, `hypergeomMass_ne_zero_iff` (`Support`) prove the true support for legal `k,m ≤ N`; zero/full margins are separately treated. |
| `eq:psi` / 93 | D/T | `hypergeomCenteredLogMGF` (`HypergeometricLaplace`) is the actual finite MGF log minus `mk t/N`. `hypergeomLogMGF_second_deriv_eq_variance` (`HypergeometricODE`) identifies its second derivative with actual tilted variance; subtracting the linear centering does not change the second derivative. |
| `eq:CNexact` / 102 | T | `exact_finite_exchangeability_constants` and `exactExchangeableConstant_even/odd` (`ExactParityConstants`). Odd end-to-end statement: `exact_odd_global_theorem` (`ExactOddGlobalTheorem`), including validity, leastness, attainment and the closed expression. The nontrivial constant problem has `N ≥ 2`; do not extend its displayed quotient to `N=1`. |
| `eq:CNupper` / 109 | T | `normalizedHypergeomProxy_universal_upper` (`NormalizedProxy`), transferred by `exactExchangeableConstant_eq_variational` (`VariationalIdentity`); the exact parity theorem is stronger. |
| `eq:odd_extremizers` / 113 | T | `odd_normalized_proxy_all_equality` (`OddHypergeomExtremizers`) and `odd_normalized_proxy_global_optimality` (`ExactOddGlobalTheorem`), with `N=2n+1`, `n>0`, interior legal margins. Complements are included; this is a classification of all maximizing **margins**, not uniqueness of the optimizing real tilt. |
| `eq:asymptotic` / 117 | T | `exactExchangeableConstant_first_order_limit` (`ConstantAsymptotics`), and parity-specific first-order limit declarations in the same module. |
| `eq:main_laplace` / 127 | T | `hypergeom_laplace_envelope` / `hypergeom_laplace_envelope_equality_iff` (`LaplaceEnvelopeTheorem`): `3≤m≤k`, `2k≤N`, `2m<N`, every real tilt; equality iff tilt zero. This printed theorem is **not** an assertion for every arbitrary margin without these hypotheses. |
| `eq:main_bern_envelope` / 131 | T | `hypergeom_proxy_lt_scaled_bernoulli_subhalf`, `hypergeom_proxy_lt_scaled_bernoulli`, and balanced/equality variants (`FinitePopulationBernoulliEnvelope`). Strictness requires the indicated unbalanced interior regime; the even balanced case has equality of optimal proxies. |
| `eq:curvature` / 143 | T | `hypergeomTiltVariance_sharp`, `hypergeomLogMGF_sharp_curvature` (`SharpCurvatureTheorem`): all `N,k,m : ℕ`, `k≤N`, `m≤N`, every real `t`, including deterministic margins. `AllParameterCurvatureEquality` contains the separate interior and one-point-margin equality statements. This is an upper bound, not merely nonnegativity. |
| `eq:mgf` / 152 | T | `hypergeom_uniform_log_laplace_domination` (`UniformLaplace`), for all legal margins and real tilt. `StrictUniformLaplace` supplies strictness/equality under its nondegenerate hypotheses. |
| `eq:proxy` / 157 | T | `hypergeomOptimalProxy_le_curvature` (`OptimalProxy`); `hypergeomOptimalProxy_isOptimal` verifies that the supremum definition is the least global quadratic coefficient. |
| `eq:twolevel_second` / 214 | P | The constrained circle is explicit, with `threeCircleObjective_second_deriv_zero` (`ThreePointCircleObjective`) and local-maximum second derivative nonpositivity used inside `pairedExponential_no_three_distinct_max` (`ThreePointExclusion`). The proof's `hcurv` and `hnonpos` give exactly the three-node weighted inequality after `ηᵢ=1/p′(xᵢ)`. It is derived from an actual constrained maximum, not supplied as a Hessian hypothesis. No separate public theorem with the paper's `h,p` notation is exported. |
| `eq:LKidentity` / 232 | T | `exchangeable_coefficient_iff_variational`, `exactExchangeableConstant_eq_variational` (`VariationalIdentity`), together with the definitions of `hypergeomVariationalConstant`, `normalizedHypergeomProxy`, `optimalProxy`. Factor `8N` times `sup ψ/t²` agrees with `4N` times the optimal variance proxy. |
| `eq:globalC` / 260 | T/P | `normalized_curvature_cancel`, `normalizedHypergeomProxy_universal_upper` (`NormalizedProxy`) implement the normalized bound. The final maximum equals one because balanced/sample-limiting choices exist, not because a maximum over an unspecified empty domain is assumed. |
| `eq:sym1` / 272 | T | `hypergeomMGF_transpose`, `hypergeomPMFValue_transpose` (`Symmetries`), and `hypergeomCenteredLogMGF_transpose`, `hypergeomOptimalProxy_transpose` (`OptimalProxy`). |
| `eq:sym2` / 273 | T | `hypergeomMass_success_complement`, `hypergeomMGF_success_complement` (`Symmetries`); centered and optimal-proxy reflection theorems (`OptimalProxy`). Legal finite margins, exact law/MGF identities. |
| `eq:sym3` / 274 | T | `hypergeomMGF_sample_complement` (`Symmetries`), `hypergeomOptimalProxy_sample_complement` (`OptimalProxy`), with the linear centering and tilt reflection retained. |
| `eq:sym4` / 275 | T/P | Composition of the two actual complement identities; no independent distributional symmetry assumption. A separate named double-complement law theorem was not needed by the actual curvature proof. |
| `eq:param` / 278 | D/T | `jacobiK`, `jacobiM`, `jacobiN` and `jacobi_normalization` (`Jacobi`) implement `k=j`, `m=j+h`, `N=2j+h+r`. The original-margin reduction is implemented by the complement/transpose cases in `SharpCurvatureTheorem`, not by asserting this parametrization for arbitrary original `k,m`. |
| `eq:Bdef` / 283 | D | The canonical curvature coefficient; corresponds to `sharpCurvatureConstant` after the canonical substitution. It is not itself an inequality. |

## 2. Jacobi normalization, roots, and the actual tilted law

| Frozen formula / line | Kind | Exact Lean correspondence and scope |
|---|---|---|
| `eq:Q` / 290 | D/T | `jacobiCoeff`, `jacobiPGF` (`Jacobi`). `jacobiCoeff_factorial_form` proves the exact coefficient normalization; `jacobiCoeff_scaled_hypergeomCount` and `jacobiPGF_eval_eq_scaled_hypergeomPolynomial` connect this polynomial to the actual finite hypergeometric generating polynomial. The normalization is not left implicit. |
| `eq:tiltuv` / 297 | D/T | Actual tilt mean/variance are `hypergeomTiltMean`, `hypergeomTiltVariance` (`HypergeometricODE`). The PGF law identity in `JacobiActualPGF`, logarithmic derivative identities in `BernoulliMGFGeometry`, and `hypergeomTiltMean_hasDerivAt` supply the mean and variance identities. The equality involving `log z` uses `z>0`; the quotient is not asserted at a zero of `Q`. |
| `eq:coeffratio` / 304 | P/T | `jacobiCoeff_recurrence` (`Jacobi`) proves the denominator-cleared adjacent coefficient identity, for `i<j`; `jacobiCoeff_pos` makes division legitimate. At `i=j`, the next coefficient is zero and the printed factorial quotient is not the operative recurrence domain. |
| `eq:hyperode` / 309 | T | `jacobiPGF_ode` (`JacobiSimpleRoots`) is a polynomial identity, hence valid also at `z=1`. Actual mass recurrences are independently proved in `HypergeometricODE`. |
| `eq:jacobi` / 321 | T | `jacobiPGF_eq_factorial_standard_cleared` (`JacobiStandardNormalization`) is an exact polynomial identity for all natural `j,h,r`. `jacobiPGF_eval_eq_standardJacobi` and `hypergeomPolynomial_eq_standardJacobi` give the displayed rational-composition formula for `z≠1`. The factor is exactly `j!` and parameters exactly `(r,h)`, not interchanged. |
| `eq:alphas` / 328 | D/T | `standardJacobi_root_maps_to_canonical`, `standardJacobi_root_alpha_pos` (`JacobiStandardNormalization`), using `standardJacobi_roots_mem_Ioo`. `α=(1−ξ)/(1+ξ)>0`; corresponding canonical root is `−α`. |
| `eq:factor` / 332 | T | `jacobiPGF_root_normalized_factorization` (`JacobiFactorization`), together with `jacobiPGF_roots_card`, `jacobiPGF_roots_nodup`, `jacobiPGF_roots_negative`; the multiset product is exactly the simple-root product in the paper. |
| `eq:PB` / 338 | T | `hypergeom_tilted_bernoulli_mean_variance` and `hypergeom_tilted_true_support_mean_variance_bound` (`BernoulliMGFGeometry`), plus canonical positivity in `HypergeometricODE`. `hypergeomTiltVariance_admissible_of_margins` (`TiltedAdmissibilityDirect`) is an additional actual-law proof of the same admissibility bound. |

### The Jacobi assertion is not a renamed PGF

`standardJacobi j α β` is defined by the standard finite binomial expansion

`Σₖ binom(j+α,k) binom(j+β,j−k) ((X+1)/2)^k ((X−1)/2)^(j−k)`.

`jacobiRodrigues_coefficient_standard` proves the natural-number factorial identity

`choose j k * descFactorial(h+j)(j−k) * descFactorial(r+j)k = j! * choose(j+r)k * choose(j+h)(j−k)`.

`standardJacobi_rodrigues_identity` then proves exactly

`D^j[(X+1)^(h+j)(X−1)^(r+j)] = 2^j j! (X+1)^h (X−1)^r P_j^(r,h)(X)`.

The equivalent shifted Rodrigues identity is also exported. `standardJacobi_hypergeom_end_to_end` bundles the cleared PGF identity, degree `j`, exactly `j` roots, no repeated roots, and every root in `(-1,1)`. Thus the factorial normalization, standard polynomial, actual PGF and simple real roots are all connected. The scope is **nonnegative integral Jacobi parameters**, exactly the manuscript's `r,h`; it does not formalize the general real-parameter orthogonality theorem for arbitrary `α,β>−1`.

At `z=1`, the manuscript's sentence must be read as the **denominator-cleared polynomial continuation**. The uncontinued rational expression is undefined classically. With Lean's totalized real division its literal RHS would be zero for `j>0`, so the evaluation theorem correctly assumes `z≠1`; the polynomial theorem covers `z=1`. No claim that the raw rational syntax holds there is justified.

The unlabeled terminating `₂F₁` line and invocation of Pfaff's transformation are not separately represented as special-function theorems. The standard Jacobi identity is proved directly by polynomial coefficients and Rodrigues normalization; this proves the identity needed here without formalizing the broader Pfaff transformation. This is an alternative proof, not evidence of a missing Jacobi identity.

Finally `jacobiPGF_tilted_bernoulli_pgF` (`JacobiFactorization`) and `jacobiHypergeom_tilted_mass_pgf` (`JacobiActualPGF`) give the normalized tilted product. `hypergeom_tilted_law_eq_shifted_independent_bernoulli` (`HypergeomBernoulliLaw`) proves equality of the **actual tilted probability law** with a shifted sum of independent Bernoulli variables, including the true-support lower shift. This is stronger than a conditional statement assuming Bernoulli parameters exist.

## 3. Stationary Riccati calculation and universal polynomial certificate

| Frozen formula / line | Kind | Exact Lean correspondence and scope |
|---|---|---|
| `eq:riccati` / 358 | T | `hypergeomTiltMeanVariance_balance`, `hypergeomTiltMean_riccati`, and `_of_margins` versions (`HypergeometricODE`). Substitution `z=exp t` gives the paper's equation, including `z=1`. |
| `eq:differentiated` / 364 | T | `hypergeomTiltVariance_differential_balance` and `_of_margins` (`HypergeometricODE`, `HypergeometricODEMargins`) retain the actual variance derivative `w`. The stationary version is `hypergeomTiltVariance_stationary_balance`. |
| `eq:Dden` / 369 | D | `stationaryDen` (`StationaryCertificates`). Its positivity on the actual admissible curve is a separate theorem, `hypergeomTiltMeanVariance_den_pos` / `_of_margins`; the displayed definition alone does not prove positivity. |
| `eq:zfromuv` / 373 | P/T | `hypergeomTiltExp_ratio` / `_of_margins`, with the stationary balance and positive denominator, yield this exact relation. The derivation is restricted to stationary actual variance, as in the paper. |
| `eq:F` / 377 | D/T | `stationaryPolynomial` defines the LHS; `stationary_elimination` proves elimination from the two balance equations. `hypergeomTiltVariance_stationary_sharp` (`CanonicalCurvature`) supplies these from the actual law. Thus the zero identity is not assumed for an arbitrary law. |
| `eq:F0` / 388 | T | `stationary_polynomial_constant` and `stationary_polynomial_quadratic` (`StationaryCertificates`); positivity uses `0<u<j≤m`, `r≥0`. `stationaryPolynomial_existsUnique_positive_root` (`StationaryPositiveBranch`) proves existence and uniqueness for real parameters `1≤j≤m`, `r≥0`, `1<j+m+r`. |
| `eq:letters` / 400 | D | Algebraic substitutions `T,L,S,D`; `S=h+r≥0` and `abs D≤S` are supplied by nonnegative `h,r`, not silently treated as extra theorems. |
| `eq:AandE` / 408 | D | Auxiliary expressions. Their nonnegativity/positivity in the proof follows from the subsequent hypotheses; it is not definitional. |
| `eq:masterpositive` / 415 | T | `universal_stationary_comparison` (`StationaryCertificates`) quantifies over **real** `j,L,D,x`, with `3≤j`, `j−1≤L`, `abs D≤L−j+1`, and `0<j²(j−1)−(L+j)x²`. This last condition is equivalent to the paper's strict square-root bound. It is not a finite table of degrees or an integer-only check. |
| `eq:g` / 426 | D/P | `stationaryG` and the sign-case reduction in `universal_stationary_comparison`. `q=abs x`, `d=abs D` retain the opposite-sign branch. |
| `eq:square1` / 433 | P/T | `stationary_square_identity` is the exact completed square for arbitrary real inputs with `A≠0`. `stationary_large_A_square` is a denominator-free version; `stationary_large_A_nonnegative` implements Case I. |
| `eq:qmin` / 441 | W | The paper introduces a radical auxiliary `q₀` and proves `q>q₀`. No named `q₀` or theorem with this precise radical comparison was found. Lean instead uses `A L<j²` directly with the exact relation between `A` and `q²`. This line should not be marked as literally exported. |
| `eq:qbound` / 445 | W | The literal auxiliary statement `q₀≥j/L` is not exported. `stationary_small_A_q_bound` proves `j≤Lq` for the **actual q**, under all of the Case II hypotheses. This is the required downstream inequality, with no radical helper. |
| `eq:gS` / 468 | P | Evaluation of `stationaryG` at `d=S`, an algebraic substitution used inside `stationary_G_nonnegative`; not a new analytic assertion. |
| `eq:Eq` / 472 | W/T | The literal `E q₀≥2jS` is not exported. `stationary_small_A_Eq_bound` proves `2j(L−j+1)≤(L(L+1)−2j)q` directly for the actual `q`, hence the needed `Eq≥2jS`. |
| `eq:Kdef` / 476 | D/T | `stationaryK` defines the exact polynomial; `stationary_K_nonnegative` proves its nonnegativity for real `j≥3`, `S≥0`, with the prescribed `L=j−1+S`. It is not just a definition. |
| `eq:Kpositive` / 485 | T | `stationary_K_expansion` is the complete exact degree-five-in-`S` expansion in free real `a,S`. `stationary_K_nonnegative` proves the coefficient signs for `a=j−3≥0`. All displayed coefficients agree, including the `S⁴` and `S⁵` terms. |
| `eq:exactidentity` / 503 | T | `stationary_main_identity` is an exact real algebraic identity with the sole division-side assumption `2j+h+r−1≠0`. It has the paper's factor `−16T`, `u=(j+x)/2`, target `B`, and the full `D,x` expression. |
| `eq:allinner` / 520 | T | `hypergeomTiltVariance_sharp_canonical` / `_of_margins` (`CanonicalCurvature`), based on `admissible_stationary_sharp_bound`, actual endpoint decay and attainment of any putative super-ceiling maximum. Covers all canonical `j≥3`, not a bounded grid. The pointwise all-tilt theorem implies the displayed supremum bound. |
| `eq:3pointvar` / 563 | W/T | `threePointVariance_normal_form`, `hypergeom_two_draw_curvature_formula`, `threePointVariance_sqrt_envelope`, `hypergeom_two_draw_curvature_le` (`SmallSupportCurvature`) prove the actual three-mass rational variance and its bound. The normalization variable `(a+c z²)/(2√(ac)z)` equals the paper's `cosh s` after centering; no separately exported theorem with the literal `cosh s` formula or its printed `d/dq` derivative was found. The sharp two-support conclusion is proved algebraically. |

### Root formula at the end of the appendix

`eq:explicitF` / 1788 and `eq:bc` / 1792 are exactly `stationary_polynomial_quadratic`: collecting its coefficient gives `(N+2)u²+(−2jm−j−m+r)u+jm(1−r)`, with `N=j+m+r`. The constant term is `u(j−u)(r+u)(m−u)`. No coefficient is dropped.

`eq:vplus` / 1797 is used as the **constructed witness** inside `concave_quadratic_existsUnique_positive_root`: the proof sets `s=√(b²+4Tc)` and `v=(b+s)/(2T)`, proves `v>0`, proves the quadratic vanishes, and proves uniqueness. The positive-root existence/uniqueness is public. A separately exported equality identifying the named positive stationary branch with this displayed radical was not found. For a claim of literal formula coverage, export this equality; do not report only existence/uniqueness as if it were the public radical formula.

The unlabeled collected-`D` expansion after line 1802 is the same polynomial identity as `stationary_main_identity`; the denominator-cleared completed square is `stationary_large_A_square`. These are exact ring identities in real parameters, not external symbolic certificates.

## 4. Variance optimum, Bernoulli and two-draw benchmark

| Frozen formula / line | Kind | Exact Lean correspondence and scope |
|---|---|---|
| `eq:variance_constant` / 592 | T | `exactExchangeableVarianceConstant_floor`, `exact_variance_parity_theorem` (`ExchangeableVarianceSupremum`) prove the actual exchangeable variance supremum, the floor expression, and the parity values, including an attaining nearest-balanced Hamming law. This is not only a hypergeometric scalar calculation. |
| `eq:variance_gap_integral` / 601 | T | `oddHypergeomConstant_variance_gap_integral` and `odd_variance_gap_scalar_pos` (`ParityVarianceGap`), with `x=1/N`. The integral identity is proved, not inferred from a numerical asymptotic. |
| `eq:variance_gap_expansion` / 602 | T | `odd_variance_gap_fourth_expansion_along` (`ParityVarianceGap`) and `exact_variance_gap_fourth_expansion_along` (`ExchangeableVarianceSupremum`): all odd population sequences tending to infinity, with exactly `2/3,2/3,26/45` and remainder `O(N⁻⁵)`. |
| `eq:bernproxy` / 649 | T | `bernoulli_sharp_quadratic_bound`, `bernoulli_sharp_quadratic_optimal` (`BernoulliOptimal`) prove the global coefficient on `p∈[0,1]`, with separate balanced and deterministic endpoint definitions. `bernoulli_half_isOptimal`, `bernoulli_half_quadratic_limit` handle `p=1/2` through the actual variance limit. The printed unbalanced logarithmic expression itself presumes `0<p<1`. |
| `eq:oddL` / 655 | T | `normalizedHypergeomProxy_singleton_subhalf` (`OddHypergeomExtremizers`), singleton Bernoulli identification (`SingletonOptimalProxy`), plus `odd_exchangeable_constant_attained` (`ExactOddGlobalTheorem`). `ExplicitExtremizerTheorem.explicit_single_coordinate_extremizer` gives the concrete contrast, actual slice law and nonzero contact argument. |
| `eq:threeproxy` / 673 | T | `threeMass_optimal_proxy` (`TwoDrawProxyComplete`) proves leastness for all positive normalized masses satisfying `p₁≤4√(p₀p₂)`, with both asymmetric orientations and the balanced continuous interpretation. The formula is not merely an equality at a candidate contact. Its literature attribution remains Atouani–Marchal–Arbel. |
| `eq:Ltwo` / 696 | T | `hypergeom_two_draw_odd_max_value`, `hypergeom_two_draw_odd_max_iff` (`TwoDrawComparison`), with full-`k` endpoints included by `odd_two_draw_all_success_upper`, `odd_two_draw_all_success_least`, `odd_two_draw_all_success_extremizers` (`TwoDrawSingletonComparison`). `N=2n+1`, `n≥2`; formula matches `4/[(N−2)log((N+1)/(N−3))]`. |
| `eq:twostrict` / 700 | T/W | Strict inequality: `odd_two_draw_closed_strict`, `oddTwoDrawConstant_lt_singleton` (`TwoDrawSingletonComparison`). The `2/(3N³)+O(N⁻⁴)` term follows from `odd_nearly_balanced_gap_fourth_expansion_along` (`OptimalProxyFourthExpansion`) specialized to `m=2` and the exact two-draw central-value identity. This is an exact theorem composition; no separate two-draw-only asymptotic declaration is needed. |

Unlabeled Hermite proof ingredients before `eq:twolevel_second` are not assumed: `threeHermitePolynomial_values`, `_derivatives`, `_fifth_derivative`, `_sixth_derivative` (`ThreePointHermite`) and `threePoint_hermite_weighted_derivative_pos` (`ThreePointHermitePositive`) establish the weighted positive derivative, while `exists_two_level_slice_dominator` (`TwoLevelExistence`) produces an actual two-level maximizing replacement under fixed sum and squared norm.

## 5. Parity-uniform Riccati envelope, every certificate coefficient

| Frozen formula / line | Kind | Exact Lean correspondence and scope |
|---|---|---|
| `odd:eq:laplace` / 776 | T | Same exact theorem as `eq:main_laplace`: `hypergeom_laplace_envelope`, every real tilt on the stated `3≤m≤k≤N/2`, `2m<N` domain, strict away from zero. |
| `odd:eq:BernEnvelope` / 781 | T | `hypergeom_proxy_lt_scaled_bernoulli_subhalf`, balanced counterpart and `hypergeom_proxy_scaled_bernoulli_equality_iff` (`FinitePopulationBernoulliEnvelope`). Strict pointwise Laplace comparison alone is not used to infer a strict supremum: the quotient-at-zero and compact/tail argument are implemented in the proxy comparison chain. |
| `odd:eq:variance0` / 797 | T | `hypergeomTiltMean_zero`, `hypergeomTiltVariance_zero` (`ZeroTiltMoments`); `varianceBarrier_center_probability` / `_success_fraction` (`HypergeometricODEMargins`) identify the exact center of the quadratic barrier. |
| `odd:eq:PB` / 803 | T | `hypergeomTiltVariance_admissible_of_margins` (`TiltedAdmissibilityDirect`) and the actual Bernoulli-law chain above. Strict positive variance and interior mean are proved in `HypergeometricODEMargins`. |
| `odd:eq:F` / 820 | D/T | `riccatiA`, `riccatiC`, `riccatiF` (`RiccatiCertificates`); `riccati_differential_algebra` proves the polynomial differential algebra. The symbols `A,C` here differ from the previous stationary certificate's `A`; the audit keeps the two APIs separate. |
| `odd:eq:curveODE` / 827 | T | `hypergeomTiltVariance_curve_identity_of_margins`, `hypergeomTiltVariance_centered_curve_identity` (`HypergeometricODEMargins`). In the tilt coordinate the term is `N y·d_t v`; since `d_t v=V·d_u V`, this is exactly `F+NyVV′=0`. The actual proof can avoid constructing a global inverse map. |
| `odd:eq:P` / 849 | D | `varianceBarrier` and `varianceBarrierDerivative` (`RiccatiCertificates`) with the exact `M,a,d` definitions. |
| `odd:eq:barrier` / 856 | T | `hypergeomTiltVariance_barrier_canonical` (`HypergeometricBarrier`): actual tilted hypergeometric variance is at most the quadratic barrier, and equality iff `t=0`. Strictly increasing actual mean identifies this with `u=μ`. It derives hypotheses from actual masses, PB admissibility, ODE and endpoints. |
| `odd:eq:W` / 868 | D | `barrierW` (`RiccatiCertificates`), exact free-variable quadratic polynomial. |
| `odd:eq:residual` / 872 | T | `barrier_residual_identity`: exact rational identity, with the required denominator nonzero conditions explicitly stated. It contains the full factor `−G y² W`. |
| `odd:eq:E` / 886 | T | `barrier_admissibility_identity`, exact gap between PB parabola and barrier. Contact admissibility is then derived from actual PB bound. |
| `odd:eq:lambda` / 893 | D | `barrierLambda`, `barrierDelta`, `barrierAlpha`; positivity is separately proved, not embedded in these definitions. |
| `odd:eq:certificate` / 904 | T | `barrier_sum_of_squares_identity`: exact identity in free real parameters after denominators are cleared. `certificateA/B/C` agree with every quadratic coefficient in the paper. |
| `odd:eq:det` / 910 | T | `barrier_determinant_identity`, exact `N² U₀ V₀ /[(N−2m)²(N−2)²(N−1)]`; `certificateU/V` are the precise cubic/quadratic polynomials. |
| `odd:eq:lambda_pos` / 927 | T | `certificate_lambda_expansion`, then `certificate_lambda_positive`; exact substitution `m=j+3`, `N=2m+r`, not a degree-bounded sign test. |
| `odd:eq:alpha_pos` / 929 | T | `certificate_alpha_numerator_expansion`, `certificate_alpha_numerator_positive`; the numerator positivity is combined with `δ²>0` on `2m<N`. |
| `odd:eq:U_pos` / 930 | T | `certificate_U_expansion`, `certificate_U_positive`: all printed terms and all real nonnegative shifted-degree parameters. |
| `odd:eq:V_pos` / 931 | T | `certificate_V_expansion`, `certificate_V_positive`: full cubic expansion, including the `r³+5r²` terms. |
| `odd:eq:Wpositive` / 935 | T | `quadratic_form_positive`, `barrier_certificate_positive`, `barrier_contact_W_positive`: `m≥3`, `2m<N`, `0≤d≤δ`, and actual contact/PB admissibility imply strict positivity. The theorem does not claim `W>0` for all free `d,z₀` with no admissibility condition. |
| `odd:eq:end0` / 944 | T | `barrier_left_endpoint_identity`, `barrier_endpoints_positive`: exact endpoint numerator and its strict sign in the envelope domain. |
| `odd:eq:endm` / 946 | T | `barrier_right_endpoint_identity`, `barrier_endpoints_positive`: exact other endpoint. Endpoint decay of the actual variance comes from the finite tilted-law endpoint module. |
| `odd:eq:crossing` / 955 | T/P | `riccati_contact_derivative_identity`, `riccati_contact_derivative_sign` (`RiccatiCertificates`, `RiccatiBarrier`) give the exact mean-coordinate contact calculation/sign. `riccati_time_contact_identity` gives the equivalent tilt-coordinate identity. `variance_barrier_of_riccati_flow` (`VarianceBarrierFlow`) proves the global crossing conclusion; it is not assumed as a no-crossing hypothesis. |
| `odd:eq:Y` / 972 | D/T | The comparison mean is the scaled Bernoulli mean used in `ScaledBernoulliComparison`. Its derivative/initial value drive `variance_bound_implies_scaled_bernoulli_laplace` and `strict_variance_bound_implies_scaled_bernoulli_laplace`; the actual-law bridge is `hypergeom_laplace_envelope_canonical`. Balanced variants exist separately. |
| `odd:eq:bern` / 994 | T | `bernoulliSharpBeta_eq_formula` and `bernoulli_sharp_quadratic_optimal` (`BernoulliOptimal`), with log-odds/artanh relation in `ArtanhRatio`/`AnalyticContractionCoefficient`. Strict positive imbalance is required for the displayed uncontinued ratio; balanced value is `1/4`. |
| `odd:eq:exact` / 1009 | T | `odd_variational_constant_global_optimum` and `exact_odd_global_theorem` (`ExactOddGlobalTheorem`), plus all-margin equality classification in `OddHypergeomExtremizers`. No `m_N` boundedness condition remains. |
| `eq:rootineq` / 1047 | T | `jacobi_root_dispersion` (`JacobiRootDispersion`) for all natural `j,h,r` and `z>0`; `jacobiHypergeom_tilt_variance_root_sum` and `jacobi_transformed_root_square_sum` prove the exact root-sum/variance bridge. Lean uses negative roots `x=−α`; its `(z+x)/(z−x)` is exactly the paper's `(z−α)/(z+α)`. |
| `B:pmf` / 1075 | D/T | Same actual law and true support as `eq:hypergeom`. |
| `B:variance` / 1081 | T | `hypergeom_cumulant2_complete` (`Cumulants`), equivalently `hypergeomTiltVariance_zero` (`ZeroTiltMoments`), with exact finite-population factor `m(N−m)/(N−1)`. |
| `B:proxy` / 1087 | D/T | `hypergeomOptimalProxy` (`OptimalProxy`) is the punctured-tilt supremum; `hypergeomOptimalProxy_isOptimal` proves it is the least bound. The removable quotient at zero is separately handled by `VarianceOptimality`/`RescaledActualProxy`. |
| `B:W` / 1095 | D/T | Defines the central-margin variance. Its exact parity evaluation follows from `hypergeom_cumulant2_complete` with the central `k`; `GoalBFixedSample`/`OddCentralStrict` use the same quantity. Do not confuse it with the unrelated Riccati certificate `W(d,z₀)`. |

## 6. Fourth-order appendix: actual global optimization, not formal jets only

| Frozen formula / line | Kind | Exact Lean correspondence and scope |
|---|---|---|
| `eq:oddparams` / 1613 | D/T | Fixed `m,s`, legal integer populations satisfying `2k+s=N`; `rescaledFactorialMoment_hypergeom` (`RescaledFactorialFamily`) and `rescaledProxyExtension_hypergeom` (`RescaledActualProxy`) identify the analytic inverse-population family with the actual law at `e=1/N`. `normalizedHypergeomProxy` has precisely the printed normalization. |
| `eq:tiltexp` / 1627 | T | `actualHypergeomProxy_joint_fourth_order_main` (`FourthOrderMainTheorem`) gives analytic `τ,T` with `τ(0)=0`, derivative `4s`, and exact remainder identity `τ(e)=4se+4s(m−1)e²+4s(6m+s²−6)e³/3+e⁴T(e)`. The same theorem proves `τ(e)` is the **unique actual global optimizer** at sufficiently large admissible integer populations. |
| `eq:Rexp` / 1632 | T | The same theorem gives exact analytic remainder `e⁵U(e)` for the printed normalized quartic polynomial. `actualHypergeomProxy_normalized_optimum_fourth_along` (`ActualNormalizedFourthAsymptotics`) and `normalizedHypergeomProxy_fourth_expansion_along` (`OptimalProxyFourthExpansion`) export actual-sequence `O(N⁻⁵)` versions. Fixed `m>0` and fixed real `s`, not a uniform expansion in growing `m` or `s`. |
| `eq:fixedgap` / 1643 | T | `odd_nearly_balanced_gap_fourth_expansion_along` and `_fourth_limit_along` (`OptimalProxyFourthExpansion`): exact `2(m−1)/3` cubic and `2(m−1)(2m+1)/3` quartic coefficients. For strict singleton dominance require `m>1`; `m=1` gives zero gap, as it should. |
| `eq:offs_gap` / 1649 | T | `odd_singleton_gap_second_expansion_along`, `odd_singleton_gap_second_limit_along`, `odd_singleton_gap_eventually_pos_along` (`OptimalProxyAsymptotics`), with `s>1` and admissible odd populations. It does not assert eventual positivity for `s=1,m=1`. |
| `eq:q0` / 1666 | T | `rescaledProxyExtension_limit_formula` and `rescaledProxyExtension_at_zero` (`RescaledQLimit`) give the exact limiting law formula, including the removable value `m/4`. |
| `eq:qstrict` / 1670 | T | `rescaledProxyExtension_limit_strict` (`RescaledCompactConvergence`) uses `limiting_proxy_strict` (`LimitProxyStrict`), `m>0`, arbitrary `t≠0`. |
| `eq:Qexpand` / 1676 | T | `rescaledProxyExtension_joint_uniform_taylor` (`ActualProxyUniformTaylor`) proves the displayed cumulant polynomial and an integral fifth-derivative remainder on one joint neighborhood in inverse-population parameter and tilt, with a jointly continuous remainder. The rescaled factorial-family cumulants at `e=1/N` are identified with the actual finite-law cumulants. |
| `eq:singletonL` / 1725 | T | `normalizedHypergeomProxy_fourth_expansion_along` specialized to `m=s=1`, together with `normalizedHypergeomProxy_singleton_subhalf`, proves the actual singleton coefficient expansion. `odd_variance_gap_fourth_expansion_along` additionally exports the same `2/3,2/3,26/45` coefficient calculation after subtracting `1+e`. |
| `eq:factorial_moments` / 1741 | T | `hypergeom_descFactorial_expectation` (`GeneralFactorialMoments`) and `hypergeom_factorial_moment_formula` (`Cumulants`): **all** natural orders `r`, legal `k,m≤N`. Explicit zero branch for `r>N`; falling factorials make `m<r≤N` zero. This deals with zero denominators rather than relying on cancellation outside `r≤N`. |
| `eq:kappa2exp` / 1754 | W/T | Exact actual formula: `hypergeom_cumulant2_complete`; rescaled exact formula: `rescaledProxyExtension_zero_tilt_formula` (`RescaledOptimumLeading`). Its second/third/fourth population derivatives are proved in `RescaledVarianceSecond`, `RescaledThirdOrderInputs`, `RescaledFourthPopulationInputs`. The exact printed fourth-order **cumulant** expansion with its `O(e⁵)` remainder is not exported as a standalone theorem. The coefficients used to prove the optimized quartic theorem are actual rational derivatives, not postulated constants. |
| `eq:kappa3exp` / 1756 | W/T | `hypergeom_cumulant3_standard` (`Cumulants`) proves the exact actual formula for `N≥3`; `rescaledProxyExtension_deriv_tilt_zero` (`RescaledMixedDerivative`) gives `κ₃/3` as the exact rational function. The required second/third population derivatives are proved. A public statement of the whole displayed `κ₃` expansion with `O(e⁴)` was not found. |
| `eq:kappa4exp` / 1758 | T | `hypergeom_rescaled_cumulant4_remainder_identity`, `hypergeom_rescaled_cumulant4_remainder`, `hypergeom_cumulant4_balanced_expansion` (`HighCumulants`). Exact polynomial coefficients and genuine analytic/sequence `O(e³)` remainder, not only a limit. |
| `eq:kappa56exp` / 1760 | T | `hypergeom_rescaled_cumulant5_remainder`, `hypergeom_rescaled_cumulant6_remainder`, `hypergeom_cumulant5_balanced_expansion`, `hypergeom_cumulant6_balanced_expansion` (`HighCumulants`). Actual fifth coefficient `−ms/2` and sixth limit `m/4` with the printed remainder orders. |
| `eq:exactk2` / 1770 | T | `rescaledProxyExtension_zero_tilt_formula`, together with the actual-family bridge and `hypergeom_cumulant2_complete`, proves exactly `m(1−s²e²)(1−me)/(4(1−e))`; stated away from the pole `e=1`. |
| `eq:exactk3` / 1774 | T | `rescaledProxyExtension_deriv_tilt_zero` proves one third of the displayed expression, with `1−e≠0` and `1−2e≠0`. The actual third-cumulant formula and the factor `3` identify it with `κ₂ se(1−2me)/(1−2e)`. These are neighborhood-of-zero formulas, not assertions at their poles. |
| `eq:explicitF`, `eq:bc`, `eq:vplus` / 1788–1797 | T/W | See the precise stationary polynomial/root discussion in Section 3; coefficients and constructed radical witness are proved, while a public branch-equals-radical conclusion remains to be exported. |
| `eq:bernref` / 1839 | W | `bernoulli_centered_log_mgf_reflection` (`BernoulliOptimal`) is **parameter reflection** `f_p(t)=f_(1−p)(−t)`, not the printed fixed-parameter gap reflection `G(2α−t)=G(t)`. The latter, and the joint claim `G′(0)=G′(α)=0`, were not found as public conclusions. The optimal Bernoulli bound is proved by the independent log-cosh tangent argument. Do not cite the parameter-reflection theorem as if it stated this formula. |
| `eq:bernsecond` / 1844 | W | `bernoulli_centered_log_mgf_cosh_representation`, `bernoulli_log_cosh_hasDerivAt`, `bernoulli_tanh_hasDerivAt`, `bernoulli_tanh_deriv_hasDerivAt` (`BernoulliProxy`) provide the needed calculus. No theorem with the displayed `G″(t)=c−1/[4cosh²((t−α)/2)]` conclusion or the subsequent complete zero/sign classification was found. `bernoulli_log_cosh_tangent_square` proves the upper bound by a different route; `BernoulliOptimal` proves contact and leastness. |

### Actual optimization and remainder dependencies

The following stronger assertions were checked in the statement of `actualHypergeomProxy_joint_fourth_order_main`:

1. It quantifies `m : ℕ` with `m>0` and arbitrary fixed real `s`; it constructs analytic `τ,T,U` rather than assuming an optimizer or its derivatives.
2. Its tilt and value remainders are exact factorizations `e⁴T(e)` and `e⁵U(e)`, with Big-O conclusions included.
3. It proves local stationary points coincide with `τ(e)` and, at sufficiently small admissible `e=1/N`, **all actual global maximizers** are precisely `τ(e)`.
4. `rescaledProxyExtension_uniform_on_compact` proves uniform convergence on compact tilt intervals, including zero. `actualHypergeomProxy_tail_bound` (`ActualProxyTail`) gives `O(1/abs t)` from the actual bounded centered support. `actualHypergeomProxy_global_maximizers_localize` and `actualHypergeomProxy_eventually_exists_unique_global_max` (`ActualOptimizerLocalization`, `ActualUniqueOptimizer`) close the global-to-local step.
5. The negative limiting Hessian and mixed jets are proved from the actual family: `rescaledProxyExtension_deriv2_tilt_zero`, `rescaledProxyExtension_zero_tilt_deriv4`, `rescaledProxyExtension_tilt_deriv_zero_deriv3`, `rescaledProxyExtension_tilt_deriv2_zero_deriv2`. The fourth-order conclusion is not a conditional formal-series calculation with supplied jets.

The unlabeled Stirling transformation at lines 1746–1750 is proved **through order six**, exactly the range used here, by `hypergeom_raw_moment_factorials_through_six` and `hypergeom_raw_moment_closed_through_six` (`HighCumulants`), with explicit order-five and order-six identities. This does not assert a new all-order Stirling theorem. In contrast the unlabeled actual moment–cumulant recursion at lines 1762–1765 is **all order**, via `finiteMGF_actual_moment_cumulant_recursion`, `hypergeom_actual_moment_cumulant_recursion` (`ActualMomentCumulantRecursion`), using actual derivatives of the logarithm. Orders five and six are connected to the explicit cumulant polynomials by `hypergeom_actual_log_derivatives_five_six`.

## 7. Actionable remaining display exports and wording precision

These are additions needed only if the deliverable promises every displayed intermediate formula, rather than all named mathematical results:

1. Export the actual stationary positive-root radical equality from the already-constructed witness in `StationaryPositiveBranch`; keep `T>0,c>0` and the canonical real-domain hypotheses.
2. Either export the auxiliary radical `q₀` comparisons (`eq:qmin`, `eq:qbound`, `eq:Eq`) or state in the formula concordance that the Lean proof directly proves the required inequalities in actual `q`. Do not label those literal radical displays as already-exported theorems.
3. Export the exact cumulant-2 and cumulant-3 Taylor remainders matching `eq:kappa2exp` and `eq:kappa3exp`, from the existing rational identities. This is a short packaging step with nonzero denominator hypotheses near zero, not a new optimized-asymptotics problem.
4. The two-variable tilt-Taylor remainder in `eq:Qexpand` is now exported by `rescaledProxyExtension_joint_uniform_taylor`; its local radius and jointly continuous integral remainder are uniform over both variables on the stated neighborhood.
5. The fixed-parameter Bernoulli gap reflection, both stationary derivative values, and its second-derivative formula are now exported in `BernoulliGapIdentities.lean` and included in the full audit. The optimal-proxy proof remains independent and covers the full probability interval.
6. For a literal display concordance, add the three-point `cosh` change-of-variable identity and the paper's `d/dq` derivative wrapper to the existing actual rational variance theorem. No sharp-curvature gap results from using the algebraic proof instead.
7. Preserve the `z≠1` condition on rational Jacobi evaluation and use the cleared polynomial identity at `z=1`. Preserve natural `h,r` scope; do not advertise general real Jacobi parameters or general Pfaff formalization.

No mathematics in the frozen manuscript was changed in this review. No new kernel-verification claim is made by this source audit. All quoted theorem names are from the inspected actual source, not the old theorem-environment map.

## Q-expansion remainder resolution — 17 October 2026

The earlier row for `eq:Qexpand` above is superseded by the integrated public
result `rescaledProxyExtension_joint_uniform_taylor` in
`ExactHoeffding/ActualProxyUniformTaylor.lean`. For fixed `m,s`, it provides a
single positive radius in both the inverse-population parameter and tilt, a
jointly continuous remainder on the full parameter plane, the displayed
coefficients through the sixth cumulant, and the integral fifth-derivative
remainder. The module is imported by `ExactHoeffding.lean`; its kernel build and
full transitive axiom audit passed on 17 October 2026. Other display rows in
this historical inventory remain separately scoped and must not be inferred
closed from this one result.
