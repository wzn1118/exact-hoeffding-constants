# A1–A5 and B1–B2 Lean closure audit — 17 October 2026

This audit records the current root-tree result scope for the seven requested
proof groups. The authoritative declaration-by-declaration bindings are in
`checks/manuscript_lean_map.json` and the generated
`submission/current/theorem_lean_concordance.md`. The frozen manuscript and
pinned Lean/Mathlib dependencies were not changed.

| Item | Current Lean entry points | Audited scope |
|---|---|---|
| A1 — variance-envelope integration | `FiniteSupportLawData.rawLogMGF_hasDerivAt`, `rawTiltMean_hasDerivAt`, `rawLogMGF_second_deriv`, `rawTiltMean_strictMono`, `rawLegendreRate_gt_meanEnvelopeRight_of_interval`, `rawLegendreRate_gt_meanEnvelopeLeft_of_interval`, `rawLegendreRate_gt_meanEnvelopeRight_endpoint`, `rawLegendreRate_gt_meanEnvelopeLeft_endpoint` | Starts from a normalized finite weighted law with two distinct endpoint atoms of positive weight. The actual tilted mean has derivative equal to its positive tilted variance; the inverse tilt yields the actual Legendre optimizer. Continuous positive envelope and `V≤Q` on the whole tilt curve give the right/left integral comparisons. A positive-length strict-variance interval gives strictness. Endpoints use the actual atom costs and finite one-sided limits of the envelope integral, without assuming a Legendre-rate limit. Actual finite weighted upper/lower tail sums are included. |
| A2 — optimized factorial moments versus exact Chernoff | `finiteIntegerTailMass_le_factorialBound`, `finiteFactorialBound_le_chernoff_inf`, `hypergeom_factorial_candidate_formula_of_degree_le_population`, `hypergeom_factorial_candidate_eq_zero_of_population_lt_degree`, `hypergeomFactorialBound_lt_exp_neg_piecewiseRate`, `hypergeom_lower_factorial_chernoff_end_to_end`, `hypergeom_factorial_chernoff_support_exterior_end_to_end` | The comparison direction is `tail ≤ optimized factorial bound ≤ exact Chernoff infimum`; on the supported strict-rate domain, the bound is strictly sharper than `exp(-J)`. Ceiling minimizers, endpoint indices, and adjacent ties at integral cutoffs are proved. The frozen manuscript omits `j≤N` from the ordinary falling-factorial quotient and omits `d≤m` in the strict `I/J` sentence. At `N=7,k=m=3,d=j=8` the quotient is `0/0`; at `N=7,k=m=3,d=4`, `d>μ=9/7` but `J(d)` is outside its stated domain `[0,m]`. Separate zero branches prove the valid exterior result. This is the only requested group whose corrected Lean scope does not literally match the frozen manuscript wording; see `a2_factorial_denominator_audit.md`. |
| A3 — four symmetric binomial KL rates | `fourBinomialKLRate_comparisons`, `fourBinomialKLRateMax_eq_R1`, `canonicalPiecewiseRate_strict_improves_fourBinomialKLRateMax` | All four transformed rates are compared on the closed supported interval, with exact equality cases, including the degenerate identity case `k=m`, zero displacement, and both support endpoints. The piecewise rate strictly improves their maximum at every supported non-mean point under the canonical parameter hypotheses. |
| A4 — Bennett/Bernstein comparisons | `hypergeomBennettRate_lt_canonicalPiecewiseRate_upper/lower`, `hypergeomBernsteinRate_lt_canonicalPiecewiseRate_upper/lower`, `bernsteinRate_le_bennettRate_kernel`, `hypergeomBennettBernsteinRates_at_mean` | Uses the actual hypergeometric mean, variance scale, and canonical piecewise rate. Both supported tails include endpoints; strict claims exclude only the center. Kernel comparison and zero-deviation contact at the mean are proved. |
| A5 — integer and two-sided tails | `hypergeomUpperDeviationMass_eq_ceil_tail`, `hypergeomLowerDeviationMass_eq_floor_tail`, `hypergeomTwoSidedDeviationMass_eq_sum`, `hypergeom_integer_upper_deviation_piecewise_kl`, `hypergeom_integer_lower_deviation_piecewise_kl`, `hypergeom_integer_two_sided_deviation_piecewise_kl` | Actual finite hypergeometric events are identified with ceiling/floor integer tails, then bounded by the proved piecewise-KL rates. The support cutoff and two-sided combination are explicit. |
| B1 — fixed-sample margin gap | `hypergeomOptimalProxy_le_individualMarginGap`, `individualMarginGap_ge_parityDelta_all`, `individualMarginGap_strict_mono_reduced`, `hypergeomOptimalProxy_individualMargin_end_to_end` | The actual optimal hypergeometric proxy is bounded by the paper's two-branch `G_{N,m}(k)` certificate. Both parity cases yield the stated quantitative margin deficit and strictness for every legal interior population margin and every noncentral sample margin. |
| B2 — odd-central variational formula and contact | `oddCentralFiniteTiltSum_eq_supported`, `oddCentralSupportedProxy_eq_actual`, `oddCentral_supported_variational_maximum`, `oddCentral_every_nonzero_maximizer_stationary`, `oddCentralSupportedProxy_zero_eq_variance`, `oddCentral_boundary_every_nonzero_tilt_maximizes` | The finite sum is restricted to the exact hypergeometric support and agrees with the actual proxy, including the continuous zero-tilt variance value. For `0<m<N`, the actual supremum is attained at a nonzero tilt and every nonzero maximizing tilt satisfies `t ψ′(t)=2ψ(t)`; uniqueness is not assumed. For `m=0` or `m=N`, the law and proxy are identically zero and every nonzero tilt maximizes. |

The separate appendix statement `eq:Qexpand` is now covered by
`rescaledProxyExtension_joint_uniform_taylor` in
`ActualProxyUniformTaylor.lean`: for fixed `m,s`, one local radius works for
both parameters, the remainder is jointly continuous, and an integral
fifth-derivative remainder gives the displayed expansion through the sixth
cumulant. At `e=1/N` the rescaled factorial-family cumulants are identified
with the actual finite-law cumulants.

## Verification on the integrated root tree

- `lake build ExactHoeffding`: **passed**, 3,445 jobs, including all newly integrated contract modules.
- Full transitive Lean axiom audit: **passed**, 1,971 public theorems in 324 project modules; dependencies are only `propext`, `Classical.choice`, and `Quot.sound`.
- The live Lean declaration manifest: **passed**, 49 result rows, 377 declaration references and 339 distinct mapped theorem declarations, with source hashes and inspected types.
- Ten result rows have separately transcribed Lean proposition contracts; 39 more rows require manual proposition transcription. A contract is kernel checked, but its translation from the frozen TeX is still reviewed mathematically rather than inferred automatically by the checker.
- Baseline protection: **passed**; all 284 previously present mathematical modules and source lines are retained, and the frozen paper plus Lean dependency pins are unchanged.
- `checks/check_full_manuscript_concordance.py`: reports exactly one open row, A2, because the manuscript's two omitted domain conditions remain unamended. No whole-paper closure is claimed.

Logs are retained under `checks/logs/full_closure/final_*_20261017.log`.
