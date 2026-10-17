# A1 final scope audit — 2026-10-17

## Scope and evidence boundary

Read-only review of the root working tree at
`/data/odd_proxy/github_publication/exact-hoeffding-constants`; only this
report is written in the reviewer's private tree. No Lean job or axiom audit
was started for this review, and no manuscript, theorem source, or root file
was edited.

The frozen target is `submission/current/manuscript.tex`, lines 1349–1382,
Theorem `A:integration` and its proof. The target is identical to
`submission/integrated/combined_manuscript.tex`; both SHA256 values at review
are `b1bb1e3df8d8b651c4872692a8b0f4424541b4e9b3a5576d39a2be485d26e23f`.
The root Git HEAD is `8b75977b138205c4ba402000b25d226d55994682`, but the
interfaces reviewed include the root's current uncommitted additions.
Consequently HEAD alone does not identify this source snapshot.

Conclusion at the level of statements: the new actual-law interfaces match
the theorem's nondegenerate finite-law domain, both interior directions,
the ordinary-mean case, finite-limit endpoints, and positive-length interval
strictness, including strictness at endpoints. This is a source/scope review,
not a replacement for the root's final whole-library build and axiom audit.
The separately identified `RawCalculus` elaboration issue was repaired during
this review; the updated evidence is recorded below.

## 1. Actual finite law and nondegeneracy

`FiniteSupportLawData` in `FiniteSupportTiltCurveOfLaw.lean` has a finite
index set, nonnegative weights, total weight one, and distinguished positive
minimum and maximum atoms. Its `lo_hi_ne`, `lo_strict`, and `hi_strict` force
two distinct endpoint values. This realizes the manuscript's `l < h` and
positive endpoint mass assumptions; no additional positive-variance
hypothesis is required by the new actual-law interfaces.

- `FiniteSupportLawData.mean0` is the ordinary weighted mean of `L.value`.
- `FiniteSupportLawData.centeredValue i = L.value i - L.mean0`.
- `FiniteSupportLawData.mean t` is the tilted mean of the centered values.
  Thus the manuscript's ordinary-coordinate tilted mean is
  `L.mean t + L.mean0`, not `L.mean t`.
- `FiniteSupportLawData.variance t` is the centered log-MGF's second
  derivative. `finiteLogMGF_second_deriv` identifies it with the actual
  tilted second moment minus the square of the tilted first moment.
- `FiniteSupportLawData.variance_pos` proves strict positivity for every
  real tilt from the two positive, distinct endpoint atoms.
- The generic `L.toTiltCurve hvar` constructor remains available for abstract
  adapters. The actual finite-law bridge
  `finiteSupportLawData_toTiltCurve_of_endpoints` supplies `L.variance_pos`
  internally, so A1 callers provide no positive-variance premise.

Zero interior weights and repeated interior values are allowed. Repeated
indices at an endpoint are excluded by the strict endpoint fields; a finite
probability law is represented with coincident atoms merged, as when its
index type is its set of distinct support values. The modules are weighted
finite-law statements. They do not themselves construct the pushforward law
of an arbitrary measurable random variable on an ambient probability space.
This is a representation boundary, not a stronger probabilistic hypothesis
on the distinct-value finite law described by the manuscript.

A one-atom law, `l = h`, or zero-mass endpoint is outside both the manuscript
statement and these interfaces. No degenerate conclusion is needed to match
`A:integration`; none should be attributed to it.

## 2. Definitions and centering

`FiniteSupportLawCentering.lean` defines the manuscript's quantities directly:

- `FiniteSupportLawData.rawLogMGF`: logarithm of the actual uncentered finite
  exponential sum;
- `FiniteSupportLawData.rawLegendreRate`: `sSup` of the actual candidates
  `t * v - L.rawLogMGF t` over all real `t`;
- `FiniteSupportLawData.rawLogMGF_eq_centered`: exact linear centering term;
- `FiniteSupportLawData.rawLegendreRate_eq_centered`: exact translation of
  the actual rate to `finiteSupportLegendreRate`;
- `FiniteSupportLawData.meanEnvelopeIntegralRight_shift` and
  `FiniteSupportLawData.meanEnvelopeIntegralLeft_shift`: exact translations
  of the displayed integrals, without extra integrability hypotheses.

`FiniteSupportLawIntegration.lean` defines `rawUpperTail` and `rawLowerTail`.
`FiniteSupportLawData.rawUpperTail_eq_sum` and
`FiniteSupportLawData.rawLowerTail_eq_sum` identify these with the actual
weighted events `X >= v` and `X <= v`. They are not free functions supplied
with a Markov-bound assumption.

The uniform envelope hypothesis is precisely
`forall t : Real, L.variance t <= Q (L.mean t + L.mean0)`.
The inverse-mean parametrization is onto the entire open support, so this
is the manuscript's variance bound expressed in the tilt coordinate.
`finiteSupportMeanInverse_spec` and `finiteSupportMeanInverse_unique`
provide that parametrization.

## 3. Interior comparison and actual tails

The following exact public names use `ContinuousOn Q (Ioo l h)` and strict
positivity of `Q` only on `Ioo l h`, with no global or endpoint regularity
assumption:

| Manuscript conclusion | Actual-law public theorem | Target domain |
| --- | --- | --- |
| right `I >= J` | `FiniteSupportLawData.rawLegendreRate_ge_meanEnvelopeRight` | `L.mean0 <= v < L.value L.hiIndex` |
| left `I >= J` | `FiniteSupportLawData.rawLegendreRate_ge_meanEnvelopeLeft` | `L.value L.loIndex < v <= L.mean0` |
| actual right Chernoff rate | `FiniteSupportLawData.rawUpperTail_le_exp_neg_rate_interior` | same right domain |
| actual left Chernoff rate | `FiniteSupportLawData.rawLowerTail_le_exp_neg_rate_interior` | same left domain |
| actual right envelope tail | `FiniteSupportLawData.rawUpperTail_le_exp_neg_meanEnvelope` | same right domain |
| actual left envelope tail | `FiniteSupportLawData.rawLowerTail_le_exp_neg_meanEnvelope` | same left domain |

The mean itself is included in both nonstrict domains. The zero-length
integral there is zero. The proof of the centered comparison explicitly
handles `v = D.mu`; this is not inferred from a punctured-domain theorem.
`finiteSupportLegendreRate_at_mean` supplies actual interior attainment at
the inverse mean and specializes at the ordinary mean to zero rate.

`FiniteSupportLawData.upperTail_le_exp` and
`FiniteSupportLawData.lowerTail_le_exp` derive the Markov inequalities from
the weights, for nonnegative and nonpositive tilts respectively. There is no
caller-supplied `hmark` in the actual-law conclusions.

## 4. Interior strictness

The direct tilted-witness interfaces are
`FiniteSupportLawData.rawLegendreRate_gt_meanEnvelopeRight` and
`FiniteSupportLawData.rawLegendreRate_gt_meanEnvelopeLeft`.
They require a strict gap at a tilt strictly between zero and the optimizer,
with the correct ordering on the negative side.

`FiniteSupportLawMeanGap.lean` supplies the manuscript's mean-coordinate
conditions rather than leaving the tilt witness to the caller:

- `FiniteSupportLawData.rawLegendreRate_gt_meanEnvelopeRight_of_mean_gap`;
- `FiniteSupportLawData.rawLegendreRate_gt_meanEnvelopeLeft_of_mean_gap`;
- `FiniteSupportLawData.rawLegendreRate_gt_meanEnvelopeRight_of_interval`;
- `FiniteSupportLawData.rawLegendreRate_gt_meanEnvelopeLeft_of_interval`.

The interval versions quantify `exists a b` with `mu <= a < b <= v` on the
right, or `v <= a < b <= mu` on the left, and strict variance comparison at
every point of `Ioo a b`, using the actual inverse mean. These are faithful
to a positive-length interval between mean and target. The proof chooses an
interior point and constructs its actual tilt. No interval is possible at
`v = mu`, and no strictness is claimed there.

The actual strict tail consequences also exist as
`FiniteSupportLawData.rawUpperTail_lt_exp_neg_meanEnvelope` and
`FiniteSupportLawData.rawLowerTail_lt_exp_neg_meanEnvelope`, initially in the
tilt-witness formulation. Combining them with the already proved interval
witness conversion is valid; the manuscript only explicitly requires strict
rate comparison.

## 5. Finite one-sided endpoint limits

`FiniteSupportLawEndpointIntegration.lean` uses exactly the finite limits
of the displayed raw-coordinate integrals:

- `FiniteSupportLawData.rawLegendreRate_ge_meanEnvelopeRight_endpoint`;
- `FiniteSupportLawData.rawLegendreRate_ge_meanEnvelopeLeft_endpoint`;
- `FiniteSupportLawData.rawUpperTail_le_meanEnvelope_endpoint`;
- `FiniteSupportLawData.rawLowerTail_le_meanEnvelope_endpoint`.

Their `Jlim : Real` and `Tendsto` hypotheses express the manuscript's finite
one-sided limits at `h` or `l`. No limit or continuity of the Legendre rate,
no value of `Q` at an endpoint, and no positivity of `Q` on a closed support
are assumed. These names should be used in the final concordance instead
of relying only on the older `FiniteSupportEndpointEnvelope` interfaces,
which carry stronger regularity or explicit rate-limit assumptions.

The exact endpoint identifications are independently supplied by
`FiniteSupportLawEndpointRates.lean`:

- `FiniteSupportLawData.rateCandidate_tendsto_atTop`;
- `FiniteSupportLawData.rateCandidate_tendsto_atBot`;
- `FiniteSupportLawData.legendreRate_hi`;
- `FiniteSupportLawData.legendreRate_lo`.

Their ordinary-coordinate versions are
`FiniteSupportLawData.rawLegendreRate_hi` and
`FiniteSupportLawData.rawLegendreRate_lo` in `FiniteSupportLawMeanGap.lean`.
They prove `-Real.log` of the actual positive endpoint weight.
`FiniteSupportLawData.upperTail_at_hi` and
`FiniteSupportLawData.lowerTail_at_lo` identify the events with the same
endpoint atoms. No endpoint identity is assumed as a theorem hypothesis.

## 6. Strictness at endpoints

`FiniteSupportLawRawEndpointStrict.lean` contains both strictly signed tilt
and positive-length mean-interval formulations. Exact interval names are:

- `FiniteSupportLawData.rawLegendreRate_gt_meanEnvelopeRight_endpoint_of_interval`;
- `FiniteSupportLawData.rawLegendreRate_gt_meanEnvelopeLeft_endpoint_of_interval`;
- `FiniteSupportLawData.rawUpperTail_lt_meanEnvelope_endpoint_of_interval`;
- `FiniteSupportLawData.rawLowerTail_lt_meanEnvelope_endpoint_of_interval`.

The interval domain is `mu <= a < b <= h` on the right and
`l <= a < b <= mu` on the left. Its open interior supplies a strictly
positive or negative tilt via the actual inverse mean. Thus intervals may
touch the mean or the target endpoint, as in the manuscript.

The corresponding tilt-witness names are
`FiniteSupportLawData.rawLegendreRate_gt_meanEnvelopeRight_endpoint`,
`FiniteSupportLawData.rawLegendreRate_gt_meanEnvelopeLeft_endpoint`,
`FiniteSupportLawData.rawUpperTail_lt_meanEnvelope_endpoint`, and
`FiniteSupportLawData.rawLowerTail_lt_meanEnvelope_endpoint`.

These results retain only open-support continuity/positivity and the same
finite integral limit. They do not assume a positive limiting gap: the
proved identities and outward monotonicity in `FiniteSupportEndpointStrict`
preserve a fixed positive interior gap before taking the limit. Therefore
endpoint strictness is not lost by merely passing a strict inequality to
a limit. The new endpoint statements resolve that specific logical issue.

## 7. Remaining boundaries and pending verification

1. **Raw calculus repair is integrated; final library audit is pending.**
   `FiniteSupportLawRawCalculus.lean` declares
   `FiniteSupportLawData.rawLogMGF_hasDerivAt`,
   `FiniteSupportLawData.rawTiltMean_hasDerivAt`,
   `FiniteSupportLawData.rawLogMGF_second_deriv`, and
   `FiniteSupportLawData.rawTiltMean_strictMono` with the correct actual-law
   meanings. The initial root source and `/tmp/a1_raw_calculus_build2.log`
   had a first-derivative elaboration failure. During this review, the repair
   from private commit `630f86f` passed compilation with `lean_exit_code=0`
   in
   `/data/hoeffding_full_20261015/evidence/finite_support_raw_calculus_private1.log`.
   By the final read at `2026-10-17T04:15:13Z`, root and repaired private
   source matched SHA256
   `653b565478bb0b19a73b2f07dc965f702f8208802e1e6a72bffaa34c73323568`,
   and the root `FiniteSupportLawRawCalculus.olean` existed. The repair keeps
   all four statements, replacing only the first proof. The earlier failure
   is therefore not an outstanding source-scope gap; final library/audit
   results remain to be confirmed by root.
2. **Proof-route formulas versus theorem conclusions.** The proof prose
   writes `I'(v)=t(v)` and `I''(v)=1/V(v)`. No public generic actual-law Lean
   theorem with these derivative conclusions was found in the reviewed
   `FiniteSupport*` modules. The comparison is instead proved directly by
   inverse-mean attainment, finite log-MGF calculus, and integral change of
   variables; hence these two derivative formulas are not assumptions or
   missing dependencies of the displayed theorem conclusions. If the final
   claim is literally formalization of every auxiliary identity in the
   proof prose, they remain an explicit separate obligation. Do not cite
   `rawLogMGF_second_deriv` as an `I''` theorem: it differentiates log-MGF,
   not the Legendre transform.
3. **Support domain.** The notation `v >= mu` / `v <= mu` in the displayed
   tail line is read together with the preceding definition of `J_Q`, and
   the finite-limit continuation at `l,h`. The audited valid targets are
   the closed half-supports. `rawLegendreRate` is real-valued `sSup`, not an
   extended-real rate outside support; no off-support Legendre conclusion
   is part of these theorems. `J_Q` is not defined by the displayed formula
   beyond support under the manuscript's stated assumptions. No blanket
   whole-real-ray claim should be extracted from the abbreviated tail line.
4. **Ambient random-variable adapter.** Actual finite weighted events are
   fully represented. A general measurable-space pushforward constructor
   is not among these interfaces. If the release describes the Lean result
   as a theorem taking an arbitrary measurable random variable as input,
   that description would exceed the reviewed API. The finite-law theorem
   itself agrees with the manuscript's law-level assertion.
5. **Final audit remains the root's responsibility.** No new `sorry`,
   `admit`, or `axiom` declaration was found by source search in the reviewed
   actual-law modules, but source search is not a kernel axiom audit. The
   root is currently rebuilding the library and auditing the declarations.
   This report deliberately does not mark global completion.

## Evidence snapshot

The independently verified strict-endpoint chain is committed in the private
branch as `e7f3844bc4553223e74e355efb96bd1d3a11e5ba`,
`d160eb471b25a10755ceb09f25cdf5946cffc203`, and
`cce3ba40abbe89a42e0f1468f73d366f01f67594`.
The last compilation exited zero with no output:
`/data/hoeffding_full_20261015/evidence/finite_support_law_raw_endpoint_strict3.log`.
The root's copied `FiniteSupportLawRawEndpointStrict.lean` matches SHA256
`9fc0a1a145e93dd03d4070e0e958b6e69cd4a748b2a6130c11d901a11c45ef05`.

Other root source hashes checked:

| File | SHA256 |
| --- | --- |
| `FiniteSupportLawCentering.lean` | `29a3166a6dfbb803d8c3b1ffe9e14d80a7c8344190e573196e39349873a6d5d9` |
| `FiniteSupportLawIntegration.lean` | `ce5fb7e106099afa15f73c22f1ca057ab18e58427f63d80e8a6025ad327574ad` |
| `FiniteSupportLawMeanGap.lean` | `6a112e418fef8efdb4f59e471b9f21192e415d711423d466620dd24b0f6a718e` |
| `FiniteSupportLawEndpointRates.lean` | `75029b6d1e96e0265ac474f131c815968b47f9ec395927f379a0db71a7e84f45` |
| `FiniteSupportLawEndpointIntegration.lean` | `b4473e92fc304428dd1d3d3a717757595d7e55fce9940e769ae634d86775e3a0` |
