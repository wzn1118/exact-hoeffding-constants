# Mathematical integration status, 15 October 2026

Baseline: `ebf534362f596175a24fc33e9eebc1cd4145349f`.
Research branch: `research/kl-control-20261015`.

## A1--A5

- A1: analytic upper/lower scaled KL derivation completed with real and integer
  thresholds, exact support guards, endpoint limits and two-sided union bound.
- A2: proved dominance over the optimal uniform quadratic coefficient; kept
  fixed-law optimized numerical proxies separate. Computed directional local
  expansion and stated the nonzero Bernoulli equality mechanism.
- A3: inspected MZC v2, Greene--Wellner and Bardenet--Maillard formulas. Duality
  and factorial optimization are prior. Optimized factorial moments dominate
  exact Chernoff, so the new bound is not a strongest-literature claim.
  Original Hush--Scovel text was not obtained; its secondary restatement is
  marked separately. A second Lee--Kim exact-constant paper was not verified.
- A4: proved the explicit piecewise rate from `min(P,B)`, its switching roots,
  strict four-binomial-KL comparison, Bennett/Bernstein comparison and endpoint
  regularity. The six-page note retains the exact manuscript domain.
- A5: froze 20 parameter cases and all integer thresholds plus switching-point
  probes. All 292 high-precision checks pass. Seventeen rows exhibit a loss
  of the scaled-only KL rate to binomial KL, corrected by the piecewise rate.
  Exact tails and factorial moments use rational arithmetic. Numeric results
  verify finite instances; analytic claims rest on the written proof.

## Lean evidence

Lean 4.33.0 and pinned Mathlib 4.33.0 compile the entire integrated library.
Nine additional declarations are accepted, and thirteen audited declarations
use only `propext`, `Classical.choice` and `Quot.sound`. The principal analytic
chain L1--L8 remains incomplete, as specified in `proof_gap_register.md`.
No complete-formalization claim is made.

The source statements of existing Lean theorems were preserved. Scoped
imports replace the broad Mathlib import; dependency revisions are locked.

## Delivery

The manuscript and its original supplement are maintained separately from
`research/tail_bounds/minimum_variance_tail.pdf`. The latter includes author
copyright, complete proof, bibliography and a documented comparison boundary.
The research branch and PR are a reviewable research milestone; PR status and
remote checks are recorded in the final delivery report after publication.
