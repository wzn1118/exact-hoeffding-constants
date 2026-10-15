# F-07 real-margin probability and derivative foundation

The following results concern the actual finite mass function in
`realMarginMass`, not merely a postulated factorial-moment sequence.

- `cbfdee3`: scaled Chu--Vandermonde; mass sum one; ordinary mean `m*p`;
  positive masses for `|d|<1/N` at `e=1/N`, `2*m≤N`; real adjacent recurrence;
  joint analyticity away from denominator zeros; reflection and MGF positivity.
- `69dbaab`: exact agreement with every physical hypergeometric mass;
  Bernoulli one-draw identity; real two-draw curvature formula, sharp upper
  bound and necessary curvature equality (`N=2*k`, `t=0`).
- `2904613`: all-degree factorial moment formula for actual masses;
  moments through order six and cumulants two through four match the
  manuscript's exact real-margin formulas; explicit positive
  `RealRecurrenceLaw` and degree-at-least-three sharp all-tilt curvature.
- `4fef803`: actual second/third logarithmic derivatives at zero and actual
  balanced fourth derivative, plus an explicit nonempty probability
  neighborhood for real imbalance at every integer population.

## Kernel evidence

- `evidence/real_margin_masses4.log`: exit 0.
- `evidence/real_margin_bridge_moments5.log`: physical bridge exit 0.
- `evidence/real_margin_recurrence9.log`: real recurrence bridge and
  two-draw curvature/equality exit 0.
- `evidence/real_margin_cumulants10.log`: all moments/cumulants and recurrence
  bridge exit 0, no warnings.
- `evidence/real_margin_logderivatives11.log`: exit 0, no warnings.

The evidence directory is `/data/hoeffding_full_20261015/evidence`.
The `RealMarginRecurrenceLaw` module imports root's proved
`RealRecurrenceCurvature`; compile after that module. No source axioms,
`sorry`, or optimizer assumptions are introduced.

## Current next layer

`RealMarginActualProxy` and `RealMarginFiniteResponse` construct an explicit
jointly analytic actual quotient and the fixed-population critical branch.
They are under compilation and are not counted as verified here. Complete
fixed-population global localization, analytic optimizer identification,
reflection, and the exact `T/A` response remain subsequent steps.
