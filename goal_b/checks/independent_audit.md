# Goal B: independent proof audit

Date: 16 October 2026. The analytic input lemmas come from the companion
formal development at `formal/full-closure-20261015` (SHA `8687c3d`). The
fixed-sample assembly is in `ExactHoeffding/GoalBFixedSample.lean`.

## Reviewed claims

1. The variance proxy `S(N,k,m)` is the unnormalized supremum
   `2 * centered-logMGF / t^2`. The companion
   `normalizedHypergeomProxy` is `4N/[m(N-m)]` times `S`.
2. Success and sample complementation preserve the centered proxy, so the
   proof may reduce to `min(k,N-k)` and `min(m,N-m)`.
3. For the reduced sector `m <= k < N/2`, the scaled Bernoulli envelope applies,
   with equality only at the singleton input.
4. `artanh(d) >= d + d^3/3` is proved by a derivative calculation, and the
   first off-center margins are `2/N` for even `N` and `3/N` for odd `N`.
5. For `k < m`, the sharp curvature ceiling and the exact product identity
   give the second branch of the separation.
6. Exact rational algebra closes the announced even and odd `Delta(N,m)`
   bounds, including the conversion from normalized to unnormalized proxies.
7. The zero-tilt limit gives the central ordinary-variance lower bound; this
   is enough for the all-`N` argmax theorem. The paper's separate strict odd
   central-value statement is retained as an analytic value result.
8. Boundary populations and complement cases are covered by the hypotheses
   and the parity split; the existing one-/two-draw identities remain in the
   reproducibility checks.

## Kernel verification

The following declarations are the new public endpoints:

- `hypergeomOptimalProxy_fixed_sample_extremizers`
- `hypergeomOptimalProxy_fixed_sample_gap_even`
- `hypergeomOptimalProxy_fixed_sample_gap_odd`
- `odd_normalized_proxy_fixed_sample_extremizers`
- `even_normalized_proxy_fixed_sample_extremizers`
- `odd_normalized_proxy_fixed_sample_gap`
- `even_normalized_proxy_fixed_sample_gap`

`lake build ExactHoeffding.GoalBFixedSample` and the umbrella
`lake build ExactHoeffding` pass in the pinned project. The dedicated
`#print axioms` audit reports only `propext`, `Classical.choice`, and
`Quot.sound` for every new public theorem. The repository-wide generated audit
contains the same endpoints.

## Independent computational audit

The verifier has separate `Fraction` (exact rational) and centered finite-MGF
numeric paths. The frozen release passes 67,570 rational off-center
comparisons for `N <= 60`, 1,560 optimized proxy checks for `N <= 18`, and
18 one-/two-draw checks. These checks are independent error detection; the
all-finite theorem is the Lean-checked analytic argument.

## Scope and provenance

The proof uses the previously established sharp all-tilt curvature bound and
scaled Bernoulli envelope as explicit inputs. For odd `N` and arbitrary
`m >= 3`, the central proxy value is kept as the exact finite-sum variational
quantity in the manuscript; no elementary closed form or uniqueness of its
optimizing tilt is asserted. No unpublished Lee--Kim manuscript is compared.
