# Problem A3 Literature Boundary Audit

This is a provenance audit for the tail/KL work, not a priority claim. The
repository's theorem-priority document remains the source of the manuscript's
formal attributions; this file records what the new scripts do and do not
compare.

| Source/result | Relation to the A work | Status here |
| --- | --- | --- |
| Hoeffding (1963) | Sampling without replacement is controlled by the corresponding with-replacement convex/MGF comparison; binomial Chernoff/KL is therefore a classical reference target | Baseline only; no originality claim |
| Serfling (1974) | Finite-population-correction quadratic tail benchmark | `serfling_bound` is a reference column; no global ordering claim |
| Chvatal (1979) | Classical KL/Chernoff-style hypergeometric tail bound | The exact rational sweep is a validation of this benchmark, not a new theorem |
| Hush--Scovel (2005) | Improved hypergeometric concentration result with a different stated bound/form | Formula is not reconstructed in the current script; no superiority claim |
| Bardenet--Maillard (2015) | Serfling/Bernstein-type without-replacement bounds and empirical variants | Related reference; not identified with the scaled-Bernoulli KL envelope |
| Greene--Wellner (2017) | Exponential hypergeometric bounds with their own parameterization and regimes | Related reference; not numerically ordered against every matrix row |
| Barber (2024) and erratum (2025) | Weighted exchangeable Hoeffding/Bernstein bounds, not just a fixed hypergeometric count | Separate target; no direct tail comparison claimed |
| Lee--Kim (2026) | Two-level reduction, exact hypergeometric variational identity, and finite exchangeability coefficient bounds | Existing provenance in `docs/theorem_priority_2026-10-11.md`; `V_global` remains conditional/open in Lean |
| Atouani--Marchal--Arbel (2025) | Three-mass optimal proxy, relevant to the `m=2` boundary | Not a general hypergeometric tail theorem |

## Consequence for the A claims

The scripts establish a reproducible comparison matrix and a symmetry-
transposed KL diagnostic. They do **not** establish that the scaled-Bernoulli
envelope is the first or globally strongest hypergeometric tail bound. Any
paper statement must call the classical KL/Chernoff rows a comparison target
and cite the relevant source for the parameter regime.

The exact finite tail is always the reference value in the matrix. A row for
`V_global=C_N^*m(N-m)/(4N)` is conditional on the manuscript's sharp constant
theorem; a fixed-law numerical `sup_t 2*psi(t)/t^2` is only a diagnostic and
must not be presented as a certified bound.

## Source records

The local primary-source inventory is `refs/references.json`,
`refs/references.bib`, and `docs/theorem_priority_2026-10-11.md`. Chvatal and
Hush--Scovel are recorded here as literature boundaries because their records
are not currently included in the repository bibliography. Adding them to the
paper bibliography would require a separate citation/metadata update and is
not part of this branch's code certificate.
