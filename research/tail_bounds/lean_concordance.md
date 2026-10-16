# Piecewise KL theorem concordance

Domain: natural `N,k,m` satisfying `3 ≤ m ≤ k`, `2*k ≤ N`, `2*m < N`.
Thresholds are real. The support is `[0,m]`; `μ=m*k/N`.

| Result | Lean declarations |
|---|---|
| Explicit roots and `0<r₋<μ<r₊<m` | `kl_switching_points_full_domain` |
| `P≤B` exactly between the roots | `kl_quadratic_envelope_le_binomial_iff` |
| KL arguments remain in `(0,1)` on closed support | `scaledKL_argument_mem_Ioo` |
| Actual variance satisfies both Riccati envelopes | `hypergeom_kl_riccati_data` |
| Stitched right and reflected left comparison | `stitched_right_fenchel_bound`, `stitched_left_fenchel_bound` |
| Upper and lower tails, including `v=m` and `v=0` | `hypergeom_upper_tail_piecewise_kl`, `hypergeom_lower_tail_piecewise_kl` |
| `J>I_B` for `v≠μ` | `canonicalPiecewiseRate_strict_improves_binomial` |
| `J≥I_P`; equality exactly on `[r₋,r₊]` | `canonicalPiecewiseRate_quadratic_comparison` |
| Actual finite Legendre supremum and boundedness | `hypergeomKLRate`, `hypergeomKLRate_bddAbove` |
| Strict `I>J`, including support endpoints | `hypergeomKLRate_strict_piecewise` |
| Combined tail and comparison theorem | `hypergeom_piecewise_kl_end_to_end` |

The numerical matrix and SymPy identities are not premises of these Lean
statements. The two envelopes are supplied by the existing Jacobi/Riccati
formalization. The direct proof uses translated Bernoulli trajectories and
Fenchel contact identities, so it does not require an unformalized inverse
of the tilted-mean map.

This table covers the piecewise-rate theorem of the tail note. The separate
sections on four symmetry-related binomial rates, optimal uniform quadratic
comparisons, Bennett/Bernstein comparisons and optimized factorial moments
are additional results of the research note; they are not substituted for
any hypothesis of the displayed piecewise-rate theorem.
