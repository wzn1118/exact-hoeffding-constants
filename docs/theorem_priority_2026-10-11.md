# Theorem-level provenance and priority

**Manuscript:** *Exact Hoeffding Constants for Finite Exchangeable Sequences*, Zinan Wang, 11 October 2026.  
**Source edition:** `main`, 28-page article with six-page technical supplement.  
**Review date:** 11 October 2026.

## Statement-by-statement concordance

| Manuscript result | Closest established result | Exact boundary of the contribution |
| --- | --- | --- |
| Exact exchangeability constant, Theorem `thm:exchange` | Lee–Kim (2026), Theorem 1, Proposition 1, Remark 1 | Lee–Kim prove a rate-optimal explicit upper coefficient `Γ_N = 1 + 3/(2N) + O(N^{-2})`, a variance lower bound and the exact hypergeometric variational identity. The present theorem evaluates that variational problem for each `N`, proving `C*_N=N/(N-1)` for even `N` and `C*_N=1/((N-1)artanh(1/N))` for odd `N`. Its first-order coefficient is exactly 1. |
| Two-level reduction, Proposition `prop:two_level` | Lee–Kim (2026), Proposition 2 | Structural reduction imported with attribution. The manuscript supplies an adapted proof, then applies the reduction to exact optimization. |
| Hypergeometric variational identity, Proposition `prop:variational` | Lee–Kim (2026), Remark 1 and proof of Theorem 1 | Exact optimization framework imported with attribution; evaluation of the supremum is the new result. |
| All-tilt curvature inequality, Theorem `thm:curvature` | Lee–Kim (2026), Lemma 4; Greene–Wellner (2017), hypergeometric exponential bounds | The manuscript supplies an all-real-tilt inequality `Var_t(H) ≤ min{k(N-k),m(N-m)}/[4(N-1)]`. Its stationary-branch argument and all-degree polynomial positivity certificate apply uniformly over the finite-population parameters. The cited bounds do not present this all-tilt inequality in this form. |
| Poisson–binomial admissibility, Lemma `lem:PB` | Jacobi zero theorem (Szegő); Kou–Ying (1996); stable-polynomial literature (Borcea–Brändén–Liggett 2009) | Real-rooted generating-function factorization is classical. Its use to restrict the stationary mean–variance curve is part of the present proof architecture. |
| Polynomial stationary certificate, Lemmas `lem:universal` and `lem:identity` | Classical Jacobi ODE and coefficient algebra | Exact stationary resultant and polynomial with nonnegative monomial coefficients in `j-3` and `h+r`. Verified separately through the independent algebraic checker. |
| Parity-uniform Laplace comparison, Theorem `thm:main_laplace` | Lee–Kim (2026), Lemma 4; hypergeometric concentration literature | Theorem controls the full log-Laplace transform by a scaled Bernoulli proxy for `N≥7, 3≤m≤k≤⌊N/2⌋, N>2m`, including the even balanced margin. Its quadratic mean–variance barrier and discriminant certificate are absent from the named precursor theorems. |
| Optimal proxy for three support points, Lemma `lem:threemass` | Atouani–Marchal–Arbel (2025), Theorem 3.2 and Corollary 3.3 | Closed-form proxy formula imported with explicit attribution. |
| Two-draw hypergeometric extremization, Proposition `prop:odd2` | Atouani–Marchal–Arbel (2025), Theorem 3.2 | Hypergeometric specialization, maximization over success counts, and sharp comparison with the singleton candidate are added calculations. |
| Odd-population extremizer classification, Theorem `odd:thm:odd` | Lee–Kim (2026), Proposition 1 and Remark 1 | Identifies the exact extremizing sample sizes and nearest-balanced success counts for every odd `N`, beyond the variance-level lower bound. |
| Fourth-order optimized proxy, Theorem `thm:odd_expansion` | Atouani–Marchal–Arbel (2025), Remark 3.6; Arbel–Marchal–Nguyen (2020), cumulant methods | Expansion is in reciprocal population size at the optimizing tilt, with fixed sample size and imbalance; the prior three-mass local Taylor expansion is in the Laplace argument. |
| Concentration for exchangeable sample means relative to de Finetti extremal means | Gottschling–Caprio (2026), main theorems | Infinite exchangeability with an unweighted sample-mean target; a separate centering and hypothesis class from arbitrary finite centered contrasts. |
| Weighted finite-exchangeability predecessors | Barber (2024), Theorem 3.1 and 2025 erratum | Existing weighted inequalities involve a harmonic inflation correction. Lee–Kim already establish the order-`1/N` improvement; the present paper determines its sharp coefficient. |

## Direct theorem comparisons

### Lee and Kim (arXiv:2608.04900v2)

- **Theorem 1** gives `Γ_N` and establishes `Γ_N = 1+3/(2N)+O(N^{-2})`.
- **Proposition 1** proves `C*_N ≥ N/(N-1)` for even `N` and `C*_N ≥ (N+1)/N` for odd `N`.
- **Remark 1** identifies `C*_N` as an exact finite hypergeometric log-MGF supremum. The remaining first-order gap is explicitly posed in the discussion following Proposition 1.
- **Proposition 2** is the two-level maximization theorem. Its proof is used with attribution in the present paper.
- **Lemma 4** bounds hypergeometric log-MGFs by a martingale argument; it gives no pointwise all-tilt curvature or sharp parity-dependent proxy identity.

The exact even coefficient equals Lee–Kim's lower bound. For odd `N`, the optimal coefficient is strictly greater than their variance lower bound, and it remains strictly smaller than the universal coefficient `N/(N-1)`. This resolves the open first-order gap through the exact finite-`N` evaluation.

### Atouani, Marchal, and Arbel (arXiv:2510.06132)

- **Theorem 3.2** gives the closed-form optimal proxy for a class of three-mass distributions with the middle-mass restriction.
- **Corollary 3.3** characterizes strict sub-Gaussianity within that class.
- **Remark 3.6** addresses a local Taylor expansion in the exponential tilt.

The manuscript cites Theorem 3.2 as the source of the three-mass proxy formula; its two-draw optimization depends on the hypergeometric parameterization. The higher-order finite-population expansion has a distinct expansion parameter and global optimality condition.

### Related work with separate mathematical targets

- **Barber (2024; erratum 2025):** weighted Hoeffding/Bernstein inequalities for exchangeable sequences, harmonic-size correction.
- **Greene and Wellner (2017):** exponential bounds for hypergeometric tails.
- **Bardenet and Maillard (2015):** finite-population sampling without replacement and Serfling-type correction.
- **Gottschling and Caprio (2026):** bounds involving extremal de Finetti component means under infinite exchangeability.
- **Arbel, Marchal, and Nguyen (2020):** general optimal sub-Gaussian proxy and strict sub-Gaussianity criteria.
- **Kou and Ying (1996); Szegő (1975):** Jacobi structure and root-location input.

## Independent certificate map

The reconstructed algebra and finite-sum checks are in `checks/verify_independent_certificates.py`.

1. Reconstructed stationary Riccati elimination and the constant/leading coefficients of `F(u,v)`.
2. Identity `-16(N-1)F((j+x)/2,B)` against the full stationary polynomial certificate.
3. Exact nonnegative-coefficient expansion of the decisive polynomial in `(j-3,h+r)`.
4. Independently parameterized residual, Poisson–binomial admissibility, sum-of-squares, and determinant identities for the Laplace envelope.
5. Exact factor expansions proving `λ>0`, `α>0` and positive definiteness.
6. Direct check of the hypergeometric polynomial ODE and finite-sum MGF comparisons.

## Bibliography of directly inspected primary sources

1. Seongchan Lee and Ilmun Kim, *A Sharper Hoeffding Bound for Weighted Sums of Exchangeable Random Variables*, arXiv:2608.04900v2 (29 September 2026). https://arxiv.org/abs/2608.04900
2. Soufiane Atouani, Olivier Marchal, and Julyan Arbel, *Optimal sub-Gaussian variance proxy for 3-mass distributions*, arXiv:2510.06132 (2025). https://arxiv.org/abs/2510.06132
3. Rina Foygel Barber, *Hoeffding and Bernstein inequalities for weighted sums of exchangeable random variables*, Electronic Communications in Probability 29 (2024), DOI 10.1214/24-ECP620; Erratum, ECP 30 (2025), DOI 10.1214/25-ECP715.
4. Julyan Arbel, Olivier Marchal, Hien D. Nguyen, *On strict sub-Gaussianity, optimal proxy variance and symmetry for bounded random variables*, ESAIM: Probability and Statistics 24 (2020), 39–55. https://doi.org/10.1051/ps/2019018
5. Evan Greene and Jon Wellner, *Exponential bounds for the hypergeometric distribution*, Bernoulli 23 (2017), 1911–1950. https://doi.org/10.3150/15-BEJ800
6. Rémi Bardenet and Odalric-Ambrym Maillard, *Concentration inequalities for sampling without replacement*, Bernoulli 21 (2015), 1361–1385. https://doi.org/10.3150/14-BEJ605
7. Nina M. Gottschling and Michele Caprio, *Hoeffding-Style Concentration Bounds for Exchangeable Random Variables*, arXiv:2603.10190v2 (2026). https://arxiv.org/abs/2603.10190
8. S. G. Kou and Z. Ying, *Asymptotics for a 2×2 table with fixed margins*, Statistica Sinica 6 (1996), 809–829.

The concordance reports the identities and theorem ranges of the sources listed above, with emphasis on the 2025–2026 overlap.
