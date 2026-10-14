# Hypergeometric tail literature audit

Audit date: 15 October 2026. Scope: primary-source comparisons for the
scaled-Bernoulli variance envelope and the piecewise rate in
`research/tail_bounds/minimum_variance_tail.tex`.
This document does not edit the manuscript or assert exhaustive priority.

## Main conclusions

1. The ordinary hypergeometric binomial KL bound is classical
   (Hoeffding--Chvatal). Swapping the sample size and success count is
   explicit in Mannalath--Zapatero--Curty (MZC), Proposition 1. Their paper
   also explicitly discusses complementation. These transformations and
   the minimum of the resulting bounds are not new methods.
2. **Use arXiv:2510.19726v2, not v1, for factorial moments.** Version 1
   (22 October 2025) has only the two binomial-based bounds. Version 2
   (17 December 2025), Proposition 2, supplies the optimized
   hypergeometric factorial-moment bound. Journal metadata identifies
   publication on 3 June 2026, *Communications in Statistics - Theory and
   Methods* 55(20), 6938--6943, DOI 10.1080/03610926.2026.2676012.
3. At an integer threshold, the optimized factorial-moment bound is at
   most the exact-MGF Chernoff bound and therefore at most any valid
   MGF-envelope Chernoff bound. Thus the proposed piecewise KL expression
   cannot be advertised as improving the optimized factorial bound.
4. The specific additional object in the current note is the explicit
   rate obtained by integrating `1/min(P,B)`, with its two switching
   points, tangent corrections, and proved dominance over the four
   binomial KL rates on the stated canonical domain. These formulas do
   not occur in the inspected MZC, Greene--Wellner, or Bardenet--Maillard
   texts. The identity `I''=1/V` and Chernoff optimization are standard
   exponential-family/convex-duality operations; novelty should rest on
   the specific variance envelope and the resulting comparison theorem.
5. One Lee--Kim paper is verified: arXiv:2608.04900v2. Its bound has
   inflation `1+3/(2N)+O(N^-2)`, not the exact parity constants. No second
   exact-constant paper was identified by the bounded primary searches
   described below. A negative search is not proof of nonexistence.

## Notation and classical KL benchmark

Let `H ~ Hypergeometric(N,k,m)`, with `1<=k,m<=N-1`,
`mu=km/N`, support `l=max(0,k+m-N)` to `h=min(k,m)`, and

\[
D(x\Vert p)=x\log(x/p)+(1-x)\log((1-x)/(1-p)).
\]

For an upper threshold `v>=mu` in the support, the classical bound is

\[
\Pr(H\ge v)\le\exp\{-mD(v/m\Vert k/N)\}.
\]

For `v<=mu` the same exponent bounds `Pr(H<=v)`. These exponential bounds
hold for real thresholds by the Chernoff argument; rounding to the actual
integer event is normally tighter. MZC states its Proposition 1 for
integer `v>=mu+1`, a shared domain with the binomial-tail comparison used
there. The `+1` restriction belongs to their joint statement and should
not be imposed on the standalone KL inequality unnecessarily.

The transformations are exact distributional identities:

\[
H_{N,k,m}\overset d=H_{N,m,k},\qquad
m-H_{N,k,m}\overset d=H_{N,N-k,m},\qquad
k-H_{N,k,m}\overset d=H_{N,k,N-m},
\]
\[
N-k-m+H_{N,k,m}\overset d=H_{N,N-k,N-m}.
\]

Consequently four generally distinct binomial KL exponents at the same
original threshold are

\[
\begin{aligned}
R_1(v)&=mD(v/m\Vert k/N),\\
R_2(v)&=kD(v/k\Vert m/N),\\
R_3(v)&=(N-m)D((k-v)/(N-m)\Vert k/N),\\
R_4(v)&=(N-k)D((m-v)/(N-k)\Vert m/N).
\end{aligned}
\]

Both upper and lower tails use `exp(-max_j R_j)` in the appropriate
direction. A complementation reverses the event direction; applying an
upper-tail formula without reversing that event is incorrect.

For `m<=k<=N/2`, `R_1` dominates the other three. MZC discusses the
advantage of the binomial distribution with fewer trials, but describes
the comparison as indicated by simulations. The current note supplies a
short explicit proof using reciprocal second derivatives on its
canonical support. That proof is a comparison refinement, not a new
duality principle.

## Verified source table

| Source | Exact location | Verified statement and domain | Attribution boundary |
|---|---|---|---|
| MZC v2 | pp. 2--3, equations (1), (4), (6)--(9), Proposition 1 | Ordinary KL `exp[-mD(v/m||k/N)]`, swapped KL `exp[-kD(v/k||m/N)]`; ordinary beta `I_(k/N)(v,m-v+1)` and swapped beta `I_(m/N)(v,k-v+1)`. Joint stated domain: integer `v>=km/N+1`, with beta arguments positive / threshold within support. | Swapping, beta comparisons, and complement use are prior. |
| MZC v2 | p. 3, final symmetry paragraph | Simultaneous success/sample complements and the swapped complemented parameterization are explicitly given. | Do not label the fourfold symmetrized KL baseline new. |
| MZC v2 | p. 4, equations (10)--(17), Proposition 2 | Optimized falling-factorial Markov bound. See endpoint-correct optimizer below. | Factorial method and hypergeometric optimization are prior. |
| Greene--Wellner (2017) | p. 1915, Theorem 1, (2.4) | Explicit prefactor, finite-sampling quadratic and quartic exponents; `N>4`, `2<=m<k<=N/2`, `0<lambda<sqrt(m)/2`. | Quartic tail corrections already exist; they are not the optimized-proxy expansion in powers of `N^-1`. |
| Greene--Wellner (2017) | p. 1916, Theorem 3, (2.7), and p. 1917, Corollary 1, (2.9) | Bennett and Bernstein bounds with the exact hypergeometric variance; `1<=m<=min(k,N-k)`, positive deviation. | Exact variance / finite sampling in an exponential bound is not new. |
| Bardenet--Maillard (2015) | PDF pp. 9--10, Theorem 2.4 and Corollary 2.5; journal pp. 1369--1370 | Improved Hoeffding--Serfling correction `rho_m`; bounded finite population; `m<N` in theorem, `m<=N` in corollary. | Finite population correction and complementation for large samples are prior. |
| Bardenet--Maillard (2015) | PDF p. 6, Proposition 2.2, with proof pp. 6--7 | Reproves and attributes Serfling's log-MGF bound, formula below. | Original Serfling text not separately obtained in this audit; this primary research text explicitly gives and proves the stated version. |
| Lee--Kim (2026), arXiv v2 | pp. 3--4, Theorem 1, Proposition 1, Remark 1; Proposition 2 later | Inflation `Gamma_N=1+3/(2N)+O(N^-2)`; lower variance bounds; exact hypergeometric variational characterization; two-level reduction. | Their reduction is prior. Their inspected theorem does not give the final exact odd/even constants. |

### Greene--Wellner formulas in the present notation

Set `p=k/N`,
`v0=mp(1-p)(N-m)/(N-1)`, and `h0(z)=(1+z)log(1+z)-z`.
Theorem 3 gives, for `x>0` and `m<=min(k,N-k)`,

\[
\Pr(H-\mu>x)\le
\exp\{-v_0 h_0(x/v_0)\}.
\]

Their statement uses a strict tail. A `>=` version follows by continuity
of the bound when approaching a positive threshold from below. Corollary 1 is

\[
\Pr(H-\mu>x)\le
\exp\{-x^2/[2(v_0+x/3)]\}.
\]

Theorem 1, for `0<lambda<sqrt(m)/2`, is exactly

\[
\Pr((H-\mu)/\sqrt m\ge\lambda)
\le {1\over2\sqrt{2\pi}\lambda}
\sqrt{\frac{N-m}{N}
\frac{\sqrt m+2\lambda}{\sqrt m-2\lambda}
\frac{N-m+2\sqrt m\lambda}{N-m-2\sqrt m\lambda}}
\exp\left\{-\frac{2\lambda^2}{1-m/N}
-\frac13\left(1+\frac{m^3}{(N-m)^3}\right)
\frac{\lambda^4}{m}\right\}.
\]

This includes a nontrivial prefactor and a quartic term. It must not be
replaced by just its quadratic exponent in a numerical comparison.
Theorem 2 additionally gives uniform constants under both proportions
bounded away from zero and one. Such compact-proportion control also
predates the present project.

### Serfling / Bardenet--Maillard formulas

For a population in `[A,B]` and its without-replacement sum `S_m`,
Proposition 2.2 proves

\[
\log\mathbb E e^{t(S_m-m\bar x)}
\le \frac{(B-A)^2t^2m}{8}\left(1-\frac{m-1}{N}\right).
\]

The proposition states `t>0`; applying it to the negated population gives
the other sign. Bardenet--Maillard's sharper fixed-time tail is

\[
\Pr(S_m-m\bar x\ge x)
\le\exp\{-2x^2/[m\rho_m(B-A)^2]\},
\quad
\rho_m=\begin{cases}
1-(m-1)/N,&m\le N/2,\\
(1-m/N)(1+1/m),&m>N/2.
\end{cases}
\]

At `m=N` the sum is deterministic and positive-deviation tails are zero.
For the hypergeometric law, use `B-A=1`.

Hush--Scovel is summarized by Greene--Wellner p. 1912, (1.5), but its
original primary paper was not obtained in this audit. Accordingly it is
not certified here as an independently read source. The secondary
statement is
`Pr(H-mu>=x)<=exp[-2 alpha (x^2-1)]`,
`alpha=max(1/(m+1)+1/(N-m+1),1/(k+1)+1/(N-k+1))`, `x>0`.
Do not cite this audit as verification of the original paper's theorem
number or all original boundary conventions.

## Factorial optimizer and the sharp comparison boundary

For an integer `d` with `mu<d<=min(k,m)`, define

\[
F_j=\frac{(k)_{\underline j}(m)_{\underline j}}
{(N)_{\underline j}(d)_{\underline j}},\qquad 0\le j\le d,
\quad F_0=1.
\]

The Markov bound is `Pr(H>=d)<=min_j F_j`. Put

\[
r=\frac{Nd-km}{N+d-k-m}.
\]

The denominator is positive on the stated nondegenerate upper-tail
domain, and `0<r<=d`. Since

\[
\frac{F_{j+1}}{F_j}=\frac{(k-j)(m-j)}{(N-j)(d-j)},
\]

the ratio is below one exactly when `j<r`, equal when `j=r`, and above
one when `j>r`. Thus a valid minimizing order is `j*=ceil(r)`. If `r`
is integral, orders `r` and `r+1` tie when both belong to `[0,d]`.

MZC prints order `floor(r)+1`. This is also a minimizer in the interior,
but at `d=min(k,m)` one has `r=d`; their literal expression then asks for
order `d+1` and has a zero denominator. Use `ceil(r)` or
`min(d,floor(r)+1)` to cover the endpoint. Example: `N=7,k=3,m=3,d=3`
has `r=3`; the valid factorial bound is `1/35` and is exact, whereas the
printed fourth-order fraction is `0/0`. The inequality in their equation
(16) also includes equality after a strict-ratio condition; this only
affects the tie description, not the interior optimized value.

An exact rational check covered 65,792 tuples with `2<=N<=40`,
`1<=k,m<N`, and integer `mu<d<=min(k,m)`: `F_ceil(r)` equals the minimum
over all admissible orders in every case.

The following elementary proof gives a stronger conceptual comparison.
For any bounded nonnegative integer-valued `X` and integer `d>=1`, let

\[
F_d=\min_{0\le j\le d}\frac{\mathbb E\binom Xj}{\binom dj}.
\]

For `t>=0`, set `z=e^t-1>=0`. Then

\[
\mathbb E e^{tX}=\sum_{j\ge0}\mathbb E\binom Xj z^j
\ge F_d\sum_{j=0}^d\binom dj z^j=F_de^{td}.
\]

Therefore

\[
\Pr(X\ge d)\le F_d\le
\inf_{t\ge0}\mathbb E e^{t(X-d)}.
\]

With `I` the exact hypergeometric Chernoff rate and `J` the current
strict envelope rate, the ordering is

\[
\Pr(H\ge d)\le F_d\le e^{-I(d)}<e^{-J(d)}
\qquad(d>\mu).
\]

Apply the same argument to `m-H` for the lower tail. This is consistent
with the older factorial-versus-Chernoff literature cited by MZC:
Philips--Nelson (1995), Naveau (1997). The current short proof should be
presented as a transparent comparison, not as discovery of factorial
moment superiority.

## Boundary for the proposed piecewise rate

The note defines `B(u)=u(m-u)/m`, the established quadratic `P(u)`,
and integrates `1/min(P,B)` from the mean. In the stated canonical domain,
`P<B` near the mean and `B<P` near both support endpoints. The resulting
rate has a central scaled-Bernoulli KL segment and binomial KL tails with
affine tangent corrections. Its specific mathematical contributions are:

- explicit analytic switching points and a global finite formula;
- pointwise dominance of the four classical binomial KL rates on the
  specified domain, with strictness away from the mean;
- recovery of the exact local variance and improvement over the project's
  uniform quadratic envelope;
- a correct distinction between such improvements and optimized
  factorial-moment / exact-Chernoff performance.

The general operation `I''=1/V`, taking the minimum of two established
upper bounds, and optimizing a Bernoulli MGF are standard deductions.
The note's scientific weight depends on the previously proved `P` bound
and the specific switching/comparison statements, not a new general
Chernoff method. No inspected source claims this exact `min(P,B)` formula.
That bounded comparison supports a carefully scoped description, not a
claim that every existing finite-population tail bound is improved.

## Primary URLs, versions, and local records

Evidence directory:
The audit records the primary URLs and SHA-256 hashes below. Third-party
downloaded PDFs are not redistributed in this research addition.

- MZC v2: https://arxiv.org/abs/2510.19726v2 and
  https://arxiv.org/pdf/2510.19726v2 ; local
  `MannalathZapateroCurty_latest.pdf` and `.txt` (PDF itself identifies v2).
  SHA256 `fa398dc6b9dc683a1e19347fa187ed8bde4a9a9faf4f8d999eda7dbb6c65ef06`.
- MZC v1: https://arxiv.org/pdf/2510.19726v1 ; local
  `MannalathZapateroCurty2025v1.pdf` and `.txt`.
- MZC journal metadata: https://doi.org/10.1080/03610926.2026.2676012 and
  https://api.crossref.org/works/10.1080/03610926.2026.2676012 ; local
  `MZC_crossref.json`. The publisher PDF request returned HTTP 403;
  theorem checks use the public author preprint, not an unexamined
  journal PDF.
- Greene--Wellner published PDF:
  https://sites.stat.washington.edu/jaw/JAW-papers/jaw-greene.bern.2017.pdf ;
  DOI https://doi.org/10.3150/15-BEJ800 ; local `GreeneWellner2017.pdf`,
  `.txt`, and a rendered page 1915. SHA256
  `c2bce5b36ce32910716fafe3158d0054ea205741a44085ba81dcbabc96a1c763`.
- Bardenet--Maillard: https://arxiv.org/pdf/1309.4029v2 ;
  https://doi.org/10.3150/14-BEJ605 ; local `BardenetMaillard2015.pdf`
  and `.txt`. SHA256
  `e9e6cda02b46aaa708c1775453640b874ecfcb4cd0ecff132a15f87a37cb6cec`.
- Chvatal bibliographic primary record:
  https://doi.org/10.1016/0012-365X(79)90084-0 ; local
  `Chvatal1979_crossref.json`. Verified title, author, *Discrete
  Mathematics* 25(3) (1979), 285--287. Formula above is independently
  rederived and corroborated by MZC, not falsely attributed to an
  uninspected page of the original Chvatal PDF.
- Lee--Kim: https://arxiv.org/abs/2608.04900v2 ; current abstract metadata
  and the paper explicitly identify v2, 29 September 2026. Local
  `LeeKim_latest_abs.html`; inspected PDF and text at
  the previously archived Lee--Kim v2 source and its extracted text.
- Lee--Kim additional metadata hit:
  https://doi.org/10.1214/26-ECP818 ; local
  `LeeKim_ECP_crossref.json` lists the same title and authors in
  *Electronic Communications in Probability* 31 (2026), 1--12. Its
  generic `2026-01-01` metadata date precedes the arXiv dates; the
  publisher response is a browser challenge. Do not use this date to
  infer priority or treat the record as a verified second paper.

Bounded Lee--Kim searches retained locally: official arXiv author search
for `Seongchan Lee` and `Ilmun Kim`, an official arXiv all-fields search
for `exact Hoeffding`, and a Crossref title/author query. The author
searches show only arXiv:2608.04900 among Hoeffding/exchangeability titles.
Files: `Lee_arxiv_search.html`, `Kim_arxiv_search.html`,
`exact_Hoeffding_arxiv_search.html`, `LeeKim_crossref_search.json`.
The result is "no second exact-constant paper located in these searches",
not "no such paper exists".
