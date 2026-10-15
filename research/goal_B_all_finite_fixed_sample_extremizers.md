# Goal B — finite-N fixed-sample hypergeometric extremizers

**Research result, 16 October 2026.** This note derives an all-parameter maximizing-success-count theorem from analytic inequalities already present in the formal/full-closure-20261015 Lean branch. The NEW assembly and gap inequalities below have NOT yet been compiled in Lean. The odd-population value for arbitrary m is characterized by an exact one-variable optimization, not a general elementary closed form.

## Theorem

For N >= 2 and 1 <= k,m < N, let H(N,k,m) be hypergeometric and define its optimal sub-Gaussian variance proxy

s²(N,k,m) = sup_{t != 0} (2/t²) log E exp[t(H(N,k,m) - km/N)].

Put c=floor(N/2), M=m(N-m)/(N-1), W=M*c*(N-c)/N², the ordinary variance of the central hypergeometric law.

**Claim B (all N,m, quantitative form).** For every 1 <= m < N,
- s²(N,c,m) = s²(N,N-c,m) >= W;
- every other 1 <= k < N satisfies s²(N,k,m) <= W - Delta(N,m) < W, where
  - for even N, Delta(N,m) = M/(3N²+4);
  - for odd N, Delta(N,m) = M*(2N²-3)/(4N²*(N²+3)).
- Therefore the exact set of maximizing success counts is {floor(N/2), ceil(N/2)}.
- For even N, max_k s²(N,k,m) = M/4.
- For odd N, max_k s²(N,k,m) is the actual central-margin optimal proxy, strictly above W. The explicit elementary formula for arbitrary m remains a separate question.

For N = 2 or 3 there is no off-center k, so the strict-gap assertion is vacuous.

## Proof

Hypergeometric success and sample complementation preserve the optimal proxy (they reflect the centered law). Reduce to 1 <= k,m <= floor(N/2), with k<floor(N/2) for the off-center argument.

The existing project proves two ingredients:

(C) The all-tilt hypergeometric curvature bound implies

s²(N,k,m) <= min{k(N-k),m(N-m)}/(4(N-1)).

(B) Whenever m <= k < N/2, the scaled Bernoulli comparison implies

s²(N,k,m) <= M * beta(k/N),
beta(p) = (1-2p)/(2 log((1-p)/p))
        = d/(4 artanh(d)), d=1-2p.

For m=1, (B) is an exact identity. For m>=2 it follows from the strict inner comparison already proved in OddHypergeomExtremizers.lean and the two-draw case included there.

For 0<d<1 the derivative of artanh(d)-d-d³/3 equals d⁴/(1-d²)>=0; hence

artanh(d)>=d+d³/3 and beta(p)<=1/[4(1+d²/3)].

**First case: m <= k.** If N is even, noncentral k <= N/2-1 gives d >= 2/N. Thus

s² <= M * 3N²/[4(3N²+4)] = W-M/(3N²+4).

If N is odd, noncentral k <= (N-3)/2 gives d >= 3/N. Consequently

s² <= M * N²/[4(N²+3)]
   = W-M*(2N²-3)/[4N²(N²+3)].

**Second case: k < m.** Identity
m(N-m)-k(N-k) = (m-k)(N-m-k)
is at least 1 if N is even, at least 2 if N is odd. Apply (C).

Even N: W-s² >= 1/[4(N-1)] > M/(3N²+4).
Odd N:
W-s² >= [2-m(N-m)/N²]/[4(N-1)]
     >= 7/[16(N-1)] > M*(2N²-3)/[4N²(N²+3)].
The last comparisons use m(N-m)<=N²/4 and N>=2.

At the central k=c, the small-tilt expansion of the log-MGF yields s² >= Var(H)=W. Success complementation makes k=c and k=N-c identical as optimal proxies. The strict off-center gap proves the argmax classification.

For even N, (C) at k=N/2 gives s² <= M/4=W, hence equality. For odd N, after sample complementation assume m<=c. The hypergeometric third cumulant at k=c is

kappa_3 = W*(N-2c)*(N-2m)/[N(N-2)] > 0.

Thus 2 log E exp[t(H-EH)]/t² = W+(kappa_3/3)t+O(t²) exceeds W for small positive t. This proves strictness at the odd central margins and completes the argument.

## Value of the odd optimum

For N=2n+1 and c=n, the exact value is the maximum over real t of the continuous-at-zero expression

F(t) = (2/t²) log [
  sum_{j=max(0,m-n-1)}^{min(m,n)}
  C(n,j) C(n+1,m-j)/C(2n+1,m) * exp(t*(j-m*n/N))
].

F(0)=W; F(t)->0 as |t|->infinity, so a global maximizer exists. Every nonzero maximizer t solves t L'(t)=2L(t), where L(t)=log E exp[t(H-EH)]. Uniqueness of the optimizing tilt is NOT asserted.

For odd N, m=1 or N-1, the closed value is 1/[2N log((N+1)/(N-1))].
For odd N>=5, m=2 or N-2, the three-mass formula gives 2/[N log((N+1)/(N-3))].

## Formalization and validation

Upstream inputs in formal/full-closure-20261015:
- SharpCurvatureTheorem.hypergeomTiltVariance_sharp and the curvature-to-MGF inequality;
- OddHypergeomExtremizers.normalizedHypergeomProxy_inner_lt_bernoulli;
- OddHypergeomExtremizers.normalizedHypergeomProxy_singleton_subhalf;
- complement symmetries, NormalizedProxy and the ordinary variance identity;
- EvenHypergeomExtremizers.even_normalized_proxy_all_equality.

NEW Lean proof obligations: artanh cubic lower bound, scalar beta gap, the k<m curvature-to-central comparison, a uniform all-N theorem for the exact normalized or unnormalized proxy (track scaling carefully), and the quantitative separation. Run lake build ExactHoeffding and the transitive axiom audit before calling the new theorem kernel-certified. For odd m>=3, an elementary closed formula for the central value has NOT been established by this proof.

**Provenance.** Original analytic deduction from the repo's previously established inequalities. This note is not independently peer-reviewed and does not claim publication priority. It should remain on its research branch pending independent mathematical and Lean checks.
