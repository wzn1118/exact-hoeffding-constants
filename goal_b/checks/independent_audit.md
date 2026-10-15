# Goal B: independent proof audit

Date: 16 October 2026. Proof input branch: formal/full-closure-20261015 at 8687c3d.

## Reviewed claims

1. The variance proxy S(N,k,m) is the unnormalized supremum 2 centered logMGF/t^2. Companion normalizedHypergeomProxy equals 4N/[m(N-m)] times S. This prevents accidental transposition of the normalized coefficient.
2. The success and sample complement symmetries each preserve the centered variance proxy, permitting kbar=min(k,N-k), mbar=min(m,N-m).
3. For reduced mbar<=kbar<N/2, scaled Bernoulli proxy bound S<=M beta(kbar/N) applies, including singleton equality.
4. Artanh(d)>=d+d^3/3 follows by the derivative d^4/(1-d^2)>0, and offcenter d>=2/N (even) or 3/N (odd).
5. For kbar<mbar, the curvature ceiling S<=kbar(N-kbar)/[4(N-1)] applies. Identity (mbar-kbar)(N-mbar-kbar)>=1 for even N and >=2 for odd N.
6. Exact rational algebra proves the announced Delta(N,m) in both parameter branches.
7. Central S>=W follows from the zero-tilt variance limit; for odd N, S>W follows from the positive third cumulant after reducing m<=floor(N/2).
8. N=2,3 have no offcenter k. For N=3,m=2, the m=N-1 singleton-complement formula must be used instead of the general two-draw expression.

## Independent computational audit

The verifier has separate Fraction (exact rational) and actual centered finite-MGF numerical paths. The frozen local baseline passed 67,570 rational offcenter comparisons for N<=60, 1,560 optimized proxy checks for N<=18, and 18 small-sample checks. Numerically optimized values are approximate; the all-N theorem is proved analytically.

## Scope and provenance

The proof invokes the previously established sharp all-tilt curvature bound and scaled Bernoulli envelope. Their proofs are in the companion Lean project. This new finite-N assembly has no confirmed Lean kernel certificate yet. No claim is made of uniqueness of the maximizing tilt for odd m>=3, an elementary general odd-m closed value, a sharp Delta, external peer-review acceptance, or universal novelty. No unpublished Lee-Kim manuscript was analyzed.
