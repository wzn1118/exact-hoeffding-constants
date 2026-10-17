# Independent read-only A2 audit, 2026-10-17

Audited root working-tree sources at HEAD 8b75977b138205c4ba402000b25d226d55994682, including uncommitted A2 additions. No root source or frozen paper was changed; no extra compilation was run.

## Corrected mathematical scope: proved

1. Arbitrary finite nonnegative integer-valued law, every natural threshold d (hence all d>=1): actual finite tail <= optimized binomial-basis factorial minimum F; F <= each nonnegative-tilt exponential candidate; and F <= the infimum of those candidates. Sources: finiteIntegerTailMass_le_factorialBound, finiteFactorialBound_le_chernoff_tilt, finiteFactorialBound_le_chernoff_inf.
2. Legal hypergeometric margins, every threshold d, degree j<=min(d,N): hypergeom_factorial_candidate_formula_of_degree_le_population gives the ordinary nonzero-denominator falling-factorial ratio. For N<j, hypergeom_factorial_candidate_eq_zero_of_population_lt_degree gives the separate zero value. Degenerate laws and j=0/N are not excluded.
3. Canonical A domain, supported strict upper thresholds mu<d<=m: actual tail <= F <= exp(-actual hypergeometric Legendre I(d)) < exp(-piecewise J(d)). d=m included.
4. Canonical A domain, supported strict lower thresholds 0<=d<mu: actual lower-tail finite sum <= reflected factorial minimum at m-d <= exp(-actual I(d)) < exp(-J(d)). d=0 included. Reflection keeps original hypergeomMass and uses map i -> m-i. No complemented-success canonical assumption is used.
5. Strict upper supported minimizer domain km<Nd, 0<d<=min(k,m), k+m<=N: explicit ceiling index admissible and globally minimizes every candidate. Integral cutoff j with j+1<=d: new succ_eq_of_integral_cutoff and Bound_eq_adjacent_candidates establish both adjacent candidates are equal global minima. At d=min(k,m)>0: index_eq_endpoint proves j*=d. No claim of nonzero j* at mean is made; the paper only states this formula above the mean.

## Exact scope qualifications

A. Ordinary falling-factorial display at j>N is undefined 0/0, not a false factorial-Chernoff comparison. The new two-branch Lean API formalizes the mathematically correct split; it does not silently impose Lean total division on the frozen paper. A-domain example N=7,k=m=3,d=j=8.
B. The paper's in-particular sentence says d>mu but does not repeat d<=m. Since its J is defined only on [0,m], the strict chain must be read on the supported domain. This is a second explicit scope qualification, independent of j>N: N=7,k=m=3,d=4 has d<=N and well-defined factorial candidates, but J(4) is outside its declared domain. Outside support, actual tail=F=nonnegative-tilt Chernoff infimum=0; the extended-real I is +infinity. An all-threshold strict chain with finite-real I,J is not the stated meaningful claim. Existing generic comparison remains valid there. The private addition FactorialSupportExterior.lean now supplies dedicated outside-support tail=0, F=0, candidate nonnegativity, arbitrarily-small-candidate, and infimum=0 interfaces. It introduces no real-valued outside-support I or J.
C. At d=mu, general finite-law comparison still applies, but strict exp(-I)<exp(-J) is excluded correctly. The index theorem's strict-mean hypotheses match the paper.

## Verdict

The mathematically correct, explicitly scoped A2 result is closed by the current source theorem family, including upper/lower supported endpoints and integral minimizer ties. The unmodified literal paper statement is not unconditionally closed because of the ordinary-fraction j>N domain omission and the non-repeated support restriction in the strict-chain sentence. Neither is a counterexample to the general factorial-Chernoff inequality. Keep manuscript frozen, record these domain qualifications transparently, and do not use an unchecked real sSup outside its bounded support domain as an extended-real rate.

Concordance recommendation: include hypergeom_factorial_candidate_eq_zero_of_population_lt_degree alongside formula_of_degree_le_population. The generic theorem covers thresholds outside support; do not state that FactorialMinimizer or strict I/J comparison does.


## Support-exterior implementation follow-up

Implemented in the isolated A2 worktree, using the original hypergeometric finite weights. All legal margins including N=0, zero/full marks, zero/full draws are allowed. The explicit estimate is candidate(t) <= exp(-t * (d-min(k,m))) for t>=0, and the positive gap yields arbitrarily small candidates. The nonempty, bounded-below candidate set then has real infimum zero. This supplies the correct missing boundary interface independently of the strict supported I/J chain. The frozen paper has not been changed.
