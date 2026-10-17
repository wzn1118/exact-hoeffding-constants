# A2 factorial ratio denominator audit

Frozen manuscript: `submission/current/manuscript.tex`, Proposition `A:factorial`.

The general finite-law comparison allows every integer threshold `d >= 1`.
The following displayed hypergeometric falling-factorial ratio is only an
ordinary real fraction for `j <= N` (as well as the already stated `j <= d`).
When `j > N`, both numerator factors and `(N)_{underlined j}` vanish, so the
right-hand side is `0/0`; the left-hand side is the well-defined number zero.

The smallest positive-population example is `N = k = m = 1`, `d = j = 2`.
Here `H = 1` almost surely, so `E[choose(H,2)] / choose(2,2) = 0`, whereas the
displayed falling-factorial quotient is `(0 * 0) / (0 * 2) = 0/0`.
If `N = 0` is allowed, `N = k = m = 0`, `d = j = 1` is smaller still.
Within the paper's canonical A parameter domain, the smallest population
example is `N = 7`, `k = m = 3`, `d = j = 8`.

This is an omitted definition-domain condition, not a counterexample to the
factorial-versus-Chernoff comparison. Under Lean's total real division the
quotient `0/0` is defined as zero, but that convention is not specified in
the frozen mathematical statement. The source theorem
`hypergeom_factorial_candidate_formula` is correctly restricted to `d <= m`
and `j <= d`, and therefore has nonzero denominator. No paper source was
changed during this audit. A mathematically complete ordinary-fraction
statement can restrict the formula to `j <= min(d,N)`, supply the separate
zero case `N < j <= d`, or restrict the hypergeometric formula to supported
thresholds `d <= min(k,m)`.


## Supported thresholds in the strict rate chain

The in-particular sentence of `A:factorial` says `d > mu` without repeating
`d <= m`, whereas its piecewise rate `J` has declared domain `[0,m]`.
The example `N=7, k=m=3, d=4` is outside that domain even though all factorial
candidate denominators for `j <= d` are nonzero. The strict finite-rate chain
is proved for `mu < d <= m`; the reflected chain is proved for `0 <= d < mu`.
The generic factorial–Chernoff comparison holds for every natural threshold.
Beyond the upper support, the actual tail, optimized factorial bound and
nonnegative-tilt Chernoff infimum are zero; the correct extended-real rate is
infinite. The real-valued Legendre `sSup` is not used outside its bounded
support domain as an extended-real substitute.

The frozen paper has not been changed. Its unconditional completion claim
remains open pending resolution of these two stated definition-domain issues.
