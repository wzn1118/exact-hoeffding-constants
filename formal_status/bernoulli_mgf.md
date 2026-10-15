# All-parameter tilted Bernoulli MGF factorization

`HypergeomBernoulliMGF.lean` proves
`hypergeom_tilted_shifted_bernoulli_mgf` for every `k ≤ N`, `m ≤ N`, every
real exponential tilt, including `N=0,1` and deterministic laws.

The lower-support shift is `L = k+m-N` using natural subtraction. The number
of strictly interior Bernoulli factors is
`j = min(min(k,N-k),min(m,N-m)) = min(k,m)-L`.
The theorem states the actual MGF identity

```
M(t+u) / M(t) = exp(L*u) * ∏ i, (1-p_i+p_i*exp(u)),  0 < p_i < 1.
```

It is obtained from the actual canonical Jacobi PGF, followed by
transposition and both complement identities. Reflection replaces each
Bernoulli parameter by its complement and tracks the deterministic shift.
No assertion about an auxiliary polynomial is used as a substitute for the
actual finite law. The empty product handles zero support width.

The first successful kernel check is
`/data/hoeffding_full_20261015/evidence/hypergeom_bernoulli_mgf3.log`, with
`lean_exit_code=0`, using Lean 4.33.0, the shared compilation lock and
`timeout 600 lean -j 1`. A product probability-space realization is a
separate interface under development in `BernoulliProductLaw.lean`.
