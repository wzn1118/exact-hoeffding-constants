# Algebraic certification of the global curvature and Bernoulli Laplace envelopes

**Zinan Wang · 11 October 2026**

## 1. Global curvature inequality

Let `H~Hyp(N,k,m)` and `v(t)=Var_t(H)`. Complementation and margin transposition reduce the parameter range to

`k=j, m=j+h, N=2j+h+r`, where `j≥1` and `h,r≥0`. Put `T=N-1`, `L=N-j-1`, `D=h-r`, and `B=j(L+1)/(4T)`.

The real-rooted Jacobi representation of the hypergeometric probability generating polynomial yields a sum of `j` Bernoulli variables after exponential tilting. Consequently the tilted mean `u` satisfies `0<u<j`, and the tilted variance satisfies `0<v≤u(j-u)/j`.

The polynomial hypergeometric differential equation is

`z(1-z)Q''+[r+1+(j+m-1)z]Q'-jmQ=0`.

At a stationary point of `v`, eliminate the tilt `z` from the differential equation and its derivative, obtaining the quadratic stationary equation `F(u,v)=0`. Its coefficient of `v²` is `-(N-1)` and its constant term is `u(j-u)(r+u)(m-u)>0`; thus the positive stationary branch is unique.

Set `x=2u-j`, `A=j²(j-1)-Tx²` and `E=L(L+1)-2j`. Independent polynomial expansion gives

`-16T F((j+x)/2,B) = A(D-x)²+(L+1)(2jDx+Ex²)`.

A putative maximizer with `v>B` has `A>0`. For `j≥3`, `L≥j-1` and `|D|≤L-j+1`, the right side is nonnegative. The proof separates the cases `A≥j²/L` (completion of squares) and `0<A<j²/L` (endpoint monotonicity in `|D|`), where the final comparison follows from the exact nonnegative-coefficient polynomial

```
K = a²(a+1)(a+3)³
  + a(a+3)²(5a²+16a+10)s
  + (10a⁴+80a³+213a²+202a+35)s²
  + (10a³+64a²+117a+52)s³
  + (5a²+22a+19)s⁴ + (a+2)s⁵,
```

with `a=j-3≥0` and `s=h+r≥0`. It follows that `F(u,B)≤0`. The unique positive root of `F(u,v)` lies at or below `B`, contradicting the assumed maximizer. Cases `j=1` and `j=2` follow respectively from Bernoulli variance and an explicit symmetric three-mass variance formula. Therefore

`Var_t(H) ≤ min{k(N-k),m(N-m)}/[4(N-1)]` for every real `t`.

## 2. Parity-uniform Laplace envelope

Assume `N≥7`, `3≤m≤k≤⌊N/2⌋`, and `N>2m`. Write `p=k/N`, `d=1-2p`, `M=m(N-m)/(N-1)`, `a=(N-2m)/(N-2)`, and `μ=mp`.

The tilted mean–variance curve `V(u)` obeys

`F(u,V)+N(u-μ)V V'=0`, where

`F(u,v)=-(N-1)v²+[A+C-A'C+C'A]v+AC`,  `A=u(u+N-k-m)`,  `C=(k-u)(m-u)`.

The candidate quadratic barrier is

`P(u)=Mp(1-p)+ad(u-μ)-(a²/M)(u-μ)²`.

With `z=2(u-μ)/M`, its residual is

`F(u,P)+N(u-μ)P P'=-G(u-μ)²W(d,z)`, where `G=N²(m-1)(N-m-1)/[4(N-2)²(N-1)]>0`.

The Poisson–binomial bound `V≤u(m-u)/m` implies `E(d,z)≥0` at any contact `V=P`. The exact certificate

`W=λ E+α(δ²-d²)+A₀d²+2B₀dz+C₀z²`,  `δ=(N-2m)/N`,

has `λ>0`, `α>0`, `A₀>0`, `A₀C₀-B₀²>0` for all admissible integers. Each positivity statement reduces to a polynomial with nonnegative coefficients in `j=m-3≥0` and `r=N-2m≥1`. Thus `W>0` at each feasible contact. The endpoint values satisfy `P(0)>0` and `P(m)>0`; the contact derivative is

`(V-P)' = G(u-μ)W/[NP]`.

Its sign is negative to the left of `μ` and positive to the right. Since `V-P` vanishes at `μ` and is negative at both support endpoints, every other interior contact is excluded. Hence `V(u)<P(u)` for `u≠μ`.

Set `y(t)=E_t H-μ`. Since `y'=V(μ+y)≤Mp(1-p)+ady-(a²/M)y²`, comparison with the explicit Riccati solution

`Y(t)=(M/a)[pe^{at}/(1-p+pe^{at})-p]`

gives `y(t)<Y(t)` for positive `t` and `y(t)>Y(t)` for negative `t`. Integration in the correct orientation establishes

`log E exp[t(H-μ)] < M/a²[log(1-p+pe^{at})-pat]` for every nonzero real `t`.

The exact Bernoulli proxy formula and the `m=1,2` cases complete the parity-dependent optimization in the principal article.

## 3. Reproducible certificate

`python3 checks/verify_independent_certificates.py`

The script independently reconstructs the stationary resultant, all polynomial certificates, the sign factorizations and the generating-polynomial ODE. It also evaluates finite-sum exponential moments for an additional independent cross-check. The sign and ODE arguments in Sections 1–2 complete the analytic passage from those identities to the uniform inequalities.
