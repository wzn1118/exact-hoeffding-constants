# A1 KL/Chernoff Audit

Source reviewed: `docs/A1_KL_Chernoff_2026-10-15.md`.

## Verdict

The stationary-point calculation and the substitution into the binary KL
divergence are correct in the stated paper domain

```text
N >= 7, 3 <= m <= k <= floor(N/2), N > 2m.
```

In particular, `p=k/N`, `M=m(N-m)/(N-1)`, `a=(N-2m)/(N-2)`, and

```text
U(t) = M/a^2 * (log(1-p+p*exp(a*t)) - p*a*t)
```

give, conditionally on the paper's Laplace envelope `psi <= U`,

```text
P(H-mp >= x) <= exp(-(M/a^2)*D(theta_+ || p)),
theta_+ = p + a*x/M,
```

and

```text
P(H-mp <= -x) <= exp(-(M/a^2)*D(theta_- || p)),
theta_- = p - a*x/M.
```

These are conditional consequences of `U`; they are not yet Lean theorems
because the global envelope itself remains unresolved in the Lean ledger.

## Required corrections

1. The derivation is parity-uniform, not odd-only. The assumptions `N>2m`
   and `a>0` allow both odd and even `N`; the even balanced case `N=2m`
   is outside this formula.
2. A noninteger real threshold is valid analytically, but an exact tail
   implementation must use
   `r_plus = ceil(mp+x)` and `r_minus = floor(mp-x)` before summing integer
   masses. The executable matrix records both the real `x` and the integer
   event threshold.
3. The support guard must run before constructing a KL parameter. If
   `r_plus > min(k,m)` or `r_minus < max(0,m+k-N)`, the corresponding event is
   empty and its exact probability is zero. No out-of-range `theta` is sent
   to `D`.
4. The endpoint formulas `theta_+=1` and `theta_-=0` are continuous KL
   limits, not evaluations containing `log(0)`. In the strict paper domain,
   the coarse support bounds actually give

   ```text
   a*m*(1-p)/M < 1-p,
   a*m*p/M     < p,
   ```

   so a nonempty supported event does not reach those endpoints. They are
   still retained as abstract boundary cases.
5. If `a=0`, the expression `M/a^2` is undefined. The only relevant balanced
   limit in the paper symmetry range is `p=1/2`, and

   ```text
   U(t) -> M*t^2/8,
   Chernoff upper/lower bound -> exp(-2*x^2/M).
   ```

   This is recorded as `quadratic_limit` in the matrix, not as a KL row.
6. The local comparison with `exp(-2*x^2/M)` is conditional on the sharp
   curvature upper theorem. It is a valid Taylor comparison of the two
   envelopes, but it does not formalize that theorem.

## Reproducible artifacts

* `checks/check_exact_hypergeom_tail_kl.py`: exact integer/Fraction tail and
  binomial KL sweep, including the proved all-success/all-failure endpoint
  strictness family.
* `checks/check_problem_a_matrix.py`: high-precision A1/A2/A5 matrix with
  noninteger thresholds, support guards, scaled-Bernoulli KL rows, the
  `a=0` quadratic limit, symmetry-transposed dual KL rows, the conditional
  global `V_global=C_N^*m(N-m)/(4N)` row, the fixed-parameter proxy diagnostic,
  and standard Hoeffding/Serfling reference rows.
* `checks/results/problem_a_tail_matrix.csv`: generated matrix artifact.

The matrix's numerical inequalities are diagnostic evidence. The binomial KL
and endpoint checks are classical Hoeffding/Chvatal benchmarks, not an
original result. The fixed-parameter proxy is not a certified upper bound.
The only analytic fact newly recorded here is a parameter-domain/support audit;
no universal strict tail theorem is inferred from the matrix.
