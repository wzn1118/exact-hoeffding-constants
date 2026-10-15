# Compact success-proportion contraction

`ExactHoeffding/CompactAnalyticContraction.lean` proves the actual statement of
Theorem `thm:compact_contraction` in `source/analytic_contraction.tex`.

For every fixed `m ≥ 2` and `0 < η < 1/2`, it gives the explicit population
threshold

```
max 2 (⌈(m : ℝ) / η⌉₊ + 1).
```

For every population at or above the threshold, and every success count with
`η ≤ k/N ≤ 1-η`, the actual optimal proxy satisfies

```
hypergeomOptimalProxy N k m ≤
  m * (N-m) / (N-1) * optimalProxy (bernoulliCenteredLogMGF (k/N)).
```

The equality set is exactly `2*k=N`; every nonbalanced success margin gives a
strict comparison.  The module proves the normalized form as well, with the
same complete equality set.

The proof uses the stronger finite-parameter Laplace envelope and the exact
Bernoulli optimal-proxy theorem.  It does not assume joint analyticity or any
optimizer localization.  The first-order inverse-population correction and
its two-variable analytic factorization in the displayed proof are separate
assertions; their scalar strict coefficient is proved in
`AnalyticContractionCoefficient.lean`.

The targeted compile of `CompactAnalyticContraction.lean` exited with code `0`
and no warnings.  Evidence:
`/data/hoeffding_full_20261015/evidence/compact_analytic_contraction3.log`.
