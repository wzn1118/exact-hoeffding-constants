# Bernoulli geometry and Jacobi root dispersion

`ExactHoeffding/BernoulliMGFGeometry.lean` proves the generic shifted
Bernoulli factorization calculus. For an everywhere positive finite MGF,
the logarithmic first derivative is the deterministic shift plus the sum of
the actual Bernoulli parameters, and the second logarithmic derivative is
the sum of their Bernoulli variances. Applying this to the already proved
actual hypergeometric shifted factorization gives
`hypergeom_tilted_bernoulli_mean_variance` and the true-support
mean-variance inequality `hypergeom_tilted_true_support_mean_variance_bound`.
The latter uses the support width
`min (min k (N-k)) (min m (N-m))`, so it remains an actual-law statement
rather than a canonical-margin assumption.

`ExactHoeffding/JacobiRootDispersion.lean` then enumerates the negative roots
of the canonical hypergeometric Jacobi PGF. It proves the exact identity
between the actual tilted hypergeometric variance and
`sum p_i(1-p_i)` for `p_i = z/(z-root_i)`, rewrites the transformed-root
square sum as `j - 4 Var_t(H)`, and combines the already kernel-checked
all-parameter sharp curvature theorem to obtain

`j (j-1) / (N-1) <= sum_i ((z+root_i)/(z-root_i))^2`,

with `N = 2*j+h+r` and `z > 0`. Roots are counted with their polynomial
multiplicities. The degree-zero case is handled explicitly.

Compilation evidence:
`/data/hoeffding_full_20261015/evidence/bernoulli_mgf_geometry6.log` and
`/data/hoeffding_full_20261015/evidence/jacobi_root_dispersion3.log`.
The two serialized checks used the shared flock lock and `timeout 600 lean
-j 1`; both returned `lean_exit_code=0`. Only two unnecessary-sequence-focus
linter warnings were emitted. No independent `#print` audit was run; root
integration performs the common audit.
