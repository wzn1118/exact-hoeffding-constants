# Even normalized-proxy extremizers

For every `q > 0` and `0 < k,m < 2*q`, the complete equality condition is

`normalizedHypergeomProxy (2*q) k m = (2*q)/(2*q-1) ↔ k = q`.

The condition is not `k=q or m=q`. The normalization is
`4*N/(m*(N-m))` times the unnormalized optimal variance proxy, so transposition
changes the normalized value by `k*(N-k)/(m*(N-m))`. In particular, the actual
law with `N=4,k=1,m=2` is Bernoulli with parameter one half; its unnormalized
proxy is `1/4` and its normalized proxy is `1`, strictly less than `4/3`.
`normalizedHypergeomProxy_four_one_two` records this exact example.

The proof uses the already established strict Bernoulli envelope in the
canonical triangle, treating the singleton separately by its exact formula.
Transposition gives strictness in the rest of the half-margin square.
Success and sample complementation then recover all original margins.
The assumptions include the singleton case and `N=2`; no size exclusion or
unproved equalities are added.

Public theorems: `even_normalized_proxy_all_equality` and
`even_normalized_proxy_global_optimality`.

Compilation evidence:
`/data/hoeffding_full_20261015/evidence/even_hypergeom_extremizers1.log`.
The serialized check started at `2026-10-15T13:35:01+00:00` and returned
`lean_exit_code=0` with no warnings. It used the shared `flock` lock and
lock-internal `timeout 600 lean -j 1`. No independent axiom audit was queued;
the root integration performs that audit together with the other modules.
