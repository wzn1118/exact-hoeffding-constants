# Semantic contract marker review — 18 October 2026

The strict gate `checks/check_semantic_contract_integrity.py --require-contracts` previously reported 35 mapped contracts without a reviewed type-marker profile. Each of those profiles was checked against the frozen manuscript environment, the complete `type_pretty` record in `submission/current/theorem_lean_manifest.json`, and the aggregate contract source. The profiles now cover all 49 mapped contracts.

The marker profiles check proposition-level symbols that survive Lean pretty-printing: actual hypergeometric laws, envelope and proxy functions, stationary polynomials, finite-support Legendre objects, asymptotic remainder constructors, equality/strictness interfaces, and the named semantic aggregate statements. Proof-only helpers remain in the separate transitive kernel dependency audit. The profiles are structural evidence for the reviewed encodings; they do not by themselves establish TeX-to-Lean semantic equivalence.

The 35 newly closed profiles are:

- Main/stationary: `manuscript_main_laplace_full_contract`, `manuscript_prop_two_level_contract`, `manuscript_lem_PB_contract`, `manuscript_lem_branch_contract`, `manuscript_extra_stationary_q0_radicals_contract`, `manuscript_lem_universal_contract`, `manuscript_lem_identity_contract`, `manuscript_prop_allinner_contract`, `manuscript_prop_variance_parity_full_contract`, `manuscript_prop_explicit_extremizer_contract`, `manuscript_lem_threemass_contract`.
- Odd/two-draw: `manuscript_prop_odd2_semantic_contract`, `manuscript_cor_two_bern_envelope_contract`, `manuscript_odd_envelope_full_contract`, `manuscript_extra_Bernoulli_gap_display_identities_contract`, `manuscript_odd_lem_PB_full_contract`, `manuscript_odd_lem_ode_mean_contract`, `manuscript_odd_lem_barrier_mean_contract`, `manuscript_odd_global_extremizer_contract`, `manuscript_extra_B2_odd_central_full_contract`.
- Goal B: `manuscript_B_inputs_contract`, `manuscript_B_main_contract`, `manuscript_B_atanh_contract`, `manuscript_B_individual_contract`, `manuscript_extra_B1_individual_margin_contract`, `manuscript_B_even_contract`, `manuscript_B_odd_contract`, `manuscript_B_small_contract`.
- A/appendix: `manuscript_extra_A_Legendre_derivatives_full_contract`, `manuscript_extra_A_quadratic_chain_contract`, `manuscript_extra_A_scaled_rate_Taylor_contract`, `manuscript_thm_odd_expansion_contract`, `manuscript_cor_fixedm_gap_full_contract`, `manuscript_extra_appendix_cumulant23_remainders_contract`, `manuscript_extra_appendix_proxy_uniform_Taylor_contract`.

Verification after registration:

```text
python3 checks/check_semantic_contract_integrity.py --self-test
PASS
python3 checks/check_semantic_contract_integrity.py --require-contracts
PASS: 49/49 typed contracts; 49/49 marker-checked contracts; 240 display blocks
```
