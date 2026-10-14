# TASK_STATUS_B

## Scope

- Branch: `research/B-jacobi-20261014`
- Required baseline: `origin/main@ebf534362f596175a24fc33e9eebc1cd4145349f`
- Current baseline commit: `ebf534362f596175a24fc33e9eebc1cd4145349f`
- Write owner: current B session only; the duplicate B session was instructed
  to stop and is not writing this worktree.
- Date: 2026-10-14 (UTC)
- No `main`, old formal branches, or other worktrees are being edited.

## Environment audit

- Declared project toolchain: `leanprover/lean4:v4.33.0`.
- Lean 4.33.0 is installed at `/data/.toolchains/lean-4.33.0-linux`; verified
  version is `4.33.0`, commit `d8b18978322de05a8f3dba51ef03cf5461676c17`.
- All proof commands below used
  `PATH=/data/.toolchains/lean-4.33.0-linux/bin:$PATH`; `lean-toolchain`
  remains unchanged at v4.33.0.
- mathlib source is present at `.lake/packages/mathlib` and is pinned to
  `v4.33.0`, commit `db584cd6d46c92f209a44c0f1c829460d327499d`.
- `lake exe cache get` completed successfully. It downloaded no missing
  artifacts, decompressed 8,312 cached v4.33.0 files, and confirmed 378 more
  were already decompressed in this B worktree's `.lake`; no shared
  worktree/cache was written.

## Command evidence

- Toolchain: `lake env lean --version`, exit code `0`, log
  `checks/logs/B/lean_version_4.33.log`.
- `lake update` was attempted with the required v4.33.0 path but hit the bounded
  20-second network timeout while refreshing upstream refs (exit code `124`);
  log `checks/logs/B/lake_update_4.33.log`. The local mathlib source and
  dependency manifest are pinned to v4.33.0.
- `lake exe cache get`, exit code `0`, log
  `checks/logs/B/lake_cache_get_4.33_full.log`.
- `lake build ExactHoeffding.PoissonBinomial`, exit code `0`, log
  `checks/logs/B/lake_build_PoissonBinomial_4.33.log`.
- `lake env lean ExactHoeffding/PoissonBinomial.lean`, exit code `0`, log
  `checks/logs/B/lean_PoissonBinomial_4.33.log`.
- `#print axioms` for all three declarations, exit code `0`, log
  `checks/logs/B/print_axioms_PoissonBinomial_4.33.log`; each lists only
  `[propext, Classical.choice, Quot.sound]`.
- The full `lake build ExactHoeffding` was started and stopped after the
  umbrella `Mathlib` imports exceeded the bounded work window. The main/control
  integration run will perform the complete suite after cherry-pick. No full
  library success is claimed by this B commit; the interrupted command record
  is `checks/logs/B/lake_build_ExactHoeffding_4.33.log` (exit code `130`).

## Mathematical audit

The existing interfaces were read in full for `Hypergeometric`, `Normalization`,
`FactorialMoments`, `OrdinaryMoments`, `MomentGenerating`, `TiltedVariance`, and
`CurvatureBridge`. They already prove finite normalization, factorial moments,
finite-MGF derivatives, exact tilted variance identities, nonnegative curvature,
and a conditional curvature-to-Laplace implication. They do not prove Jacobi
real-rootedness, the hypergeometric-to-Poisson-binomial factorization, or the
sharp all-tilt curvature upper bound.

The deliverable is therefore restricted to a kernel-checkable finite
Bernoulli-list mean-variance inequality. It proves the algebraic estimate for
arbitrary real parameter lists and provides a `[0,1]`-parameter Poisson-binomial
interface. It does not prove independence as a probability-space statement,
Jacobi factorization, or admissibility of the hypergeometric tilt. Those remain
explicit gaps and are not stated as unconditional theorems.

## Current work

- [x] Verify branch and baseline.
- [x] Audit the proof-status ledger and requested Lean modules.
- [x] Confirm the exact v4.33.0 toolchain and fetch its mathlib cache.
- [x] Add and kernel-check the finite Bernoulli-list mean-variance inequality.
- [x] Run `#print axioms` for all three declarations.
- [x] Update theorem map and gap register with exact scope and evidence.
- [ ] Run the full umbrella build and `lake env lean ExactHoeffding.lean` after
  integration; this is delegated to the main/control worktree.

## Minimal blocker

There is no blocker for the scoped theorem: the v4.33.0 targeted build and
kernel check passed. Upstream `lake update` remains network-limited, and the
complete umbrella build is intentionally left for the control worktree's
integration run. The Jacobi-to-Poisson-binomial representation is still an
open mathematical formalization gap.
