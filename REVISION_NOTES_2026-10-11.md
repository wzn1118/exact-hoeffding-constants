# Editorial and reproducibility revision — 11 October 2026

The primary paper has been shortened from 33 to **28 pages**. The reduction to hypergeometric laws, global tilted-variance proof, sharp parity-dependent constant, and parity-uniform Laplace envelope form the central body. Fourth-order fixed-margin calculations and their proof remain in the appendix.

A **six-page separately compiled technical supplement** now preserves the complete proofs for fixed-sample success-count extremality, the exact imbalance response, analytic contraction on compact intervals, and subsidiary curvature estimates. These results are no longer interleaved with the main proof.

The GitHub Actions publication workflow executes the **entire `run_all.sh` mathematical test suite**, builds both papers, enforces the main-paper page range, tests the bibliography and reference structure, verifies the current checksums and publishes all individual computation logs. The missing `checks/logs/verify_even_envelope_extension.log` is included and is regenerated upon every successful publication run.

The odd-envelope exact-arithmetic test is now implemented with integer-scaled probability weights: the original **28,420** population/tilt combinations and all strict/equality assertions are preserved.
