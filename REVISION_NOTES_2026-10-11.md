# Revision notes — 11 October 2026

This revision updates *Exact Hoeffding Constants for Finite Exchangeable Sequences* by Zinan Wang.

1. The abstract now foregrounds the exact constant and parity mechanism.
2. The Lee–Kim two-level reduction is placed before the Jacobi and polynomial arguments.
3. Rising and falling factorial conventions are explicitly distinguished; the original value of Q_j(0) was correct.
4. The quadratic variance envelope and scaled Bernoulli Laplace bound are extended to both parities for N >= 7, 3 <= m <= k <= floor(N/2), N > 2m. The even balanced margin k=N/2 gives equality for optimal proxies at zero tilt, while the Laplace comparison is strict for nonzero t.
5. The two-draw proxy comparison is extended to the even balanced boundary.
6. Cumulant calculations, an auxiliary curvature example, and compact-proportion asymptotics have moved into the appendices.
7. The parity-dependent sharp constant and odd equality classifications are preserved.

Verification:
- `python3 checks/sync_submission.py`
- `bash build_manuscript.sh`
- `python3 checks/verify_even_envelope_extension.py`
- `bash run_all.sh`

Note: `manuscript.pdf` and the archived submission ZIP are binary artifacts from the previous release; regenerate those from the updated source before considering the revision a fully synchronized PDF release.
