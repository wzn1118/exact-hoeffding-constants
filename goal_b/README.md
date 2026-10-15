# Goal B: all-finite hypergeometric proxy extremizers

Paper: **Balanced Populations Maximize the Optimal Sub-Gaussian Proxy for Hypergeometric Sampling at Every Finite Size**.
Author: Zinan Wang, 16 October 2026.

This directory contains an English LaTeX research manuscript, an independently designed arithmetic and numerical verifier, reproduction scripts, and a documented Lean formalization boundary. The paper proves that for every N>=2 and 1<=m<N, the maximizing marked count is exactly k=floor(N/2) or ceil(N/2), including an explicit universal positive separation from the ordinary central variance for all noncentral k.

Paper source: goal_b/paper/main.tex
Proof precursor: research/goal_B_all_finite_fixed_sample_extremizers.md

## Reproduction (no Docker)
Install Python >=3.10, NumPy and SciPy plus pdflatex with basic AMS/microtype packages.

    python -m pip install -r goal_b/requirements.txt
    python goal_b/code/verify_goal_b.py --maxN 60 --numericN 18 --output goal_b/checks/verification.json
    bash goal_b/build.sh

The build script generates the PDF manuscript and a complete source/PDF ZIP archive. GitHub Actions workflow goal-b-paper.yml runs the same procedure and stores PDF, ZIP and test report as artifacts.

## Audit summary
- 67,570 exact rational offcenter gap certificates passed for N<=60.
- 1,560 directly numerically optimized offcenter hypergeometric proxies passed for N<=18.
- 18 odd-population one-/two-draw closed-form validations passed.
- The proof for all finite N is analytic. Finite tests are independent error-detection evidence.
- Existing sharp all-tilt curvature and Bernoulli proxy input lemmas are already Lean-checked upstream at SHA 8687c3d.
- This newly assembled fixed-m finite-N theorem and strict gap have not yet been encoded and kernel-certified in Lean.
- General odd-N,m proxy values have an exact finite-sum variational representation, not a general elementary closed form.
- The manuscript has not yet received external peer review or a comprehensive priority determination; no unpublished Lee-Kim manuscript is compared.

Detailed independent audit: goal_b/checks/independent_audit.md. Formalization obligations: goal_b/checks/lean_tasks.md.

The earlier document in research/ is preserved as a dated derivation. This source-and-paper package is the primary Goal B research deliverable.
