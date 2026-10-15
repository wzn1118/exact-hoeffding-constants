# Remaining Lean obligations for the NEW Goal B finite-N assembly

Existing proof inputs (already kernel-checked in formal/full-closure-20261015 at 8687c3d): hypergeomTiltVariance_sharp, hypergeomOptimalProxy_le_curvature, normalizedHypergeomProxy_inner_lt_bernoulli, normalizedHypergeomProxy_singleton_subhalf, complement symmetries and the hypergeometric ordinary variance formula.

New statements to formalize (do NOT mark as already proved):
1. Real artanh cubic lower bound on 0 <= d < 1, and the resulting Bernoulli proxy deficit.
2. Even/odd exact rational margin separation for all noncentral reduced k, split into m<=k and k<m.
3. Main theorem for every N>=2, 1<=m<N, 1<=k<N with exact argmax k=floor(N/2) or ceil(N/2).
4. Uniform Delta(N,m) quantitative strict gap, plus k-specific G(N,m,k).
5. Odd-central strictness via the actual hypergeometric third cumulant.
6. Optional one- and two-draw exact values via existing Bernoulli/three-mass theorems.

Verification: lake build ExactHoeffding, zero sorry/admit/custom axiom/native_decide/unsafe, #print axioms on all new top-level theorems, compare precise statements to the paper; only then call the new results kernel-certified. Reuse the pinned Lean 4.33.0/Mathlib project and push a new CI-checked commit.
