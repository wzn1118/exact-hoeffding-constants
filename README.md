# Exact Hoeffding Constants for Finite Exchangeable Sequences

**Zinan Wang** · Revised 11 October 2026

**Copyright (c) 2026 Zinan Wang. All rights reserved.** See [LICENSE](LICENSE) and [COPYRIGHT.md](COPYRIGHT.md).

[Main paper — 28 pages](manuscript.pdf) · [Technical supplement — 6 pages](supplementary_refinements.pdf) · [Single-file submission source](submission/manuscript.tex) · [Chinese guide](README_zh.md)

The paper determines the sharp Hoeffding coefficient for centered linear contrasts of bounded, finitely exchangeable sequences:
\[
C_N^\star=\begin{cases}
\displaystyle \frac{N}{N-1},&N\text{ even},\\[4pt]
\displaystyle[(N-1)\operatorname{artanh}(1/N)]^{-1},&N\text{ odd}.
\end{cases}
\]

The main paper proves the two-level reduction, all-tilt hypergeometric curvature theorem, parity-uniform Laplace envelope, optimal coefficient, and odd-population equality classification. The fixed-margin fourth-order expansion is retained in the appendix. The separate technical supplement contains the complete proofs of fixed-sample success-count extremality, compact-proportion analytic contraction, and subsidiary curvature results.

## Publication files

- `manuscript.pdf`: the **28-page main article**, including full proofs of its sharp constant and envelope theorems.
- `supplementary_refinements.pdf`: the **6-page independently compiled technical supplement**.
- `source/manuscript.tex` and `source/supplement.tex`: modular LaTeX entry points.
- `submission/manuscript.tex`: standalone, single-file LaTeX source for the main article.
- `checks/`: exact-symbolic, rational and high-precision tests.
- `checks/logs/`: individual mathematical and two PDF compilation logs, published by CI.
- `SHA256SUMS.txt`: maintained-file integrity checks.

## Full reproduction

Requires Python 3.10+, SymPy, mpmath, pdfLaTeX, and the manuscript packages.

```bash
python3 -m pip install -r requirements.txt
python3 checks/sync_submission.py
bash run_all.sh
python3 checks/refresh_checksums.py
sha256sum -c SHA256SUMS.txt
```

The [CI publication workflow](.github/workflows/publish-manuscript.yml) runs **all eleven** mathematical tests through `run_all.sh`, including the even-population Laplace-envelope extension. It then validates both PDFs, verifies the checksums and publishes the PDFs and complete logs to `main`. A successful compilation alone is not accepted as a valid publication.

## Citation and rights

Zinan Wang. *Exact Hoeffding Constants for Finite Exchangeable Sequences*. Revised manuscript, 11 October 2026.

Original text, author-created source and verification scripts remain all-rights-reserved. Third-party reference PDFs retain their own licenses; see [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).
