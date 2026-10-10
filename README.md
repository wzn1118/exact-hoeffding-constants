# Exact Hoeffding Constants for Finite Exchangeable Sequences

**Zinan Wang** · 10 October 2026

**Copyright (c) 2026 Zinan Wang. All rights reserved.** See [LICENSE](LICENSE) and [COPYRIGHT.md](COPYRIGHT.md).

[Read the manuscript](manuscript.pdf) · [Single-file source](submission/manuscript.tex) · [Chinese guide](README_zh.md) · [References](refs/README_zh.md)

This manuscript determines the optimal Hoeffding constant for centered linear contrasts of bounded exchangeable sequences of every finite length:

$$
C_N^\star=\begin{cases}
\displaystyle\frac{N}{N-1},&N\text{ even},\\[4pt]
\displaystyle\frac{1}{(N-1)\operatorname{artanh}(1/N)},&N\text{ odd}.
\end{cases}
$$

For even populations, the constant equals the largest normalized variance. For odd populations, it strictly exceeds that variance constant and is attained at an explicit nonzero Laplace argument.

The article proves a sharp hypergeometric tilted-variance bound, a uniform odd-population Laplace comparison, the complete odd hypergeometric extremizer classification, and fourth-order optimized proxy expansions. It also proves success-count extremality for each fixed sample size and all sufficiently large odd populations.

The two-level reduction is attributed to Lee and Kim. The three-point optimal proxy formula used for two draws is attributed to Atouani, Marchal and Arbel. Their proofs and applications are presented with explicit attribution in the manuscript.

## Files

| Path | Contents |
| --- | --- |
| `manuscript.pdf` | Complete 33-page article |
| `source/` | Modular LaTeX source, including proofs and bibliography |
| `submission/` | Self-contained LaTeX source and source ZIP |
| `docs/` | Chinese proof notes, contribution map and reading guide |
| `checks/` | Mathematical verification scripts and calculation records |
| `refs/` | Bibliographic records, source links and four licensed reference PDFs |
| `CITATION.cff` | Citation metadata |
| `SHA256SUMS.txt` | File integrity checks |

## Build and Verify

The manuscript requires pdfLaTeX and the packages listed in `source/manuscript.tex`. The mathematical scripts require Python 3.10 or later, SymPy and mpmath.

```bash
python3 -m pip install -r requirements.txt
bash run_all.sh
```

To compile only the manuscript:

```bash
bash build_manuscript.sh
```

To verify the published files before rebuilding:

```bash
sha256sum -c SHA256SUMS.txt
```

## Cite

Zinan Wang. *Exact Hoeffding Constants for Finite Exchangeable Sequences*. Manuscript, 10 October 2026.

## Rights

The original manuscript, author-created source, documentation and verification code remain the property of Zinan Wang. They are published with all rights reserved, without an open-source or Creative Commons license for that original material.

Third-party reference PDFs retain their authors' rights and their individual CC BY 4.0 licenses. See [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md). The author's notice does not override those licenses. GitHub's service permissions and rights provided by applicable law remain unaffected.
