# Submission files

**Zinan Wang · 15 October 2026**

The complete article combines the principal paper and all technical refinements in **34 pages**, with **30 theorem, proposition, lemma and corollary statements** and **16 references**. It uses one bibliography and resolves all cross-references internally.

| File | Purpose |
|---|---|
| [Complete article](release/combined_all.pdf) | The full manuscript, including the technical refinements. |
| [arXiv source archive](release/Wang_Zinan_Exact_Hoeffding_arXiv_Source_2026-10-15.zip) | Upload this ZIP in the arXiv source-upload step. It contains exactly one file, `combined_all.tex`, with no external input files. |
| [Publication bundle](release/Wang_Zinan_Exact_Hoeffding_Publication_Bundle_2026-10-15.zip) | The full article, separate 28-page principal paper and 6-page supplement, modular sources, build script, reference materials and rights notices. |
| [Reference companion](release/Wang_Zinan_Exact_Hoeffding_References_2026-10-15.zip) | Catalogue of all 16 cited works and four unchanged CC BY 4.0 reference PDFs, with source versions, licenses and checksums. |
| [Abstract](release/abstract.txt) | Copyable arXiv abstract, using standard mathematical notation. |
| [Submission metadata](release/arxiv_metadata.json) | Title, author, categories, MSC codes and comments. |
| [Build report](release/build_report.json) | Clean-directory build results, article structure and artifact hashes. |
| [SHA-256 manifest](release/SHA256SUMS.txt) | Checksums for the released files. |

For arXiv, select **Mathematics → Probability (`math.PR`)** as the primary category. `math.ST` is an optional cross-list. Enter the title and author from the metadata, paste the abstract, and upload the dedicated source ZIP. The archive has a single entry point, `combined_all.tex`, and needs pdfLaTeX with standard TeX Live packages. The reference companion and the larger publication bundle are separate reading and reproduction materials.

The displayed revision date is **15 October 2026**. The PDF and TeX source retain **Copyright © 2026 Zinan Wang. All rights reserved.** The third-party reference PDFs retain their respective CC BY 4.0 licenses, recorded in `THIRD_PARTY_NOTICES.md` and `refs/SOURCES.json`.

## Rebuild

From the repository root:

```bash
python3 checks/package_submission.py
(cd submission/release && sha256sum -c SHA256SUMS.txt)
```

The script regenerates both flattened LaTeX sources, creates the upload archive, extracts it into a new temporary directory and runs pdfLaTeX three times. It also builds the modular principal paper and supplement in a separate clean directory, checks final-pass diagnostics, validates the 30 statements and 16 bibliography entries, and verifies the four included reference PDFs against their recorded hashes. The final TeX logs and compiler output are retained in `release/build_evidence/`.

The publication bundle includes `build_articles.sh`; run `bash build_articles.sh` after extraction to rebuild all three PDFs. Lean source and formalization records are maintained in the repository alongside the manuscript.
