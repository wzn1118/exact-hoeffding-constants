# Main+A+B manuscript and submission materials

**Zinan Wang** — The University of Manchester  
**Xinhao Yang** — University of Southern California

The [current submission directory](current/) contains the 37-page unified paper, its standalone LaTeX source, arXiv upload archive and full formal/numerical reproducibility package.

- [Paper PDF](current/manuscript.pdf)
- [Standalone LaTeX](current/manuscript.tex)
- [arXiv source ZIP](current/arxiv-source.zip)
- [Clean submission ZIP](current/clean-submission.zip)
- [Complete reproducibility ZIP](current/complete-reproducibility.zip)
- [Submission metadata](current/metadata.json)
- [Manuscript–Lean concordance](current/theorem_lean_concordance.md)

The unified LaTeX is assembled from `submission/manuscript.tex`, `goal_b/paper/main.tex` and `research/tail_bounds/minimum_variance_tail.tex`.

## Rebuild

Install Python, pdfLaTeX, latexmk and the repository's pinned Lean toolchain, then run from the repository root:

```bash
python3 submission/integrated/build_clean_submission.py
(cd submission/integrated && latexmk -pdf -halt-on-error combined_manuscript.tex)
python3 checks/build_current_release.py
```

The release builder checks PDF metadata, reference integrity, all tracked Lean source files and archive checksums. The older Main article, supplement and `combined_all.tex` edition remain in their original locations as dated research documents.
