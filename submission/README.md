# Main+A+B manuscript and submission materials

**Zinan Wang** — The University of Manchester  
**Xinhao Yang** — University of Southern California

## Official current manuscript

The single current publication entry is [`submission/current/`](current/): the 37-page, 20-reference unified paper, standalone LaTeX source, arXiv upload archive, clean submission archive, complete reproducibility package, and theorem–Lean concordance.

- [Paper PDF](current/manuscript.pdf)
- [Standalone LaTeX](current/manuscript.tex)
- [arXiv source ZIP](current/arxiv-source.zip)
- [Clean submission ZIP](current/clean-submission.zip)
- [Complete reproducibility ZIP](current/complete-reproducibility.zip)
- [Submission metadata](current/metadata.json)
- [Manuscript–Lean concordance](current/theorem_lean_concordance.md)
- [240-display source review binding](../formal_status/display_formula_audit_current_20261018.md)

`submission/current/manuscript.tex` is the frozen complete manuscript. `submission/manuscript.tex`, `goal_b/paper/main.tex`, and `research/tail_bounds/minimum_variance_tail.tex` are its three component sources; none is a standalone replacement for the unified paper.

## Rebuild

Install Python, pdfLaTeX, latexmk, Poppler `pdfinfo`, and the pinned Lean toolchain, then run from the repository root:

```bash
python3 submission/integrated/build_clean_submission.py
(cd submission/integrated && latexmk -pdf -halt-on-error combined_manuscript.tex)
python3 checks/build_current_release.py
```

The generated `submission/integrated/combined_manuscript.tex` and PDF are build outputs. The release builder checks them against the frozen official source, validates PDF metadata and references, confirms all tracked Lean source files are included, and regenerates checksummed submission archives.

## Historical editions

The root-level `manuscript.pdf`, `supplementary_refinements.pdf`, and `submission/combined_all.tex` were 16 October Main-only release files. They are not current submission entry points; their dated release packages are preserved under [`research/history/release-archives/2026-10-15-16/`](../research/history/release-archives/2026-10-15-16/). Earlier display-formula audits are retained as source-specific historical records; the current 240-display binding is the report linked above.
The matching `run_all.sh`, `build_manuscript.sh`, and old publication workflow were retired with that release line. The current extracted-package command is `bash checks/verify_current_reproducibility.sh`.
