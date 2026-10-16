# Authoritative Main+A+B submission

**Zinan Wang** — The University of Manchester  
**Xinhao Yang** — University of Southern California

The only current unified submission is maintained in the [current release directory](current/README.md).

- [Current paper PDF](current/manuscript.pdf)
- [Single-file LaTeX](current/manuscript.tex)
- [arXiv source archive](current/arxiv-source.zip) (one TeX file)
- [Clean paper submission archive](current/clean-submission.zip)
- [Full formal and numerical reproducibility archive](current/complete-reproducibility.zip)
- [Author and classification metadata](current/metadata.json)

The corresponding LaTeX is assembled from submission/manuscript.tex, goal_b/paper/main.tex, and research/tail_bounds/minimum_variance_tail.tex. Each source retains its own full mathematical proof. The integrated PDF is checked for metadata, duplicate labels and unresolved citations.

To reproduce the current submission after installing pdfLaTeX, latexmk, Python and the pinned Lean toolchain:

    python3 submission/integrated/build_clean_submission.py
    (cd submission/integrated && latexmk -pdf -halt-on-error combined_manuscript.tex)
    python3 checks/build_current_release.py

The separate original main paper (28 pages), supplement (6 pages), and older combined_all.tex release have historical value, but are superseded for unified Main+A+B submissions. The legacy packaging script checks/package_submission.py is retained for reproducing that historical edition.

The full reproducibility archive contains the mathematical and formal verification sources, check programs, frozen inputs and dependency pins, with a single disclosure of AI assistance in Lean 4 formalization and verification.
