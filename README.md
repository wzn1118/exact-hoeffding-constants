# Sharp Hypergeometric Concentration

**Zinan Wang** — The University of Manchester  
**Xinhao Yang** — University of Southern California

*Exact Exchangeability Constants, Fixed-Sample Extremizers, and Piecewise KL Bounds*

This repository contains the unified mathematical article, its source and verifiable Lean 4 development. All current research is maintained on **main**.

## Current manuscript

**[Read the complete paper (PDF)](submission/current/manuscript.pdf)** · [LaTeX](submission/current/manuscript.tex) · [arXiv source](submission/current/arxiv-source.zip) · [Clean submission](submission/current/clean-submission.zip) · [Full reproducibility](submission/current/complete-reproducibility.zip)

The 36-page article has 19 references and presents three results:

1. **Exact Hoeffding constants.** For centered contrasts of bounded finitely exchangeable sequences,
   \[
   C_N^\star=\begin{cases}
     N/(N-1), & N\ \text{even},\\
     [(N-1)\operatorname{artanh}(1/N)]^{-1}, & N\ \text{odd}.
   \end{cases}
   \]
2. **Fixed-sample extremizers.** The optimal hypergeometric sub-Gaussian proxy attains its maximum at the central marked counts, with complete equality classification and strict off-center gaps for all finite admissible parameters.
3. **Piecewise KL tails.** In the domain \(3\le m\le k,\;2k\le N,\;2m<N\), the explicit rate provides upper and lower bounds and a strict improvement on ordinary binomial KL at every noncentral threshold.

## Formal verification

The project uses a pinned Lean 4 toolchain and Mathlib dependencies. The mathematical sources and check scripts are in [ExactHoeffding/](ExactHoeffding/) and [checks/](checks/). To reproduce the Lean build:

```bash
lake exe cache get
lake build ExactHoeffding
python3 checks/generate_axiom_audit.py --check
lake env lean checks/full_closure_axioms.lean
```

The reproducibility archive contains all **303 tracked Lean files**: **281** mathematical source files (including the umbrella), **21** audit files and **1** archived checker. It also includes the manuscript–theorem concordance, numerical verification programs, frozen data and pinned dependencies.

## Repository guide

| Directory | Contents |
| --- | --- |
| [submission/current/](submission/current/) | Authoritative Main+A+B manuscript and submission archives |
| [ExactHoeffding/](ExactHoeffding/) | Lean 4 mathematical definitions and proofs |
| [goal_b/](goal_b/) | Fixed-sample extremizer research and checks |
| [research/tail_bounds/](research/tail_bounds/) | Piecewise KL derivations and supporting computations |
| [checks/](checks/) | Reproduction and verification utilities |
| [source/](source/) | Foundational manuscript source |
| [research/history/](research/history/) | Historical independent checkpoints |

The current Main+A+B submission is in [`submission/current/`](submission/current/). Earlier editions and research notes are preserved in their respective source and history directories.

[Submission guide](submission/README.md) · [Citation metadata](CITATION.cff) · [Formal theorem coverage](LEAN_PROOF_STATUS.md) · [Current theorem–Lean concordance](submission/current/theorem_lean_concordance.md) · [License](LICENSE) · [Third-party notices](THIRD_PARTY_NOTICES.md)
