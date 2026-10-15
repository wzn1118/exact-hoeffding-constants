#!/usr/bin/env python3
"""Flatten the principal paper and the full article into submission entry points."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "source"
INPUT = re.compile(r"(?m)^\\input\{([A-Za-z0-9_-]+)\.tex\}\s*$")


def expand(text: str, chain: tuple[str, ...]) -> str:
    def include(match: re.Match[str]) -> str:
        name = match.group(1) + ".tex"
        if name in chain:
            raise RuntimeError("Circular TeX include: " + " -> ".join((*chain, name)))
        path = SOURCE / name
        return "\n% begin " + name + "\n" + expand(path.read_text(), (*chain, name)) + "\n% end " + name + "\n"
    return INPUT.sub(include, text)


def synchronize() -> dict[str, Path]:
    principal = (SOURCE / "manuscript.tex").read_text()
    references = r"\input{references.tex}"
    if principal.count(references) != 1:
        raise RuntimeError("The principal paper must have one bibliography input")
    supplement = (SOURCE / "supplement.tex").read_text()
    refinements = INPUT.findall(supplement.split(r"\begin{document}", 1)[1])
    if refinements != ["uniform_results", "analytic_contraction", "auxiliary_curvature"]:
        raise RuntimeError("Review the supplement input list before combining")
    appendix = "\n\\clearpage\n% Technical refinements, continuing the appendix numbering.\n" + "\n".join(r"\input{" + name + ".tex}" for name in refinements) + "\n\n"
    combined = principal.replace(references, appendix + references)
    combined = combined.replace("in the accompanying technical supplement", r"in Appendices \ref{sec:uniform_fixed}--\ref{sec:curvature_obstruction}")
    combined = combined.replace("in the technical supplement.", r"in Appendices \ref{sec:uniform_fixed}--\ref{sec:curvature_obstruction}.")
    output = ROOT / "submission"
    output.mkdir(exist_ok=True)
    result = {}
    for name, text in (("manuscript.tex", principal), ("combined_all.tex", combined)):
        path = output / name
        path.write_text(expand(text, ("manuscript.tex",)))
        if INPUT.search(path.read_text()):
            raise RuntimeError("Unexpanded input in " + name)
        result[name] = path
        print(f"PASS: {path.relative_to(ROOT)} ({path.stat().st_size} bytes)")
    return result


if __name__ == "__main__":
    synchronize()
