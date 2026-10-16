#!/usr/bin/env python3
"""Build a clean unified manuscript from the three proven source texts.

Original mathematical statements and proofs remain in full; labels and
references are made unique, and the bibliographies are consolidated.
"""
from pathlib import Path
import re

ROOT=Path(__file__).resolve().parents[2]
OUT=Path(__file__).resolve().parent
M=ROOT/"submission/manuscript.tex"
A=ROOT/"research/tail_bounds/minimum_variance_tail.tex"
B=ROOT/"goal_b/paper/main.tex"

def extension(src, prefix):
    text=src.split(r"\begin{document}",1)[1].rsplit(r"\end{document}",1)[0]
    text=re.sub(r"\\maketitle\s*","",text,count=1)
    text=re.sub(r"\\begin\{abstract\}.*?\\end\{abstract\}\s*","",text,count=1,flags=re.S)
    start=re.search(r"\\begin\{thebibliography\}(?:\{[^}]*\})?",text)
    if not start: raise RuntimeError(prefix+" bibliography missing")
    end=re.search(r"\\end\{thebibliography\}",text[start.end():])
    if not end: raise RuntimeError(prefix+" bibliography not closed")
    bib=text[start.end():start.end()+end.start()]
    text=text[:start.start()]+text[start.end()+end.end():]
    if prefix=="B":
        for h in ("Independent computational audit","Relation to machine-checked results","Audit checklist and provenance"):
            hit=re.search(r"\\(?:section|subsection)\{"+re.escape(h)+r"\}",text)
            if hit:
                nx=re.search(r"\\(?:section|subsection|appendix)\b",text[hit.end():])
                cut=hit.end()+nx.start() if nx else len(text)
                text=text[:hit.start()]+text[cut:]
    text=text.replace(r"\appendix",r"\section*{Additional derivations}")
    text=re.sub(r"(?m)^\\noindent\\textbf\{Keywords[^\n]*\n","",text)
    text=re.sub(r"\\(label|ref|eqref|autoref|pageref)\{([^{}]+)\}",
        lambda m:"\\"+m.group(1)+"{"+prefix+":"+m.group(2)+"}",text)
    text=text.replace(r"\cite{Wang2026}","the preceding exact-curvature results")
    text=text.replace(r"\cite{Wang}","the exact-curvature theorem above")
    bibkeys={}
    chunks=re.findall(r"(\\bibitem(?:\[[^]]*\])?\{([^}]+)\}.*?)(?=\\bibitem|\Z)",bib,flags=re.S)
    for entry,key in chunks:
        if key not in ("Wang","Wang2026"):
            bibkeys[key]=prefix+":"+key
    def rewrite_cite(m):
        keys=[bibkeys.get(k.strip(),k.strip()) for k in m.group(2).split(",")]
        return m.group(1)+",".join(keys)+m.group(3)
    text=re.sub(r"(\\cite(?:\[[^]]+\])?\{)([^}]+)(\})",rewrite_cite,text)
    entries=[entry.replace("{"+key+"}","{"+bibkeys[key]+"}",1)
             for entry,key in chunks if key in bibkeys]
    return text,entries

def main():
    for p in (M,A,B):
        if not p.exists(): raise FileNotFoundError(str(p))
    src=M.read_text(encoding="utf-8")
    mb=re.search(r"\\begin\{thebibliography\}\{99\}.*?\\end\{thebibliography\}",src,re.S)
    if not mb: raise RuntimeError("main bibliography missing")
    bib=mb.group()
    src=src[:mb.start()]+src[mb.end():]
    pre,body=src.split(r"\begin{document}",1)
    body=body.rsplit(r"\end{document}",1)[0]
    if r"\appendix" not in body:raise RuntimeError("main appendix missing")
    core,appendix=body.split(r"\appendix",1)
    ba,refs_a=extension(A.read_text(encoding="utf-8"),"A")
    bb,refs_b=extension(B.read_text(encoding="utf-8"),"B")
    bib=bib.replace(r"\end{thebibliography}",
        "\n".join(x.strip() for x in refs_b+refs_a)+"\n"+r"\end{thebibliography}")
    pre=re.sub(r"\\title\{.*?\\author\{",
        r"\\title{\\bfseries Sharp Hypergeometric Concentration: Exact Exchangeability Constants,\\ Fixed-Sample Extremizers, and Piecewise KL Bounds}\n\\author{",
        pre,count=1,flags=re.S)
    pre+="\n"+r"\DeclareMathOperator*{\argmax}{arg\,max}"+"\n"
    add=("\n"+r"\noindent\textbf{Additional results.} "
         "For every fixed sample size, the optimal hypergeometric sub-Gaussian "
         "proxy is attained exactly at central success counts. In the canonical "
         "interior range, a piecewise KL rate gives explicit upper and lower tails "
         "and improves the ordinary binomial rate at noncentral thresholds.\n")
    core=core.replace(r"\end{abstract}",r"\end{abstract}"+add,1)
    intro=("\n\\clearpage\n\\part{Fixed-sample optimal sub-Gaussian proxies}\n"
           "The all-tilt curvature and scaled Bernoulli envelope established "
           "above are used to determine the exact maximizing success counts.\n")
    into_a=("\n\\clearpage\n\\part{Piecewise relative-entropy concentration}\n"
            "The two mean-dependent hypergeometric variance envelopes give "
            "piecewise KL concentration for canonical interior margins.\n")
    tex=(pre+r"\begin{document}"+"\n"+core+intro+bb+into_a+ba+
         "\n"+r"\appendix"+"\n"+appendix+"\n"+bib+
         "\n"+r"\end{document}"+"\n")
    OUT.mkdir(exist_ok=True)
    dest=OUT/"combined_manuscript.tex"
    dest.write_text(tex,encoding="utf-8")
    labels=re.findall(r"\\label\{([^{}]+)\}",tex)
    assert len(set(labels))==len(labels),"duplicate theorem/equation labels"
    refs=set(re.findall(r"\\(?:ref|eqref|autoref|pageref)\{([^{}]+)\}",tex))
    assert refs.issubset(set(labels)), "unresolved references: "+str(refs-set(labels))
    print("Generated:",dest,"bytes:",dest.stat().st_size)

if __name__=="__main__":
    main()
