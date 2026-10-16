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
    if prefix=="B":
        text=re.sub(r"\\section\{Interpretation, computational audit, and formalization\}.*?(?=\\section\{Conclusion\})",
            r"\\section{Scope of the fixed-sample theorem}"+"\n"+
            "The maximizing success counts are classified at every finite population size. "+
            "The odd-population value at general fixed sample size has the exact "+
            "one-dimensional variational expression obtained above.\n",
            text,flags=re.S)
        text=re.sub(r"\\section\{Conclusion\}.*?(?=\\appendix|\Z)","",text,flags=re.S)
    if prefix=="A":
        text=re.sub(r"We use the two inequalities established in the accompanying manuscript\s+\\cite\{Wang\}:",
            "We use the two inequalities established in Part I:",text)
        text=text.replace("Throughout Sections 1--4, assume","Throughout this part, assume")
        text=re.sub(r"The results below are consequences and refinements of these established\s+inequalities; their proof does not assert a new Jacobi factorization or a\s+new two-level exchangeability reduction\.",
            "",text)
    text=text.replace(r"\appendix",r"\section*{Additional derivations}")
    text=re.sub(r"(?m)^\\noindent\\textbf\{Keywords[^\n]*\n","",text)
    text=re.sub(r"\\(label|ref|eqref|autoref|pageref)\{([^{}]+)\}",
        lambda m:"\\"+m.group(1)+"{"+prefix+":"+m.group(2)+"}",text)

    bibkeys={}
    chunks=re.findall(r"(\\bibitem(?:\[[^]]*\])?\{([^}]+)\}.*?)(?=\\bibitem|\Z)",bib,flags=re.S)
    for entry,key in chunks:
        if key not in ("Wang","Wang2026"):
            bibkeys[key]=prefix+":"+key
    def rewrite_cite(m):
        keys=[k.strip() for k in m.group(2).split(",")
              if k.strip() not in ("Wang","Wang2026")]
        if not keys:return "the preceding exact-curvature results"
        return m.group(1)+",".join(bibkeys.get(k,k) for k in keys)+m.group(3)
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
    duplicates={
        "B:Arbel":"ArbelMarchalNguyen",
        "B:ThreeMass":"AtouaniMarchalArbel",
        "B:Hoeffding":"Hoeffding",
        "B:Serfling":"Serfling",
        "B:GW":"GreeneWellner",
        "B:BM":"BardenetMaillard",
        "A:Hoeffding":"Hoeffding",
        "A:GW":"GreeneWellner",
        "A:BM":"BardenetMaillard",
    }
    def dedup_cites(text):
        return re.sub(r"(\\cite(?:\[[^]]+\])?\{)([^}]+)(\})",
            lambda m:m.group(1)+",".join(duplicates.get(k.strip(),k.strip())
              for k in m.group(2).split(","))+m.group(3),text)
    ba=dedup_cites(ba)
    bb=dedup_cites(bb)
    refs_a=[x for x in refs_a if not any(x.lstrip().startswith(r"\bibitem{"+k+"}") for k in duplicates)]
    refs_b=[x for x in refs_b if not any(x.lstrip().startswith(r"\bibitem{"+k+"}") for k in duplicates)]
    bib=bib.replace(r"\end{thebibliography}",
        "\n".join(x.strip() for x in refs_b+refs_a)+"\n"+r"\end{thebibliography}")
    pre=re.sub(r"\\title\{.*?\\author\{",
        r"\\title{\\bfseries Sharp Hypergeometric Concentration: Exact Exchangeability Constants,\\ Fixed-Sample Extremizers, and Piecewise KL Bounds}\n\\author{",
        pre,count=1,flags=re.S)
    pre+="\n"+r"\DeclareMathOperator*{\argmax}{arg\,max}"+"\n"
    pre=re.sub(r"\\date\{[^}]+\}",r"\\date{16 October 2026}",pre,count=1)
    pre=pre.replace(r"\fancyhead[LO]{\small WANG -- SHARP FINITE EXCHANGEABILITY}",
                    r"\fancyhead[LO]{\small WANG -- HYPERGEOMETRIC CONCENTRATION}")
    add=("\n"+r"\noindent\textbf{Additional results.} "
         "For every fixed sample size, the optimal hypergeometric sub-Gaussian "
         "proxy is attained exactly at central success counts. In the canonical "
         "interior range, a piecewise KL rate gives explicit upper and lower tails "
         "and improves the ordinary binomial rate at noncentral thresholds.\n")
    core=core.replace(r"\end{abstract}",add+r"\end{abstract}",1)
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
    citations={key.strip() for group in re.findall(r"\\cite(?:\[[^]]+\])?\{([^}]+)\}",tex) for key in group.split(",")}
    bibitems=set(re.findall(r"\\bibitem(?:\[[^]]+\])?\{([^}]+)\}",tex))
    assert citations.issubset(bibitems), "unresolved citations: "+str(citations-bibitems)
    print("Generated:",dest,"bytes:",dest.stat().st_size)

if __name__=="__main__":
    main()
