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


def polish_integrated(text):
    """Apply manuscript-only copyediting after mathematical source assembly."""
    def sub(old, new):
        nonlocal text
        if text.count(old) != 1:
            raise RuntimeError("Language edit anchor count: " + str(text.count(old)) + " / " + old[:75])
        text = text.replace(old, new)
    def rex(pattern, replacement):
        nonlocal text
        text, n = re.subn(pattern, lambda m: replacement, text, count=1, flags=re.S)
        if n != 1:
            raise RuntimeError("Language edit regex missing: " + pattern[:80])

    sub(r"\hypersetup{pdftitle={Exact Hoeffding Constants for Finite Exchangeable Sequences}",
        r"\hypersetup{pdftitle={Sharp Hypergeometric Concentration: Exact Exchangeability Constants, Fixed-Sample Extremizers, and Piecewise KL Bounds}")
    sub(r"\fancyhead[LO]",r"\fancyhead[L]")
    sub(r"\author{Zinan Wang\thanks{Copyright \textcopyright\ 2026 Zinan Wang. All rights reserved.}\\{\small The University of Manchester}\and Xinhao Yang\\{\small University of Southern California}}",
        r"\author{Zinan Wang\\{\small The University of Manchester}\and Xinhao Yang\\{\small University of Southern California}}")
    sub(r"\noindent\textbf{Additional results.} For every fixed sample size, the optimal hypergeometric sub-Gaussian proxy is attained exactly at central success counts. In the canonical interior range, a piecewise KL rate gives explicit upper and lower tails and improves the ordinary binomial rate at noncentral thresholds.",
        "For each fixed sample size, we identify the central success counts as the unique maximizers of the optimal hypergeometric sub-Gaussian proxy, up to complementation, and establish quantitative gaps for all other margins. On the canonical interior parameter domain, the two tilted-variance envelopes yield an explicit piecewise relative-entropy rate for both tails. The resulting rate strictly improves the binomial KL rate at every noncentral threshold.")
    sub(r"Jacobi polynomials; exponential tilting; Riccati equation.\\",
        r"Jacobi polynomials; exponential tilting; Riccati equation; fixed-sample extremizers; piecewise KL concentration.\\")
    sub("The finer fixed-sample extremality and compact-proportion comparison, together with subsidiary curvature examples, are given in the accompanying technical supplement. These refinements have no role in the proof of Theorem "+r"\ref{thm:exchange}.",
        "The fixed-sample success-count extremality theorem appears in Section "+r"\ref{sec:fixedsample}"+", while the piecewise relative-entropy tail bound is proved in Section "+r"\ref{sec:piecewise}"+".")
    sub("The main statements are followed immediately by the exchangeability-to-hypergeometric reduction. We then develop the curvature estimate, determine the parity-dependent sharp constants, and establish the unified Laplace envelope. The odd-population extremizers and the uniform envelope complete the main argument. Fourth-order asymptotics and computational algebra are placed in the appendices, with additional finite-sample refinements in the technical supplement.",
        "The two-level exchangeability reduction leads to the curvature theorem, parity-dependent sharp constants, and quadratic Laplace envelope. The subsequent fixed-sample extremizer theorem and piecewise KL bounds develop their finite-sample consequences. Fourth-order asymptotics and supporting algebraic calculations appear in the appendices.")
    rex(r"\\clearpage\s*\\part\{Fixed-sample optimal sub-Gaussian proxies\}.*?\\section\{Distribution, proxy, and input bounds\}",
        r"\section{Fixed-sample optimal sub-Gaussian proxies}\label{sec:fixedsample}"+ "\n"+
        r"For a sample of fixed size $m$, the hypergeometric variance is maximized at the central success counts. Skewed bounded laws can have optimal centered sub-Gaussian proxies strictly larger than their variances \cite{ArbelMarchalNguyen}. We prove that central success counts also maximize the optimal proxy for every finite population size and quantify the deficit at every noncentral margin. The proof combines the curvature bound and scaled Bernoulli comparison established above."+
        "\n\n"+r"\subsection{Distribution, proxy, and input bounds}")
    sub(r"\begin{proposition}[Proved analytic inputs from the preceding exact-curvature results]\label{B:inputs}",
        r"\begin{proposition}[Curvature and Bernoulli proxy bounds]\label{B:inputs}")
    rex(r"The upstream theorem names include.*?is required when invoking \\eqref\{B:C\}--\\eqref\{B:B\}\.\s*","")
    sub(r"\section{The exact finite extremizer theorem}",r"\subsection{The exact finite extremizer theorem}")
    sub(r"\section{Value at the maximizing margin}",r"\subsection{Value at the maximizing margin}")
    sub("No uniqueness or universal elementary closed form is asserted.\n","")
    sub(r"\section{Scope of the fixed-sample theorem}"+"\n"+
        "The maximizing success counts are classified at every finite population size. The odd-population value at general fixed sample size has the exact one-dimensional variational expression obtained above.\n\n","")
    sub("For "+r"$N=2n+1\ge3$"+" and any "+r"$1\le m<N$"+",\n"+
        r"$\max_{1\le k<N}S_{N,m}(k)=S_{N,m}(n)>W_{N,m}$"+".",
        "For "+r"$N=2n+1\ge3$"+" and any "+r"$1\le m<N$"+",\n"+
        r"\["+"\n"+r"\max_{1\le k<N}S_{N,m}(k)=S_{N,m}(n)>W_{N,m}."+"\n"+r"\]")
    rex(r"\\clearpage\s*\\part\{Piecewise relative-entropy concentration\}.*?\\section\{Parameters and established variance inequalities\}",
        r"\section{Piecewise relative-entropy concentration}\label{sec:piecewise}"+
        "\nThe two hypergeometric tilted-variance envelopes yield an explicit piecewise relative-entropy rate for both tails.\n\n"+
        r"\subsection{Parameters and variance inequalities}")
    for a,b in [
        (r"\section{Integration in the tilted mean}",r"\subsection{Integration in the tilted mean}"),
        (r"\section{A closed piecewise rate}",r"\subsection{The piecewise KL rate}"),
        (r"\section{Comparison boundaries}",r"\subsection{Comparison with classical and optimized bounds}"),
        (r"\subsection{Four binomial KL bounds}",r"\subsubsection{Four binomial KL bounds}"),
        (r"\subsection{The optimal uniform quadratic coefficient}",r"\subsubsection{The optimal uniform quadratic coefficient}"),
        (r"\subsection{Exact-variance Bennett and Bernstein bounds}",r"\subsubsection{Exact-variance Bennett and Bernstein bounds}"),
        (r"\subsection{Optimized factorial moments}",r"\subsubsection{Optimized factorial moments}"),
        ("We use the two inequalities established in Part I:","The preceding variance and Laplace comparison results give"),
        ("the preceding exact-curvature results give "+r"$P(0)>0$"+" and "+r"$P(m)>0$"+".",
         "explicit endpoint evaluations give "+r"$P(0)>0$"+" and "+r"$P(m)>0$"+"."),
        ("Thus an endpoint of the hypergeometric support never requires an invalid\nKL argument in "+r"\eqref{A:IP}"+".",
         "Consequently, the KL argument in "+r"\eqref{A:IP}"+" remains in "+r"$(0,1)$"+" at both support endpoints."),
        ("For completeness, direct optimization of the established Laplace bound","Direct optimization of the Laplace envelope"),
        ("For an abstract\nBernoulli envelope, "+r"$\theta=0,1$"+" are interpreted by "+r"$t\to\mp\infty$"+";\nvalues outside "+r"$[0,1]$"+" are not inserted into "+r"$D$"+".",
         "At "+r"$\theta=0$"+" or "+r"$1$"+", the Bernoulli transform is defined by the limits "+r"$t\to\mp\infty$"+". The relative entropy "+r"$D(\theta\Vert p)$"+" has domain "+r"$0\le\theta\le1$"+"."),
        ("This is the coefficient for "+r"$H-\mu$"+" obtained from the exact uniform\nexchangeability constant in the preceding exact-curvature results, in the convention",
         "The exact uniform exchangeability constant in Theorem~"+r"\ref{thm:exchange}"+" gives this coefficient for "+r"$H-\mu$"+", with"),
        ("Thus the scaled KL and piecewise bounds are never weaker than this\nparticular uniform quadratic bound. They need not dominate the numerically\noptimized quadratic proxy for each fixed hypergeometric law.",
         "Both KL rates therefore improve the displayed uniform quadratic bound. The optimized quadratic proxy of an individual hypergeometric law may yield a stronger bound."),
        ("This does not compare "+r"$J$"+" with Greene--Wellner's\nother bounds containing a prefactor and a quartic exponent.\n",""),
        ("Optimized hypergeometric factorial-moment bounds are already studied\nin "+r"\cite{A:MZC}"+"; neither that method nor its optimization is new here.\nEarlier comparisons of moment bounds with Chernoff bounds include\nPhilips and Nelson~"+r"\cite{A:PN}"+"; Proposition~"+r"\ref{A:factorial}"+" provides the\nfinite integer-valued binomial-basis argument used for the present comparison.",
         "Optimized hypergeometric factorial-moment bounds appear in "+r"\cite{A:MZC}"+". Comparisons of moment bounds with Chernoff bounds also appear in Philips and Nelson~"+r"\cite{A:PN}"+". Proposition~"+r"\ref{A:factorial}"+" establishes the finite binomial-basis inequality used here."),
        ("At "+r"$d=\min(k,m)$"+" the valid endpoint\nindex is "+r"$j=d$"+"; one must not use the undefined denominator\n"+r"$(d)_{\underline{d+1}}$"+". These facts set a precise comparison boundary:\nthe piecewise KL expression is an explicit refinement of the stated KL\nand uniform quadratic envelopes, not a universal improvement over\noptimized factorial moments or all existing finite-population bounds.",
         "At "+r"$d=\min(k,m)$"+" the admissible endpoint index is "+r"$j=d$"+". The piecewise KL rate improves the stated KL and uniform quadratic envelopes, while optimized factorial-moment bounds can be sharper at integer thresholds.")
    ]:
        sub(a,b)
    if any(t in text for t in ("companion work","Additional results.","No unpublished collaboration manuscript","We use the two inequalities established in Part I:")):
        raise RuntimeError("Defensive/composite text remains after polish")
    labs=re.findall(r"\\label\{([^{}]+)\}",text)
    if len(labs)!=len(set(labs)):raise RuntimeError("Duplicate labels after polish")
    return text


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
    pre=re.sub(r"pdftitle=\{[^}]+\}",
        "pdftitle={Sharp Hypergeometric Concentration: Exact Exchangeability Constants, Fixed-Sample Extremizers, and Piecewise KL Bounds}",pre,count=1)
    pre+="\n"+r"\DeclareMathOperator*{\argmax}{arg\,max}"+"\n"
    pre=re.sub(r"\\date\{[^}]+\}",r"\\date{16 October 2026}",pre,count=1)
    pre=pre.replace(r"\fancyhead[LO]{\small WANG AND YANG -- SHARP FINITE EXCHANGEABILITY}",
                    r"\fancyhead[LO]{\small WANG AND YANG -- HYPERGEOMETRIC CONCENTRATION}")
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
    tex = polish_integrated(tex)
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
