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


def polish_language_clarity(text):
    """Precisely apply the full integrated-manuscript copyedit, preserving the mathematical notation."""
    replacements = [["The even coefficient coincides with the maximal normalized variance. In odd populations the optimal Laplace parameter is nonzero, and the sharp coefficient strictly exceeds the variance benchmark. We obtain the result through a two-level reduction to hypergeometric laws, a global tilted-variance bound, and a mean-dependent quadratic envelope for their Laplace transforms. The envelope holds for both parities throughout the sub-half-population parameter range; parity enters when the remaining discrete margins are optimized. The proof also determines all odd-population extremizers.","The even coefficient coincides with the maximal normalized variance. In odd populations the optimal Laplace parameter is nonzero, and the sharp coefficient strictly exceeds the variance benchmark. We obtain the result through a two-level reduction to hypergeometric laws, a global tilted-variance bound, and a mean-dependent quadratic envelope for tilted hypergeometric variance. The quadratic envelope holds for both parities when $3\\le m\\le k\\le\\lfloor N/2\\rfloor$ and $2m<N$; parity enters when the remaining discrete margins are optimized. The proof also determines all odd-population extremizers."],
        ["For each fixed sample size, we identify the central success counts as the unique maximizers of the optimal hypergeometric sub-Gaussian proxy, up to complementation, and establish quantitative gaps for all other margins. On the canonical interior parameter domain, the two tilted-variance envelopes yield an explicit piecewise relative-entropy rate for both tails. The resulting rate strictly improves the binomial KL rate at every noncentral threshold.","For each fixed sample size, we identify the central success counts as the unique maximizers of the optimal hypergeometric sub-Gaussian proxy, up to complementation, and establish quantitative gaps for all other margins. For $3\\le m\\le k\\le\\lfloor N/2\\rfloor$ and $2m<N$, the two tilted-variance envelopes yield an explicit piecewise relative-entropy rate for both tails. The resulting rate strictly improves the binomial KL rate at every noncentral threshold."],
        ["uniformly over the law of $X$ and the contrast $a$. Zero padding and orthogonal projection give the equivalent formulation for $\\sum_{i=1}^n w_i(X_i-\\bar X_N)$, where $\\bar X_N=N^{-1}\\sum_iX_i$. This formulation includes arbitrary signed weights.","uniformly over the law of $X$ and the contrast $a$. Zero padding and orthogonal projection give the equivalent formulation for $\\sum_{i=1}^n w_i(X_i-\\bar X_N)$, where $\\bar X_N=N^{-1}\\sum_iX_i$. The zero-padded weighted-contrast formulation permits arbitrary signed weights."],
        ["For independent bounded variables the reference coefficient is one. Finite exchangeability introduces an exact population-dependent inflation. Barber \\cite{Barber,BarberErratum} established weighted exchangeable Hoeffding bounds, and Lee and Kim \\cite{LeeKim} obtained an upper coefficient $1+3/(2N)+O(N^{-2})$, a matching order-$N^{-1}$ lower bound, and an exact hypergeometric variational representation. We evaluate that representation for every $N$. The answer is $N/(N-1)$ when $N$ is even and $[(N-1)\\operatorname{artanh}(1/N)]^{-1}$ when $N$ is odd.","For independent bounded variables the reference coefficient is one. Finite exchangeability introduces an exact population-dependent inflation. Barber \\cite{Barber,BarberErratum} established weighted exchangeable Hoeffding bounds, and Lee and Kim \\cite{LeeKim} obtained an upper coefficient $1+3/(2N)+O(N^{-2})$, a matching order-$N^{-1}$ lower bound, and an exact hypergeometric variational representation. We evaluate that representation for every $N$. The resulting optimal constant is $N/(N-1)$ when $N$ is even and $[(N-1)\\operatorname{artanh}(1/N)]^{-1}$ when $N$ is odd."],
        ["Thus the odd coefficient measures a genuine exponential-moment effect beyond the largest variance. A single coordinate centered by the population mean, $X_1-\\bar X_N$, attains the odd bound at the explicit nonzero argument $\\log((N+1)/(N-1))$ on a nearest-balanced Hamming slice. Proposition \\ref{prop:variance_parity} and Proposition \\ref{prop:explicit_extremizer} make this distinction precise.","Thus the odd coefficient measures a genuine exponential-moment effect beyond the largest variance. A single coordinate centered by the population mean, $X_1-\\bar X_N$, attains the odd bound at the explicit nonzero argument $\\log((N+1)/(N-1))$ on a nearest-balanced Hamming slice. Propositions \\ref{prop:variance_parity} and \\ref{prop:explicit_extremizer} distinguish the maximal variance from the nonzero-tilt Laplace optimum."],
        ["The central reduction identifies the exact finite-population problem with an optimization over hypergeometric random variables. The convex reduction to Hamming slices is followed by the two-level extremal principle of Lee and Kim, giving","The Lee--Kim two-level reduction converts the finite-exchangeability contrast problem into an optimization over hypergeometric moment generating functions. The convex reduction to Hamming slices is followed by the two-level extremal principle of Lee and Kim, giving"],
        ["We state and prove this variational identity immediately after the main results. In particular, a sharp estimate for each hypergeometric law can be transferred to every signed contrast of the original exchangeable sequence.","We state and prove the Lee--Kim variational identity \\eqref{eq:LKidentity} immediately after the main results. In particular, a sharp estimate for each hypergeometric law can be transferred to every signed contrast of the original exchangeable sequence."],
        ["Two complementary estimates determine the optimum. First, a sharp bound on hypergeometric variance at every exponential tilt implies the universal coefficient $N/(N-1)$, which is attained for even populations. Second, a quadratic upper envelope for variance as a function of the tilted mean gives a scaled-Bernoulli Laplace comparison. The certificate for this envelope is valid in the sub-half-population regime for both parities. For odd $N$, all admissible success counts stay away from the exact half-population balance; optimizing the Bernoulli comparison then singles out the one-draw laws. For even $N$, the balanced zero-tilt equality accounts for the sharp constant. This separation of the continuous Laplace comparison from the discrete optimization isolates the role of parity.","Two complementary estimates determine the optimum. First, a sharp bound on hypergeometric variance at every exponential tilt implies the universal coefficient $N/(N-1)$, which is attained for even populations. Second, a quadratic upper envelope for variance as a function of the tilted mean gives a scaled-Bernoulli Laplace comparison. The positive-definite certificate proves the mean-dependent quadratic bound on tilted variance for both parities in the stated sub-half-population regime. For odd $N$, all admissible success counts stay away from the exact half-population balance; optimizing the Bernoulli comparison then singles out the one-draw laws. For even $N$, the balanced zero-tilt equality accounts for the sharp constant. Separating the continuous Laplace comparison from the discrete margin optimization isolates the role of parity."],
        ["The proof of the sharp constant rests on two global ingredients: the all-tilt hypergeometric curvature bound and the parity-uniform quadratic Laplace envelope. The complete classification of odd-population equality cases is part of the central theorem. Appendix \\ref{sec:odd_asym} records fourth-order expansions for fixed margins. The fixed-sample success-count extremality theorem appears in Section \\ref{sec:fixedsample}, while the piecewise relative-entropy tail bound is proved in Section \\ref{sec:piecewise}.","The proof of the sharp constant rests on two global ingredients: the all-tilt hypergeometric curvature bound and the parity-uniform quadratic Laplace envelope. The complete classification of odd-population equality cases is part of Theorem \\ref{thm:exchange}. Appendix \\ref{sec:odd_asym} records fourth-order expansions for fixed margins. The fixed-sample success-count extremality theorem appears in Section \\ref{sec:fixedsample}, while the piecewise relative-entropy tail bound is proved in Section \\ref{sec:piecewise}."],
        ["Kou and Ying \\cite{Kou} connect fixed-margin laws with Jacobi polynomials and sums of independent Bernoulli variables; Borcea, Br\\\"and\\'en, and Liggett \\cite{BBL} develop the broader stability framework. The Jacobi identities and zero-location theorem are classical \\cite[Chapter IV and Section 6.7]{Szego}. Arbel, Marchal, and Nguyen \\cite{ArbelMarchalNguyen} study optimal variance proxies and strict sub-Gaussianity, and Marchal and Arbel \\cite{MarchalArbel} use differential equations for Beta and Dirichlet proxies. Atouani, Marchal, and Arbel \\cite[Theorem 3.2 and Corollary 3.3]{AtouaniMarchalArbel} give the three-mass proxy formula specialized in Section \\ref{sec:twodraw}. That section applies their formula to two draws and evaluates the resulting success-count extremum and singleton comparison. The all-degree variance certificates, the parity-uniform Laplace envelope, the classification of odd-population extremizers, and the optimized expansions for each fixed sample size are the hypergeometric results developed here. The fourth-order local moment expansion in \\cite[Remark 3.6]{AtouaniMarchalArbel} is in the Laplace argument; our expansion is in $N^{-1}$ at the globally optimizing argument, and is accompanied by an extremum theorem over all success counts.","Kou and Ying \\cite{Kou} connect fixed-margin laws with Jacobi polynomials and sums of independent Bernoulli variables; Borcea, Br\\\"and\\'en, and Liggett \\cite{BBL} develop the broader stability framework. The Jacobi identities and zero-location theorem are classical \\cite[Chapter IV and Section 6.7]{Szego}. Arbel, Marchal, and Nguyen \\cite{ArbelMarchalNguyen} study optimal variance proxies and strict sub-Gaussianity, and Marchal and Arbel \\cite{MarchalArbel} use differential equations for Beta and Dirichlet proxies. Atouani, Marchal, and Arbel \\cite[Theorem 3.2 and Corollary 3.3]{AtouaniMarchalArbel} give the three-mass proxy formula specialized in Section \\ref{sec:twodraw}. Section \\ref{sec:twodraw} applies the Atouani--Marchal--Arbel formula to two draws and evaluates the resulting success-count extremum and singleton comparison. The all-degree variance certificates, the parity-uniform Laplace envelope, the classification of odd-population extremizers, and the optimized expansions for each fixed sample size are the hypergeometric results developed here. The fourth-order local moment expansion in \\cite[Remark 3.6]{AtouaniMarchalArbel} is in the Laplace argument; our expansion is in $N^{-1}$ at the globally optimizing argument, and is accompanied by an extremum theorem over all success counts."],
        ["The two-level exchangeability reduction leads to the curvature theorem, parity-dependent sharp constants, and quadratic Laplace envelope. The subsequent fixed-sample extremizer theorem and piecewise KL bounds develop their finite-sample consequences. Fourth-order asymptotics and supporting algebraic calculations appear in the appendices.","The two-level exchangeability reduction leads to the curvature theorem, parity-dependent sharp constants, and quadratic Laplace envelope. The fixed-sample extremizer theorem sharpens the success-count proxy maximization, and the piecewise KL theorem converts the tilted-variance envelopes into finite-sample tail rates. Fourth-order asymptotics and supporting algebraic calculations appear in the appendices."],
        ["The second derivative is the variance of $H$ under the probability law having Radon--Nikodym derivative proportional to $e^{tH}$. The centering has no effect on this second derivative. Define $\\sigma^2_{\\mathrm{opt}}(H)=\\sup_{t\\ne0}2\\psi_{N,k,m}(t)/t^2$. The quotient $2\\psi_{N,k,m}(t)/t^2$ is assigned its continuous value $\\Var(H)$ at $t=0$.","The second derivative is the variance of $H$ under the probability law having Radon--Nikodym derivative proportional to $e^{tH}$. Subtracting the hypergeometric mean from $H$ leaves the tilted variance unchanged. Define $\\sigma^2_{\\mathrm{opt}}(H)=\\sup_{t\\ne0}2\\psi_{N,k,m}(t)/t^2$. The quotient $2\\psi_{N,k,m}(t)/t^2$ is assigned its continuous value $\\Var(H)$ at $t=0$."],
        ["while for $N$ even and $k=N/2$ equality holds in the optimal-proxy comparison. The same proxy comparison and its equality classification hold for $m=2$ and $2\\le k\\le\\lfloor N/2\\rfloor$, $N\\ge5$.","while for $N$ even and $k=N/2$ equality holds in the optimal-proxy comparison. The scaled-Bernoulli optimal-proxy comparison and its equality classification hold for $m=2$ and $2\\le k\\le\\lfloor N/2\\rfloor$, $N\\ge5$."],
        ["The bound is sharp over the indicated parameter family. Equality occurs for a singleton marked margin after a suitable exponential tilt, and at zero tilt when both margin products are maximal and $N$ is even.","The curvature bound \\eqref{eq:curvature} is sharp over the indicated parameter family. Equality occurs for a singleton marked margin after a suitable exponential tilt, and at zero tilt when both margin products are maximal and $N$ is even."],
        ["Compactness gives a maximizer. The claims for $\\rho=0$ and $N=2$ are immediate. Suppose that a maximizer has three distinct coordinates $x_1,x_2,x_3$. Fix all other coordinates $R$ and set $s=x_1+x_2+x_3$, $q=x_1^2+x_2^2+x_3^2$. On the circle defined by these two constraints, the part of the objective depending on the triple is","Compactness gives a maximizer. When $\\rho=0$, the feasible set consists only of the zero vector; when $N=2$, every coefficient vector has at most two coordinate values. Suppose that a maximizer has three distinct coordinates $x_1,x_2,x_3$. Fix all other coordinates $R$ and set $s=x_1+x_2+x_3$, $q=x_1^2+x_2^2+x_3^2$. On the circle defined by these two constraints, the part of the objective depending on the triple is"],
        ["It satisfies $H(x_i)=h(x_i)=0$ and $H'(x_i)=h'(x_i)$. Repeated Rolle's theorem applied to these three double zeros gives a point $\\xi$ between the smallest and largest $x_i$ such that","The Hermite interpolant $H$ satisfies $H(x_i)=h(x_i)=0$ and $H'(x_i)=h'(x_i)$. Repeated Rolle's theorem applied to these three double zeros gives a point $\\xi$ between the smallest and largest $x_i$ such that"],
        ["This contradicts \\eqref{eq:twolevel_second}.","The positive sign forced by the Hermite interpolation remainder contradicts the nonpositivity required by \\eqref{eq:twolevel_second}."],
        ["For $a\\perp\\one$, average $\\exp(\\lambda\\langle a,x\\rangle)$ over coordinate permutations and denote the resulting convex function on $[-1,1]^N$ by $\\Phi(x)$. Exchangeability gives $\\E e^{\\lambda\\langle a,X\\rangle}=\\E\\Phi(X)$. Convexity bounds this by the largest value at a cube vertex. A vertex with $k$ positive coordinates, uniformly permuted, is the $k$th Hamming slice. If $S_k$ is a uniform $k$-subset and $y_i=2\\lambda a_i$, its log-MGF is","For $a\\perp\\one$, average $\\exp(\\lambda\\langle a,x\\rangle)$ over coordinate permutations and denote the resulting convex function on $[-1,1]^N$ by $\\Phi(x)$. Exchangeability gives $\\E e^{\\lambda\\langle a,X\\rangle}=\\E\\Phi(X)$. Convexity bounds $\\E\\Phi(X)$ by the largest value of $\\Phi$ at a cube vertex. Uniformly permuting a vertex with $k$ positive coordinates produces the uniform law on the $k$th Hamming slice. If $S_k$ is a uniform $k$-subset and $y_i=2\\lambda a_i$, the log-MGF of the random subset sum $\\sum_{i\\in S_k}y_i$ is"],
        ["For $\\lambda a\\ne0$, Proposition \\ref{prop:two_level} bounds this objective by that of a vector of the same norm with values $(N-m)t/N$ on $m$ coordinates and $-mt/N$ on the others. Its slice sum and squared norm are","For $\\lambda a\\ne0$, Proposition \\ref{prop:two_level} bounds $F_{N,k}(y)$ by its value at a vector of the same norm with values $(N-m)t/N$ on $m$ coordinates and $-mt/N$ on the others. Its slice sum and squared norm are"],
        ["Theorem \\ref{odd:thm:odd} supplies the exact odd value. Together with the sharp examples below, these results prove Theorem \\ref{thm:exchange}. Substituting the projected, zero-padded weights into \\eqref{eq:exchange-intro} proves Corollary \\ref{cor:tail}; its tail bound follows by minimizing the Chernoff exponent.","Theorem \\ref{odd:thm:odd} supplies the exact odd value. The curvature upper bound, the odd-population theorem, and the sharp examples together prove Theorem \\ref{thm:exchange}. Substituting the projected, zero-padded weights into \\eqref{eq:exchange-intro} proves Corollary \\ref{cor:tail}; the probability bound in that corollary follows by optimizing the Chernoff exponent."],
        ["For exponential-tilt variances, reflection $H\\mapsto c-H$ simply replaces $t$ by $-t$. Both $k(N-k)$ and $m(N-m)$ remain invariant under their respective complementation, while the minimum of these products is invariant under exchanging $k$ and $m$. Therefore it suffices to prove the curvature theorem under the normalization","For exponential-tilt variances, reflection $H\\mapsto c-H$ simply replaces $t$ by $-t$. Both $k(N-k)$ and $m(N-m)$ remain invariant under their respective complementation, while the minimum of these products is invariant under exchanging $k$ and $m$. The four complement and transposition symmetries thus reduce the curvature theorem to the normalization"],
        ["Real-rootedness gives the mean--variance constraint \\eqref{eq:PB}. At a stationary tilt, the pair $(u,v)$ belongs to the intersection of this region and the algebraic curve derived below.","Real-rootedness gives the mean--variance constraint \\eqref{eq:PB}. At a stationary tilt, the pair $(u,v)$ belongs to the intersection of the admissible region $0<v\\le u(j-u)/j$ and the algebraic curve derived below."],
        ["This eliminates the exponential tilt exactly.","Eliminating $z$ between \\eqref{eq:riccati} and \\eqref{eq:zfromuv} yields the stationary relation $\\mathcal F(u,v)=0$."],
        ["Consequently it has exactly one positive real zero, denoted $v_+(u)$. At any stationary point of the actual tilted variance, $v=v_+(u)$. Moreover, for any $B>0$, if $\\mathcal F(u,B)\\le0$ then $v_+(u)\\le B$.","Consequently the polynomial $v\\mapsto\\mathcal F(u,v)$ has exactly one positive real zero, denoted $v_+(u)$. At any stationary point of the actual tilted variance, $v=v_+(u)$. Moreover, for any $B>0$, if $\\mathcal F(u,B)\\le0$ then $v_+(u)\\le B$."],
        ["Collecting powers of $v$ in \\eqref{eq:F} gives the asserted leading coefficient and constant term. Since $\\mathcal F(u,0)>0$ and its leading coefficient is negative, the two real roots have opposite signs. The positive root is unique. The polynomial is positive strictly between its two roots and negative to the right of the positive root, proving the last assertion.","Collecting powers of $v$ in \\eqref{eq:F} gives the asserted leading coefficient and constant term. Since $\\mathcal F(u,0)>0$ and its leading coefficient is negative, the two real roots have opposite signs. The positive root is unique. The polynomial is positive strictly between its two roots and negative to the right of the positive root, proving that $\\mathcal F(u,B)\\le0$ implies $v_+(u)\\le B$."],
        ["If $xD\\ge0$, then each of the two terms in \\eqref{eq:masterpositive} is nonnegative. We may therefore assume $xD<0$. Write $q=|x|>0$ and $d=|D|\\in(0,S]$. The expression to be bounded becomes","If $xD\\ge0$, then each of the two terms in \\eqref{eq:masterpositive} is nonnegative. We may therefore assume $xD<0$. Write $q=|x|>0$ and $d=|D|\\in(0,S]$. The polynomial on the left of \\eqref{eq:masterpositive} becomes"],
        ["Since $A=j^2(j-1)-Tq^2$, this assumption implies","Since $A=j^2(j-1)-Tq^2$, the Case II assumption $A<j^2/L$ implies"],
        ["Both sides are nonnegative, since $E\\ge0$. Squaring \\eqref{eq:Eq} and using the definition of $q_0$ shows that it is equivalent to","Both sides are nonnegative, since $E\\ge0$. Squaring \\eqref{eq:Eq} and using the definition of $q_0$ shows that inequality \\eqref{eq:Eq} is equivalent to"],
        ["The expression in \\eqref{eq:Kpositive} is a polynomial in $a=j-3$ and $S$ with nonnegative coefficients. Its six powers of $S$ establish the comparison on the entire quadrant $a,S\\ge0$.","The expression in \\eqref{eq:Kpositive} is a polynomial in $a=j-3$ and $S$ with nonnegative coefficients. Its six coefficients, for powers $S^0$ through $S^5$, establish the comparison throughout the quadrant $a,S\\ge0$."],
        ["Insert $m=j+h$ and $N=2j+h+r$ into \\eqref{eq:F}, substitute $u=(j+x)/2$ and $v=j(N-j)/(4(N-1))$, and multiply by $16(N-1)$. Group the resulting polynomial by powers of $D=h-r$. Its coefficient of $D^2$ is $-A$ before changing the overall sign; the coefficient of $D$ is $2x(A-j(L+1))$; and the $D$-free part is $-Ax^2-(L+1)Ex^2$. These three coefficients coincide with expansion of the right side after the overall sign. The coefficient form is recorded in Appendix \\ref{app:algebra}.","Insert $m=j+h$ and $N=2j+h+r$ into \\eqref{eq:F}, substitute $u=(j+x)/2$ and $v=j(N-j)/(4(N-1))$, and multiply by $16(N-1)$. Group the resulting polynomial by powers of $D=h-r$. The coefficient of $D^2$ in the expanded polynomial is $-A$ before changing the overall sign; the coefficient of $D$ is $2x(A-j(L+1))$; and the $D$-free part is $-Ax^2-(L+1)Ex^2$. These three coefficients coincide with expansion of the right side after the overall sign. The coefficient form is recorded in Appendix \\ref{app:algebra}."],
        ["On the other hand $w(t_*)=0$, so the stationary elimination in \\eqref{eq:F} shows $\\mathcal F(u_*,v_*)=0$. Lemma \\ref{lem:branch} states that this zero is the unique positive root of the concave quadratic and that $\\mathcal F(u_*,B)\\le0$ forces $v_*\\le B$, a contradiction. Hence $\\sup_t v(t)\\le B$.","On the other hand $w(t_*)=0$, so the stationary elimination in \\eqref{eq:F} shows $\\mathcal F(u_*,v_*)=0$. Lemma \\ref{lem:branch} states that $v_*$ is the unique positive root of the concave quadratic $v\\mapsto\\mathcal F(u_*,v)$ and that $\\mathcal F(u_*,B)\\le0$ forces $v_*\\le B$, a contradiction. Hence $\\sup_t v(t)\\le B$."],
        ["hold. The upper bound follows by multiplying $m/(m-1)\\le2$ and $(N-m)/(N-m-1)\\le2$. For the lower bound, observe that","hold. The inequality $\\rho\\le2$ follows by multiplying $m/(m-1)\\le2$ and $(N-m)/(N-m-1)\\le2$. For the lower bound, observe that"],
        ["This is the desired symmetric curvature envelope for $j=2$. The cases with another margin equal to one were handled in the preceding subsection.","Thus $\\sup_t\\Var_t(H)\\le j(N-j)/[4(N-1)]$ for the two-mark layer $j=2$. The cases with another margin equal to one were handled in the preceding subsection."],
        ["For even $N$, \\eqref{eq:globalC} and the variance lower bound prove equality. For odd $N$, use the value established in Theorem \\ref{odd:thm:odd}:","For even $N$, \\eqref{eq:globalC} and the variance lower bound give $C_N^\\star=D_N$. For odd $N$, use the value established in Theorem \\ref{odd:thm:odd}:"],
        ["For two draws with $2\\le k\\le N-2$, the hypergeometric law has three support points. The optimal-proxy formula is the specialization of Atouani, Marchal, and Arbel \\cite[Theorem 3.2 and Corollary 3.3]{AtouaniMarchalArbel} under a shift of the support. We give its calculus proof and then optimize the resulting expression over the hypergeometric success count.","For two draws with $2\\le k\\le N-2$, the hypergeometric law has three support points. The optimal-proxy formula is the specialization of Atouani, Marchal, and Arbel \\cite[Theorem 3.2 and Corollary 3.3]{AtouaniMarchalArbel} under a shift of the support. We derive the three-mass optimal-proxy formula by calculus and then optimize it over the hypergeometric success count."],
        ["After substituting $x=t-a$ and centering $X$, this gives the optimal quadratic bound with equality at $t=2a$. When $a=0$, the same derivative argument gives the optimal coefficient $f''(0)=2p_0$, equal to the continuous limit of \\eqref{eq:threeproxy}.","After substituting $x=t-a$ and centering $X$, the integrated inequality gives the optimal quadratic bound with equality at $t=2a$. When $a=0$, the same derivative argument gives the optimal coefficient $f''(0)=2p_0$, equal to the continuous limit of \\eqref{eq:threeproxy}."],
        ["As $\\operatorname{artanh}(x/b)/x$ is strictly increasing for $0<x<b$, the normalized proxy is largest when $x=1$. The endpoint laws $k=1,N-1$ are Bernoulli; Hoeffding's lemma bounds their normalized contributions by $N/[2(N-2)]<1$, whereas the central two-draw contribution exceeds one. This proves \\eqref{eq:Ltwo}.","As $\\operatorname{artanh}(x/b)/x$ is strictly increasing for $0<x<b$, the normalized proxy is largest when $x=1$. The endpoint laws $k=1,N-1$ are Bernoulli; Hoeffding's lemma bounds their normalized optimal-proxy values by $N/[2(N-2)]<1$, whereas the central two-draw contribution exceeds one. This proves \\eqref{eq:Ltwo}."],
        ["This is equivalent to $L_N^{(2)}<L_N$. The asymptotic difference follows by expanding $\\operatorname{artanh}x=x+x^3/3+x^5/5+O(x^7)$ in both exact formulas.","The resulting integral inequality is equivalent to $L_N^{(2)}<L_N$. The asymptotic difference follows by expanding $\\operatorname{artanh}x=x+x^3/3+x^5/5+O(x^7)$ in both exact formulas."],
        ["All these estimates are finite-population statements.",""],
        ["The envelope depends quadratically on the tilted mean.","The polynomial $P(u)$ is quadratic in the tilted mean $u$."],
        ["At a noncentral contact $V=P$, the sign of the residual is determined by $W$.","At a noncentral contact $V=P$, the sign of the residual $\\mathcal F(u,P(u))$ is determined by $W(d,z_0)$."],
        ["The coefficient identities establish strict positivity for every allowed $N,m$.","The displayed coefficient identities establish $W(d,z_0)>0$ throughout the admissible region for every allowed $N,m$."],
        ["At the two endpoints the envelope is positive. Explicitly,","The quadratic polynomial $P$ satisfies $P(0)>0$ and $P(m)>0$. Explicitly,"],
        ["At this zero, \\eqref{odd:eq:E} and \\eqref{odd:eq:PB} imply $E\\ge0$, so","At each noncentral zero $u$ of $f(u)=V(u)-P(u)$, \\eqref{odd:eq:E} and \\eqref{odd:eq:PB} imply $E\\ge0$, so"],
        ["To optimize the comparison, extend the hypergeometric quotient continuously to zero. It tends to zero at either infinity, so its maximum is attained at a finite point. At every nonzero tilt it is strictly below the Bernoulli upper envelope. If $d>0$, its value at zero is $Mpq$, strictly below $M\\sigma^2_{\\rm opt}(\\Bern(p))=Md/(4\\artanh d)$, because","To optimize the comparison, define the proxy quotient $Q(t)=2\\psi(t)/t^2$ for $t\\ne0$ and $Q(0)=\\Var(H)$. The quotient $Q(t)$ tends to zero at either infinity, so its maximum is attained at a finite point. At every nonzero tilt $t$, the quotient $Q(t)$ is strictly below the scaled Bernoulli proxy quotient at the same tilt. If $d>0$, its value at zero is $Mpq$, strictly below $M\\sigma^2_{\\rm opt}(\\Bern(p))=Md/(4\\artanh d)$, because"],
        ["Thus the proxy comparison is strict for $k<N/2$. If $d=0$, the integrated Laplace bound and $\\log\\cosh x\\le x^2/2$ give $\\sigma^2_{\\rm opt}(H)\\le M/4$. The variance at zero tilt is $Mpq=M/4$, so equality holds in the optimal-proxy comparison. Finally, $g(d)$ strictly decreases for $d>0$ by the same integral inequality. In the odd case $d\\ge1/N$, and hence $g(d)\\le g(1/N)$. This completes Theorem~\\ref{odd:thm:envelope} for both parities.","Thus the proxy comparison is strict for $k<N/2$. If $d=0$, the integrated Laplace bound and $\\log\\cosh x\\le x^2/2$ give $\\sigma^2_{\\rm opt}(H)\\le M/4$. The variance at zero tilt is $Mpq=M/4$, so equality holds in the optimal-proxy comparison. Finally, $g(d)$ strictly decreases for $d>0$ because $\\operatorname{artanh}(d)/d=\\int_0^1(1-d^2s^2)^{-1}\\,ds$ increases strictly for $d\\in(0,1)$. In the odd case $d\\ge1/N$, and hence $g(d)\\le g(1/N)$. This completes Theorem~\\ref{odd:thm:envelope} for both parities."],
        ["Complementation of either margin replaces the centered variable by its negative. It leaves the optimal proxy unchanged, and sample complementation preserves $m(N-m)$. Reduce first to $1\\le k,m\\le(N-1)/2$.","Complementation of either margin replaces the centered variable by its negative. Each margin-complement transformation preserves the optimal proxy, and sample complementation also preserves $m(N-m)$. Reduce first to $1\\le k,m\\le(N-1)/2$."],
        ["Applying \\eqref{eq:LKidentity} proves the odd formula in Theorem \\ref{thm:exchange}. The comparison is finite-population and covers every sample size, including sequences with $m_N\\to\\infty$, whether $m_N=o(N)$ or $m_N/N$ stays bounded away from zero.","Applying \\eqref{eq:LKidentity} proves the odd formula in Theorem \\ref{thm:exchange}. The bound holds for every finite $N$ and every $1\\le m<N$, including sequences with $m_N\\to\\infty$, whether $m_N=o(N)$ or $m_N/N$ stays bounded away from zero."],
        ["For a sample of fixed size $m$, the hypergeometric variance is maximized at the central success counts. Skewed bounded laws can have optimal centered sub-Gaussian proxies strictly larger than their variances \\cite{ArbelMarchalNguyen}. We prove that central success counts also maximize the optimal proxy for every finite population size and quantify the deficit at every noncentral margin. The proof combines the curvature bound and scaled Bernoulli comparison established above.","For a sample of fixed size $m$, the hypergeometric variance is maximized at the central success counts. Skewed bounded laws can have optimal centered sub-Gaussian proxies strictly larger than their variances \\cite{ArbelMarchalNguyen}. We prove that central success counts also maximize the optimal proxy for every finite population size and quantify the deficit at every noncentral margin. The proof combines Theorem \\ref{thm:curvature} with the scaled-Bernoulli comparison in Theorem \\ref{odd:thm:envelope} and Corollary \\ref{cor:two_bern_envelope}."],
        ["for $m\\ge2$ is strict. Success complementation $k\\mapsto N-k$","for $m\\ge2$ and $k<N/2$ is strict. Success complementation $k\\mapsto N-k$"],
        ["The difference on the left vanishes at zero and has derivative","The difference between the two sides of the first inequality vanishes at zero and has derivative"],
        ["The second inequality follows by taking reciprocals of positive quantities.","The upper bound for $d/[4\\operatorname{artanh}(d)]$ follows by taking reciprocals of the positive sides of the first inequality."],
        ["If $N$ is even, offcenter $\\bar k\\le N/2-1$ entails","If $N$ is even, off-center $\\bar k\\le N/2-1$ entails"],
        ["The exact difference","The exact difference between the two margin products"],
        ["Indeed, the final quantity is smaller than $1/[8(N-1)]$.","Indeed, the gap threshold $\\Delta_{N,m}$ is smaller than $1/[8(N-1)]$."],
        ["The explicit bound","The explicit deficit certificate"],
        ["Each branch is exactly the upper proxy used in","Each branch of $G_{N,m}(k)$ equals $W_{N,m}$ minus the corresponding upper bound for $S_{N,m}(k)$ used in"],
        ["The all-tilt ceiling \\eqref{B:C} at this $k$ yields","The all-tilt ceiling \\eqref{B:C} at $k=N/2$ yields"],
        ["so a finite maximizer exists; strictness ensures it is nonzero.","so a finite maximizer exists; the strict increase above the zero-tilt proxy for small positive $t$ ensures that the maximizer is nonzero."],
        ["The two hypergeometric tilted-variance envelopes yield an explicit piecewise relative-entropy rate for both tails.","The hypergeometric tilted-variance bounds $V(u)\\le B(u)$ and $V(u)\\le P(u)$ yield an explicit piecewise relative-entropy rate for both tails."],
        ["The first follows from the classical Jacobi real-root representation as a","The Poisson--binomial representation proves $V\\le B$ by expressing the tilted hypergeometric law as a"],
        ["sum of independent Bernoulli variables; the second is its quadratic","sum of independent Bernoulli variables; Theorem \\ref{odd:thm:envelope} supplies the quadratic"],
        ["at $u=\\mu$. In particular, $P(\\mu)=Mpq>0$, and the endpoint calculations in","at $u=\\mu$. In particular, $P(\\mu)=Mpq>0$, and the endpoint evaluations in"],
        ["explicit endpoint evaluations give $P(0)>0$ and $P(m)>0$. Concavity implies $P>0$ on $[0,m]$.","the proof of Lemma \\ref{odd:lem:barrier} show $P(0)>0$ and $P(m)>0$. Concavity implies $P>0$ on $[0,m]$."],
        ["For $v\\in(l,h)$, differentiation of its Legendre transform gives","For $v\\in(l,h)$, differentiation of the Legendre transform $I$ of $\\log\\E e^{tX}$ gives"],
        ["of $Q$. Their kernels are nonnegative on the respective integration","of $Q$. The integral kernels $(v-u)$ and $(u-v)$ are nonnegative on the respective integration"],
        ["This is the ordinary Bernoulli Chernoff transform. At $\\theta=0$ or $1$, the Bernoulli transform is defined by the limits $t\\to\\mp\\infty$. The relative entropy $D(\\theta\\Vert p)$ has domain $0\\le\\theta\\le1$.","The explicit optimizer is the standard Bernoulli Chernoff optimizer for the scaled envelope. At $\\theta=0$ or $1$, the Bernoulli transform is defined by the limits $t\\to\\mp\\infty$. The relative entropy $D(\\theta\\Vert p)$ has domain $0\\le\\theta\\le1$."],
        ["It gives valid upper and lower tail bounds as in Theorem~\\ref{A:integration}.","The piecewise rate $J$ gives valid upper and lower tail bounds as in Theorem~\\ref{A:integration}."],
        ["On every noncentral path the interval near $\\mu$ has $P<B$, proving","For every $v\\ne\\mu$, the integration interval between $\\mu$ and $v$ contains points near $\\mu$ where $P<B$, proving"],
        ["proving the characterization of $J>I_P$. Finally, $V<P$ except at $\\mu$,","proving the characterization of $J>I_P$. Finally, $V(u)<P(u)$ for every $u\\ne\\mu$,"],
        ["so the central interval gives $I>J$ on every noncentral path.","so the positive-length central portion of each nontrivial integration interval gives $I(v)>J(v)$."],
        ["Use $e^{-J(z_+)}$ for the upper event when $z_+\\le m$, and zero otherwise;","If $z_+\\le m$, then $\\Pr(H-\\mu\\ge x)=\\Pr(H\\ge z_+)\\le e^{-J(z_+)}$; if $z_+>m$, this probability is zero."],
        ["use $e^{-J(z_-)}$ for the lower event when $z_-\\ge0$, and zero otherwise.","Likewise, if $z_-\\ge0$, then $\\Pr(H-\\mu\\le -x)=\\Pr(H\\le z_-)\\le e^{-J(z_-)}$; if $z_-<0$, this probability is zero."],
        ["Their sum, capped at one, bounds $\\Pr(|H-\\mu|\\ge x)$.","The sum of the two one-sided bounds, capped at one, bounds $\\Pr(|H-\\mu|\\ge x)$."],
        ["Therefore $R_1=I_B\\ge R_j$ for $j=2,3,4$ on $[0,m]$, and","Therefore $\\max_{1\\le j\\le4}R_j=R_1=I_B$ on $[0,m]$, and"],
        ["Theorem~\\ref{A:piecewise} strictly improves their maximum at every","Theorem~\\ref{A:piecewise} gives $J(v)>\\max_{1\\le j\\le4}R_j(v)$ at every"],
        ["by Mannalath, Zapatero and Curty~\\cite{A:MZC}; the improvement here comes","by Mannalath, Zapatero and Curty~\\cite{A:MZC}; the strict improvement $J>I_B$ comes"],
        ["The exact uniform exchangeability constant in Theorem~\\ref{thm:exchange} gives this coefficient for $H-\\mu$, with","The exact uniform exchangeability constant in Theorem~\\ref{thm:exchange} gives the variance coefficient $V_*$ for $H-\\mu$, with"],
        ["Both KL rates therefore improve the displayed uniform quadratic bound. The optimized quadratic proxy of an individual hypergeometric law may yield a stronger bound.","Both $J(v)$ and $I_P(v)$ therefore dominate the displayed uniform quadratic rate $(v-\\mu)^2/(2V_*)$. The optimized quadratic proxy of an individual hypergeometric law may yield a stronger bound."],
        ["The inequality $J\\ge I_P$ is an equality precisely in the central region.","Equality $J(v)=I_P(v)$ holds precisely for $v\\in[r_-,r_+]$."],
        ["This shows the directional asymmetry and the variance-scale improvement","The cubic term in the expansion of $I_P$ determines the directional asymmetry, while the quadratic term shows the variance-scale improvement"],
        ["can be smaller than $I_B$ in the tails. Theorem~\\ref{A:piecewise} removes","can be smaller than $I_B$ in the tails. The piecewise rate $J$ in Theorem~\\ref{A:piecewise} removes"],
        ["this loss relative to the four binomial bounds.","the tail-region deficit of the unspliced $I_P$ relative to the four binomial bounds."],
        ["$x^2/[2(v_0+x/3)]$. For either tail, the scaled rate is strictly larger","$x^2/[2(v_0+x/3)]$. For either tail sign and every supported deviation $s>0$, the quadratic-envelope rate $I_P(\\mu\\pm s)$ is strictly larger"],
        ["than the Bennett exponent at every nonzero supported deviation.","than the Bennett exponent $v_0h_0(s/v_0)$; the piecewise rate $J(\\mu\\pm s)$ inherits this strict comparison."],
        ["Both rates and their first derivatives vanish at zero. Integrating the","For each tail sign, the functions $s\\mapsto I_P(\\mu\\pm s)$ and $s\\mapsto v_0h_0(s/v_0)$ and their first derivatives vanish at $s=0$. Integrating the"],
        ["strict comparison twice, and then using $J\\ge I_P$, proves the assertion.","strict second-derivative comparison twice proves $I_P(\\mu\\pm s)>v_0h_0(s/v_0)$, and $J\\ge I_P$ transfers the bound to $J$."],
        ["The standard inequality $h_0(z)\\ge z^2/[2(1+z/3)]$ gives the Bernstein","The standard inequality $h_0(z)\\ge z^2/[2(1+z/3)]$ consequently gives the Bernstein"],
        ["comparison as well. ","comparison $J(\\mu\\pm s)>s^2/[2(v_0+s/3)]$ for every nonzero supported $s$. "],
        ["For $\\mu<d\\le\\min(k,m)$, a valid minimizing index is","For $\\mu<d\\le\\min(k,m)$, a minimizing index for the factorial-moment ratio defining $F_d$ is"],
        ["$j\\le(Nd-km)/(N+d-k-m)$. When this fraction is integral, the two adjacent","$j\\le(Nd-km)/(N+d-k-m)$. When $(Nd-km)/(N+d-k-m)$ is an integer, the two adjacent"],
        ["The strict singleton comparison of Theorem \\ref{odd:thm:odd} has a small gap for nearly balanced populations. This section determines that gap through fourth order and the location of the globally maximizing tilt through third order, for every fixed sample size and fixed success imbalance. The cases $m=1$ and $m=2$ agree with the Bernoulli formula \\eqref{eq:bernproxy} and the three-point specialization in Section \\ref{sec:twodraw}. The theorem gives the expansion for arbitrary fixed $m$, together with uniqueness of the global optimizer and analytic remainders.","For fixed $m\\ge2$ and nearly balanced odd populations, the strict singleton comparison in Theorem \\ref{odd:thm:odd} has a gap $L_N-R_{N,1,m}$ of order $N^{-3}$. This section expands $L_N-R_{N,s,m}$ through fourth order and locates the globally maximizing tilt through third order, for every fixed sample size and fixed success imbalance. The cases $m=1$ and $m=2$ agree with the Bernoulli formula \\eqref{eq:bernproxy} and the three-point specialization in Section \\ref{sec:twodraw}. Theorem \\ref{thm:odd_expansion} gives the expansion for arbitrary fixed $m$, together with uniqueness of the global optimizer and analytic remainders."],
        ["For every fixed $m,s$, the finite probability generating polynomial depends analytically on $(t,\\varepsilon)$ near $(0,0)$, and its value at $(0,0)$ is one. Consequently $Q_\\varepsilon$ is jointly real analytic in a neighborhood of $(0,0)$. At $\\varepsilon=0$,","For every fixed $m,s$, the finite probability generating polynomial is analytic in $(t,\\varepsilon)$ near $(0,0)$ and equals one at $(t,\\varepsilon)=(0,0)$. Consequently $Q_\\varepsilon$ is jointly real analytic in a neighborhood of $(0,0)$. At $\\varepsilon=0$,"],
        ["Furthermore, $|H_N-\\E H_N|\\le m$ implies $0\\le Q_\\varepsilon(t)\\le2m/|t|$ for $t\\ne0$, uniformly in the admissible populations. On every compact interval, $Q_\\varepsilon$ converges uniformly to $Q_0$, including at zero by analytic continuation. Combining this compact convergence with the uniform tail bound shows that every global maximizer of $Q_\\varepsilon$ tends to zero as $\\varepsilon\\downarrow0$.","Furthermore, $|H_N-\\E H_N|\\le m$ implies $0\\le Q_\\varepsilon(t)\\le2m/|t|$ for $t\\ne0$, uniformly in the admissible populations. On every compact interval, $Q_\\varepsilon$ converges uniformly to $Q_0$, including at zero by analytic continuation. Combining this compact convergence with the estimate $Q_\\varepsilon(t)\\le2m/|t|$ shows that every global maximizer of $Q_\\varepsilon$ tends to zero as $\\varepsilon\\downarrow0$."],
        ["Thus $Q_\\varepsilon$ is strictly concave on some fixed neighborhood of zero for all sufficiently small $\\varepsilon$. The derivative at zero is $\\kappa_3(\\varepsilon)/3>0$ for $\\varepsilon>0$ small. By the analytic implicit-function theorem, there exists a unique critical point $t(\\varepsilon)$ in that neighborhood; it is analytic in $\\varepsilon$, and the localization argument establishes that it is the unique global maximizer. Differentiation of the critical point equation at zero gives","Thus $Q_\\varepsilon$ is strictly concave on some fixed neighborhood of zero for all sufficiently small $\\varepsilon$. The derivative at zero is $\\kappa_3(\\varepsilon)/3>0$ for $\\varepsilon>0$ small. By the analytic implicit-function theorem, there exists a unique critical point $t(\\varepsilon)$ in that neighborhood; it is analytic in $\\varepsilon$, and the compact-convergence and uniform-tail localization shows that this critical point is the unique global maximizer. Differentiation of the critical point equation at zero gives"],
        ["The terms omitted from the derivative contribute $O_{m,s}(e^4)$ because the cumulants are analytic and $t=O(e)$. This establishes the full tilt expansion in \\eqref{eq:tiltexp}.","The higher-order cumulant terms omitted from the displayed derivative expansion contribute $O_{m,s}(e^4)$ because the cumulants are analytic and $t=O(e)$. This establishes the full tilt expansion in \\eqref{eq:tiltexp}."],
        ["Multiplying by $4/[m(1-me)]$ proves the fourth-order proxy expansion \\eqref{eq:Rexp}. The analytic global optimizer supplies the Taylor remainder for each fixed $m,s$.","Multiplying by $4/[m(1-me)]$ proves the fourth-order proxy expansion \\eqref{eq:Rexp}. The analytic implicit-function solution and the global-maximizer localization yield the Taylor remainder for each fixed $m,s$."],
        ["The $N^{-1}$ coefficient in \\eqref{eq:Rexp} is one. The $N^{-2}$ coefficient records the success imbalance through $-s^2/3$ and is common to all fixed sample sizes. For $s=1$, the first sample-size contribution is the order-$N^{-3}$ term $-2(m-1)/3$ relative to the singleton law. Thus \\eqref{eq:fixedgap} quantifies the separation between the optimized proxies. The maximizing tilt has leading term $4s/N$.","The $N^{-1}$ coefficient in \\eqref{eq:Rexp} is one. The $N^{-2}$ coefficient records the success imbalance through $-s^2/3$ and is common to all fixed sample sizes. For $s=1$, the coefficient of $N^{-3}$ in $L_N-R_{N,1,m}$ is $2(m-1)/3$, which quantifies the first sample-size-dependent separation from the singleton law. Thus \\eqref{eq:fixedgap} quantifies the separation between the optimized proxies. The maximizing tilt has leading term $4s/N$."],
        ["The expressions remain valid when $r>m$, with zero falling factorials. Let $\\kappa_j(\\varepsilon)$ denote the $j$th cumulant of $H_N$. Elementary simplification of the first six moments yields","The expressions remain valid when $r>m$, with zero falling factorials. Let $\\kappa_j(\\varepsilon)$ denote the $j$th cumulant of $H_N$. Applying the Stirling-number moment transformation and the cumulant recurrence below yields"],
        ["All these identities are rational in $\\varepsilon$ for fixed $m,s$ and are valid in a neighborhood of the origin. The zero-parameter limit is $H_0\\sim\\mathrm{Binomial}(m,1/2)$, for which odd cumulants vanish and $\\kappa_4(0)=-m/8$.","The displayed cumulant expansions for $\\kappa_2$ through $\\kappa_6$ are rational in $\\varepsilon$ for fixed $m,s$ and are valid in a neighborhood of the origin. The zero-parameter limit is $H_0\\sim\\mathrm{Binomial}(m,1/2)$, for which odd cumulants vanish and $\\kappa_4(0)=-m/8$."],
        ["The Bernoulli admissibility constraint restricts this root to $v_+(u)\\le u(j-u)/j$ at an actual stationary tilt.","At an actual stationary tilt, the Bernoulli admissibility constraint restricts the positive root $v_+(u)$ to $v_+(u)\\le u(j-u)/j$ at an actual stationary tilt."],
        ["The coefficient identity \\eqref{eq:Kpositive} follows by setting $a=j-3$ and $L=a+2+S$. The three factors become","The coefficient identity \\eqref{eq:Kpositive} follows by setting $a=j-3$ and $L=a+2+S$. The factors $E$, $(j-1)L-1$, and $L(L+j)$ become"],
        ["The second term on the right is strictly increasing for $t<\\alpha$ and strictly decreasing for $t>\\alpha$. Furthermore $G''(0)>0$, since with $y=\\alpha/2$,","The function $1/[4\\cosh^2((t-\\alpha)/2)]$ increases strictly for $t<\\alpha$ and decreases strictly for $t>\\alpha$. Furthermore $G''(0)>0$, since with $y=\\alpha/2$,"],
        ["(The latter inequality follows by integrating the strictly decreasing function $\\operatorname{sech}^2$ on $[0,y]$.) Thus $G''$ has one zero on $(0,\\alpha)$, is positive initially, and negative near $\\alpha$. As $G'(0)=G'(\\alpha)=0$, it follows that $G'(t)>0$ on $(0,\\alpha)$ and therefore $G(t)>0$ there. Reflection \\eqref{eq:bernref} gives $G\\ge0$ on $[\\alpha,2\\alpha]$ as well. For $t<0$ the variance term in \\eqref{eq:bernsecond} is smaller than at zero, hence $G''(t)>0$; together with $G(0)=G'(0)=0$, this yields $G(t)>0$. Reflection handles $t>2\\alpha$. Therefore $G(t)\\ge0$ for all $t$, establishing the upper bound.","(The latter inequality follows by integrating the strictly decreasing function $\\operatorname{sech}^2$ on $[0,y]$.) Thus $G''$ has one zero on $(0,\\alpha)$, is positive initially, and negative near $\\alpha$. As $G'(0)=G'(\\alpha)=0$, it follows that $G'(t)>0$ on $(0,\\alpha)$ and therefore $G(t)>0$ there. Reflection \\eqref{eq:bernref} gives $G\\ge0$ on $[\\alpha,2\\alpha]$ as well. For $t<0$ the function $1/[4\\cosh^2((t-\\alpha)/2)]$ is smaller than its value at $t=0$, hence $G''(t)>0$; together with $G(0)=G'(0)=0$, this yields $G(t)>0$. Reflection handles $t>2\\alpha$. Therefore $G(t)\\ge0$ for all $t$, establishing the upper bound."]]
    for index, (original, revised) in enumerate(replacements, 1):
        count = text.count(original)
        if count != 1:
            raise RuntimeError(f'Language-clarity anchor {index} occurred {count} times: {original[:95]!r}')
        text = text.replace(original, revised, 1)
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
    tex = polish_language_clarity(polish_integrated(tex))
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
