# I238 primary source excerpts and reading record


## Jin 2026 v2: web-rendered primary excerpt, Section 9, proof continuation

URL: https://www.preprints.org/manuscript/202609.0079/v2
Retrieval: web tool rendered lines 830–1055; raw HTTP retrieval returned 403. These lines were read in full. Theorem 3 is qualitative in each fixed dimension; its final modulus is expressly nonconstructive. This is primary text extraction, not a claimed raw HTTP copy.

```text
L830: There are ${\mathsf{\Omega }}_{n}\in \mathcal{F}$, ${A}_{n}\in {M}_{m}\left(\mathbb{C}\right)$, and rational functions ${f}_{n}$ with
L831: 
L832: $$W\left({A}_{n}\right)\subset {\mathsf{\Omega }}_{n},\phantom{\rule{2.em}{0ex}}\parallel {f}_{n}{\parallel }_{{\mathsf{\Omega }}_{n}}\le 1,\phantom{\rule{2.em}{0ex}}\parallel {f}_{n}\left({A}_{n}\right)\parallel ⟶2.$$
L833: 
L834: (41)
L835: 
L836: Discarding finitely many terms, we may assume that no ${A}_{n}$ is scalar. Fix a unit vector $e\in {\mathbb{C}}^{m}$ and define
L837: $$\begin{array}{c}{a}_{n}={e}^{*}{A}_{n}e,\phantom{\rule{2.em}{0ex}}{s}_{n}=\parallel {A}_{n}-{a}_{n}I\parallel >0,\\ {B}_{n}={\displaystyle \frac{{A}_{n}-{a}_{n}I}{{s}_{n}}},\phantom{\rule{2.em}{0ex}}{D}_{n}={\displaystyle \frac{{\mathsf{\Omega }}_{n}-{a}_{n}}{{s}_{n}}},\phantom{\rule{2.em}{0ex}}{g}_{n}\left(z\right)={f}_{n}({a}_{n}+{s}_{n}z).\end{array}$$
L838: 
L839: (42)
L840: 
L841: Since ${a}_{n}\in W\left({A}_{n}\right)$, we have $0\in {D}_{n}$. Moreover,
L842: $$\begin{array}{c}{e}^{*}{B}_{n}e=0,\phantom{\rule{2.em}{0ex}}\parallel {B}_{n}\parallel =1,\phantom{\rule{2.em}{0ex}}W\left({B}_{n}\right)\subset {D}_{n},\\ \parallel {g}_{n}{\parallel }_{{D}_{n}}\le 1,\phantom{\rule{2.em}{0ex}}\parallel {g}_{n}\left({B}_{n}\right)\parallel ⟶2.\end{array}$$
L843: 
L844: (43)
L845: 
L846: Passing to a subsequence gives
L847: 
L848: $${B}_{n}⟶B,\phantom{\rule{2.em}{0ex}}{e}^{*}Be=0,\phantom{\rule{2.em}{0ex}}\parallel B\parallel =1.$$
L849: 
L850: (44)
L851: 
L852: These two identities make B nonscalar.
L853: Step 2: Exclusion of boundary-spectrum degeneration. We claim that
L854: 
L855: $$spec\left(B\right)\subset intW\left(B\right).$$
L856: 
L857: (45)
L858: 
L859: Suppose instead that $\lambda \in spec\left(B\right)\cap \partial W\left(B\right)$. Lemma 3 makes this eigenvalue reducing and semisimple. After a fixed unitary change of basis,
L860: 
L861: $$B=\lambda {I}_{k}\oplus {B}_{0},\phantom{\rule{2.em}{0ex}}\lambda \notin spec\left({B}_{0}\right),\phantom{\rule{2.em}{0ex}}1\le k<m.$$
L862: The inequality $k<m$ follows because B is not scalar. In these fixed coordinates, write
L863: 
L864: $${B}_{n}=\left(\begin{array}{cc}{E}_{n}& {F}_{n}\\ {G}_{n}& {H}_{n}\end{array}\right)⟶\left(\begin{array}{cc}\lambda {I}_{k}& 0\\ 0& {B}_{0}\end{array}\right).$$
L865: 
L866: The graph of $\mathcal{X}:{\mathbb{C}}^{k}\to {\mathbb{C}}^{m-k}$ is invariant under ${B}_{n}$ exactly when
L867: 
L868: $${G}_{n}+{H}_{n}\mathcal{X}-\mathcal{X}{E}_{n}-\mathcal{X}{F}_{n}\mathcal{X}=0.$$
L869: At the limiting matrix and $\mathcal{X}=0$, the derivative in $\mathcal{X}$ is $\mathcal{X}\mapsto ({B}_{0}-\lambda I)\mathcal{X}$, which is invertible. The implicit-function theorem gives solutions ${\mathcal{X}}_{n}\to 0$. Interchanging the two blocks gives ${\mathcal{Y}}_{n}:{\mathbb{C}}^{m-k}\to {\mathbb{C}}^{k}$, with ${\mathcal{Y}}_{n}\to 0$, satisfying
L870: 
L871: $${F}_{n}+{E}_{n}{\mathcal{Y}}_{n}-{\mathcal{Y}}_{n}{H}_{n}-{\mathcal{Y}}_{n}{G}_{n}{\mathcal{Y}}_{n}=0.$$
L872: 
L873: Set
L874: $${P}_{n}={E}_{n}+{F}_{n}{\mathcal{X}}_{n},\phantom{\rule{2.em}{0ex}}{Q}_{n}={H}_{n}+{G}_{n}{\mathcal{Y}}_{n},\phantom{\rule{2.em}{0ex}}{S}_{n}=\left(\begin{array}{cc}I& {\mathcal{Y}}_{n}\\ {\mathcal{X}}_{n}& I\end{array}\right).$$
L875: 
L876: Then ${S}_{n}\to I$, so ${S}_{n}$ is eventually invertible, and the two graph equations give
L877: 
L878: $${B}_{n}={S}_{n}({P}_{n}\oplus {Q}_{n}){S}_{n}^{-1},\phantom{\rule{2.em}{0ex}}\parallel {S}_{n}\parallel \phantom{\rule{0.166667em}{0ex}}\parallel {S}_{n}^{-1}\parallel ⟶1.$$
L879: 
L880: (46)
L881: The graph embedding ${J}_{n}x=(x,{\mathcal{X}}_{n}x)$ satisfies
L882: 
L883: $$\parallel x\parallel \le \parallel {J}_{n}x\parallel \le (1+\parallel {\mathcal{X}}_{n}\parallel )\parallel x\parallel .$$
L884: 
L885: In orthonormal coordinates on its range, the restriction of ${B}_{n}$ has numerical range in ${D}_{n}$, so its rational calculus is bounded by $C({D}_{n},k)\le \beta $. Transporting this estimate through ${J}_{n}$, and doing the same for the other graph, gives
L886: $$\parallel {g}_{n}\left({P}_{n}\right)\parallel \le \beta (1+\parallel {\mathcal{X}}_{n}\parallel ),\phantom{\rule{2.em}{0ex}}\parallel {g}_{n}\left({Q}_{n}\right)\parallel \le \beta (1+\parallel {\mathcal{Y}}_{n}\parallel ).$$
L887: 
L888: Applying the rational calculus to (cite59†46 ), we obtain
L889: $$\parallel {g}_{n}\left({B}_{n}\right)\parallel \le \parallel {S}_{n}\parallel \phantom{\rule{0.166667em}{0ex}}\parallel {S}_{n}^{-1}\parallel \phantom{\rule{0.166667em}{0ex}}\beta max\{1+\parallel {\mathcal{X}}_{n}\parallel ,1+\parallel {\mathcal{Y}}_{n}\parallel \}=\beta +o\left(1\right).$$
L890: 
L891: This contradicts (cite60†43 ) and proves (cite61†45 ).
L892: 
L893: Step 3: Passage to a limiting domain and function. Put $K=W\left(B\right)$. The numerical-range estimate
L894: $${d}_{H}(W\left({B}_{n}\right),W\left(B\right))\le \parallel {B}_{n}-B\parallel $$
L895: 
L896: shows that $W\left({B}_{n}\right)\to K$. By (cite61†45 ), the set K has nonempty interior. Apply Lemma 11 to ${K}_{n}=\overline{{D}_{n}}$, passing to a further subsequence. The limiting closed convex set ${K}_{\infty }$ contains K, because $W\left({B}_{n}\right)\subset {K}_{n}$. Set
L897: 
L898: $$D=int{K}_{\infty }.$$
L899: Then $intK\subset D$, and every compact subset of D is eventually contained in $int{K}_{n}={D}_{n}$. Montel’s theorem on an exhaustion of D, followed by a diagonal argument, therefore gives
L900: 
L901: $${g}_{n}⟶g\phantom{\rule{1.em}{0ex}}\mathrm{locally}\phantom{\rule{4.pt}{0ex}}\mathrm{uniformly}\phantom{\rule{4.pt}{0ex}}\mathrm{on}\phantom{\rule{4.pt}{0ex}}D,\phantom{\rule{2.em}{0ex}}g\in {H}^{\infty }\left(D\right),\phantom{\rule{2.em}{0ex}}{\parallel g\parallel }_{D}\le 1.$$
L902: 
L903: (47)
L904: Choose $t>0$ so small that the compact convex body
L905: 
L906: $$\mathcal{K}=conv(spec\left(B\right))+t\overline{\mathbb{D}}$$
L907: 
L908: is contained in $intK$, and let $\mathsf{\Gamma }=\partial \mathcal{K}$, positively oriented. Its interior contains $spec\left(B\right)$, and continuity of the roots of the characteristic polynomial gives $spec\left({B}_{n}\right)\subset int\mathcal{K}$ eventually. Uniform convergence of the functions and resolvents on $\mathsf{\Gamma }$ gives
L909: $$\begin{array}{cc}\hfill {g}_{n}\left({B}_{n}\right)& ={\displaystyle \frac{1}{2\pi i}}{\int }_{\mathsf{\Gamma }}{g}_{n}\left(z\right){(zI-{B}_{n})}^{-1}\phantom{\rule{0.166667em}{0ex}}dz\hfill \\ & ⟶{\displaystyle \frac{1}{2\pi i}}{\int }_{\mathsf{\Gamma }}g\left(z\right){(zI-B)}^{-1}\phantom{\rule{0.166667em}{0ex}}dz=g\left(B\right).\hfill \end{array}$$
L910: 
L911: Consequently,
L912: 
L913: $$\parallel g\left(B\right)\parallel =2,\phantom{\rule{2.em}{0ex}}{\psi }_{intK}\left(B\right)=2,$$
L914: 
L915: (48)
L916: where the upper bound is Proposition 1.
L917: 
L918: Step 4: Strict monotonicity identifies the limiting domain. We claim that
L919: 
L920: $$D=intK.$$
L921: 
L922: (49)
L923: 
L924: Otherwise, since D is open and $K=\overline{intK}$, there is ${z}_{★}\in D\setminus K$. Choose $R>\parallel B\parallel +|{z}_{★}|$. The bounded convex domain
L925: 
L926: $${\mathsf{\Omega }}_{*}=D\cap R\mathbb{D}$$
L927: 
L928: contains ${z}_{★}$ and satisfies $intK⊊{\mathsf{\Omega }}_{*}\subset D$. Restriction of functions and (cite62†48 ) give
L929: $$2=\parallel g\left(B\right)\parallel \le {\psi }_{{\mathsf{\Omega }}_{*}}\left(B\right)\le {\psi }_{intK}\left(B\right)=2.$$
L930: 
L931: This contradicts Lemma 5, applied to the bounded convex domains $intK⊊{\mathsf{\Omega }}_{*}$. Thus (cite63†49 ) holds.
L932: 
L933: Step 5: Disk rigidity and global convergence. By (cite62†48 ) and Corollary 1,
L934: $$K=\gamma +\rho \overline{\mathbb{D}}\phantom{\rule{2.em}{0ex}}\mathrm{for}\phantom{\rule{4.pt}{0ex}}\mathrm{some}\phantom{\rule{4.pt}{0ex}}\gamma \in \mathbb{C}\phantom{\rule{4.pt}{0ex}}\mathrm{and}\phantom{\rule{4.pt}{0ex}}\rho >0.$$
L935: 
L936: A closed convex set with nonempty interior is the closure of its interior. Hence (cite63†49 ) implies
L937: 
L938: $${K}_{\infty }=\overline{D}=K.$$
L939: 
L940: Lemma 11 now shows that the sets $\overline{{D}_{n}}$ are eventually uniformly bounded and
L941: $${d}_{H}(\overline{{D}_{n}},\gamma +\rho \overline{\mathbb{D}})⟶0.$$
L942: 
L943: Set
L944: 
L945: $${c}_{n}={a}_{n}+{s}_{n}\gamma ,\phantom{\rule{2.em}{0ex}}{r}_{n}={s}_{n}\rho .$$
L946: 
L947: Then ${r}_{n}>0$, and
L948: 
L949: $${\displaystyle \frac{\overline{{\mathsf{\Omega }}_{n}}-{c}_{n}}{{r}_{n}}}={\displaystyle \frac{\overline{{D}_{n}}-\gamma }{\rho }}⟶\overline{\mathbb{D}}$$
L950: 
L951: in Hausdorff distance. Discarding the finitely many terms before boundedness holds completes the proof. □
L952: ### 9.3. Proofs of Domain Rigidity and Stability
L953: 
L954: Proof
L955: 
L956: (Proof of Theorem 2). Suppose $C(\mathsf{\Omega },d)=2$, and apply Proposition 7 to the singleton family $\mathcal{F}=\left\{\mathsf{\Omega }\right\}$. The domain $\mathsf{\Omega }$ is bounded, and there are ${c}_{n}\in \mathbb{C}$ and ${r}_{n}>0$ such that
L957: 
L958: $${\displaystyle \frac{\overline{\mathsf{\Omega }}-{c}_{n}}{{r}_{n}}}⟶\overline{\mathbb{D}}$$
L959: 
L960: in Hausdorff distance. Taking diameters gives
L961: $${\displaystyle \frac{diam\mathsf{\Omega }}{{r}_{n}}}⟶2,\phantom{\rule{2.em}{0ex}}{r}_{n}⟶r:={\displaystyle \frac{diam\mathsf{\Omega }}{2}}>0.$$
L962: 
L963: For a fixed ${z}_{0}\in \mathsf{\Omega }$, the points $({z}_{0}-{c}_{n})/{r}_{n}$ remain bounded, so the centers ${c}_{n}$ are bounded. Passing to a subsequence, let ${c}_{n}\to c$. Continuity of translation and positive scaling in Hausdorff distance then yields
L964: 
L965: $${\displaystyle \frac{\overline{\mathsf{\Omega }}-c}{r}}=\overline{\mathbb{D}}.$$
L966: Since an open convex set equals the interior of its closure, $\mathsf{\Omega }=c+r\mathbb{D}$.
L967: 
L968: Conversely, suppose $\mathsf{\Omega }=c+r\mathbb{D}$, with $r>0$. For $0<t<1$, let
L969: 
L970: $${A}_{t}=\left(\begin{array}{cc}c& 2rt\\ 0& c\end{array}\right)\oplus c{I}_{d-2},\phantom{\rule{2.em}{0ex}}p\left(z\right)={\displaystyle \frac{z-c}{r}},$$
L971: 
L972: where the final summand is omitted when $d=2$. Then
L973: $$W\left({A}_{t}\right)=c+rt\overline{\mathbb{D}}\subset {\mathsf{\Omega },\phantom{\rule{2.em}{0ex}}\parallel p\parallel }_{\mathsf{\Omega }}=1,\phantom{\rule{2.em}{0ex}}\parallel p\left({A}_{t}\right)\parallel =2t.$$
L974: 
L975: Letting $t\uparrow 1$ gives $C(\mathsf{\Omega },d)\ge 2$, and (cite58†36 ) gives equality. □
L976: 
L977: Proof
L978: (Proof of Theorem 3). Fix $d\ge 2$ and $0<\epsilon <1$. Let ${\mathcal{F}}_{\epsilon }$ be the family of proper convex domains for which there are no $c\in \mathbb{C}$ and $r>0$ satisfying (cite64†35 ). This family is nonempty, since it contains every unbounded proper convex domain.
L979: 
L980: Suppose that
L981: 
L982: $$\underset{\mathsf{\Omega }\in {\mathcal{F}}_{\epsilon }}{sup}C(\mathsf{\Omega },d)=2.$$
L983: Proposition 7 supplies bounded domains ${\mathsf{\Omega }}_{n}\in {\mathcal{F}}_{\epsilon }$, centers ${c}_{n}$, and scales ${r}_{n}>0$ such that the compact convex sets
L984: 
L985: $${L}_{n}={\displaystyle \frac{\overline{{\mathsf{\Omega }}_{n}}-{c}_{n}}{{r}_{n}}}$$
L986: 
L987: satisfy ${\eta }_{n}:={d}_{H}({L}_{n},\overline{\mathbb{D}})\to 0$. For every unit complex number $\nu $, their support functions obey
L988: 
L989: $$\left|\underset{z\in {L}_{n}}{max}Re\left(\overline{\nu }z\right)-1\right|\le {\eta }_{n}.$$
L990: The supporting-half-plane characterization of compact convex sets therefore gives, once ${\eta }_{n}<1$,
L991: 
L992: $$(1-{\eta }_{n})\overline{\mathbb{D}}\subset {L}_{n}\subset (1+{\eta }_{n})\overline{\mathbb{D}}.$$
L993: 
L994: For all sufficiently large n, ${\eta }_{n}<\epsilon $. Taking interiors for the inner inclusion and using the strict inequality of the radii for the outer inclusion yields
L995: 
L996: $${c}_{n}+(1-\epsilon ){r}_{n}\mathbb{D}\subset {\mathsf{\Omega }}_{n}\subset {c}_{n}+(1+\epsilon ){r}_{n}\mathbb{D}.$$
L997: This contradicts ${\mathsf{\Omega }}_{n}\in {\mathcal{F}}_{\epsilon }$. Consequently,
L998: 
L999: $$\delta (d,\epsilon ):=2-\underset{\mathsf{\Omega }\in {\mathcal{F}}_{\epsilon }}{sup}C(\mathsf{\Omega },d)>0.$$
L1000: 
L1001: (50)
L1002: 
L1003: With this choice, (cite65†34 ) implies $\mathsf{\Omega }\notin {\mathcal{F}}_{\epsilon }$, which is precisely (cite64†35 ). □
L1004: 
L1005: Corollary 2
L1006: 
L1007: (A uniform gap for unbounded domains). For each finite integer $d\ge 2$, there exists ${\eta }_{d}>0$ such that
L1008: 
L1009: $$C(\mathsf{\Omega },d)\le 2-{\eta }_{d}$$
L1010: 
L1011: (51)
L1012: for every unbounded proper convex domain Ω.
L1013: 
L1014: Proof.
L1015: 
L1016: Take ${\eta }_{d}=\delta (d,1/2)$ in Theorem 3. An unbounded domain cannot satisfy the bounded outer inclusion in (cite64†35 ). □
L1017: 
L1018: The following test-matrix bound is proved in [cite56†21 ].
L1019: 
L1020: Corollary 3
L1021: 
L1022: (A geometric lower bound). Let $d\ge 2$. If
L1023: 
L1024: $$c+r\mathbb{D}\subset \mathsf{\Omega }\subset c+R\mathbb{D},\phantom{\rule{2.em}{0ex}}0<r\le R<\infty ,$$
L1025: 
L1026: then
L1027: 
L1028: $$C(\mathsf{\Omega },d)\ge {\displaystyle \frac{2r}{R}}.$$
L1029: 
L1030: (52)
L1031: 
L1032: In particular, (cite64†35 ) implies
L1033: $$C(\mathsf{\Omega },d)\ge 2\phantom{\rule{0.166667em}{0ex}}{\displaystyle \frac{1-\epsilon }{1+\epsilon }}.$$
L1034: 
L1035: (53)
L1036: 
L1037: Proof.
L1038: 
L1039: For $0<t<1$, use
L1040: 
L1041: $${A}_{t}=\left(\begin{array}{cc}c& 2rt\\ 0& c\end{array}\right)\oplus c{I}_{d-2},\phantom{\rule{2.em}{0ex}}f\left(z\right)={\displaystyle \frac{z-c}{R}},$$
L1042: again omitting the final summand when $d=2$. Then $W\left({A}_{t}\right)\subset c+r\mathbb{D}\subset \mathsf{\Omega }$, ${\parallel f\parallel }_{\mathsf{\Omega }}\le 1$, and $\parallel f\left({A}_{t}\right)\parallel =2rt/R$. Letting $t\uparrow 1$ proves (cite66†52 ); the last assertion follows by using the inner and outer radii in (cite64†35 ). □
L1043: 
L1044: Corollary 4
L1045: (Sequential form of stability). Fix $d\ge 2$, and let $\left({\mathsf{\Omega }}_{n}\right)$ be proper convex domains. Then $C({\mathsf{\Omega }}_{n},d)\to 2$ if and only if ${\mathsf{\Omega }}_{n}$ is eventually bounded and there are ${c}_{n}\in \mathbb{C}$ and ${r}_{n}>0$ such that
L1046: 
L1047: $${d}_{H}\left({\displaystyle \frac{\overline{{\mathsf{\Omega }}_{n}}-{c}_{n}}{{r}_{n}}},\overline{\mathbb{D}}\right)⟶0,$$
L1048: 
L1049: where the Hausdorff distances are taken on the bounded tail.
L1050: 
L1051: Proof.
L1052: Suppose $C({\mathsf{\Omega }}_{n},d)\to 2$. Apply Theorem 3 successively with ${\epsilon }_{j}=1/(j+2)$, and choose increasing integers ${N}_{j}$ so that all $n\ge {N}_{j}$ admit the corresponding disk sandwich. For each sufficiently large n, choose the sandwich with the largest $j\le n$ for which ${N}_{j}\le n$. Its error tends to zero, and its center and radius give the required normalization. In particular, these domains are bounded.
L1053: Conversely, the support-function estimate used in the proof of Theorem 3 turns Hausdorff convergence into an eventual disk sandwich for every fixed $0<\epsilon <1$. Corollary 3 and $C({\mathsf{\Omega }}_{n},d)\le 2$ give convergence to two by letting $\epsilon \downarrow 0$. □
L1054: 
L1055: The stability modulus (cite67†50 ) is nonconstructive; its positivity follows from compactness in each fixed dimension.
```


Pinned results and lower operations are stipulated true; no truth audit. Full retrieved TeX follows; read ranges are recorded separately.

## preprints/A-direct-proof-of-the-complete-Crouzeix-inequality-September-26-2026/build/main.tex

{"path": "preprints/A-direct-proof-of-the-complete-Crouzeix-inequality-September-26-2026/build/main.tex", "url": "https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-direct-proof-of-the-complete-Crouzeix-inequality-September-26-2026/build/main.tex", "bytes": 35174, "sha256": "54a429fe7129b4760b3015fabf2269d4de5fa38aba9539b18542c1df7e58333f", "git_blob": "5976502d77febf477933f36f6205c6e1aa6370ae", "catalogue_git_blob": "5976502d77febf477933f36f6205c6e1aa6370ae", "matches_catalogue": true}

```tex
\documentclass[11pt]{article}
\usepackage[T1]{fontenc}
\usepackage[utf8]{inputenc}
\usepackage{amsmath,amssymb,amsthm,mathtools}
\usepackage{lmodern}
\usepackage[margin=1.05in]{geometry}
\usepackage{microtype,booktabs,tikz}
\usetikzlibrary{arrows.meta}
\usepackage[colorlinks=true,allcolors=blue]{hyperref}
\newcommand{\C}{\mathbb C}
\newcommand{\T}{\mathbb T}
\newcommand{\D}{\mathbb D}
\newcommand{\HS}[1]{\lvert #1\rvert_2}
\DeclareMathOperator{\tr}{tr}
\DeclareMathOperator{\Rea}{Re}
\DeclareMathOperator{\diag}{diag}
\DeclareMathOperator{\dist}{dist}
\newtheorem{theorem}{Theorem}[section]
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{proposition}[theorem]{Proposition}
\theoremstyle{remark}\newtheorem{remark}[theorem]{Remark}
\numberwithin{equation}{section}
\setlength{\emergencystretch}{2em}
\hypersetup{pdftitle={A direct proof of the complete Crouzeix inequality},pdfauthor={OpenAI}}
\pdftrailerid{}
\title{A direct proof of the complete Crouzeix inequality}
\author{OpenAI}
\date{September 26, 2026}
\begin{document}
\maketitle
\begin{abstract}
We give a direct proof of the sharp constant-two numerical-range inequality
for matrix-valued polynomials in all finite base and coefficient dimensions.
This resolves the complete Crouzeix conjecture in its matrix formulation,
including matrices whose numerical ranges are points or line segments.
\end{abstract}
\section{Introduction}\label{sec:intro}
The numerical range of a matrix $A\in M_n(\C)$ is
\[
 W(A)=\{u^*Au:u\in\C^n,\ u^*u=1\}.
\]
It is a compact convex set containing the spectrum. For a normal matrix,
the spectral theorem controls polynomial evaluation by values on the
spectrum. For a nonnormal matrix, the spectrum alone cannot provide the
same control: even a nonzero nilpotent matrix has spectrum $\{0\}$.
The numerical range retains enough information to give a universal bound.

We allow matrix coefficients. If
$P(z)=\sum_{k=0}^d B_kz^k$ with $B_k\in M_m(\C)$, set
\[
 P[A]=\sum_{k=0}^d A^k\otimes B_k.
\]
The base space $\C^n$ is the first tensor factor. All operator norms
come from the Euclidean inner products and their Hilbert tensor products.
The complete Crouzeix conjecture asks whether the constant two holds
uniformly in the coefficient dimension $m$, the base dimension, and the degree.

\begin{theorem}\label{thm:main}
For every pair of positive integers $n,m$, every $A\in M_n(\C)$,
every nonnegative integer $d$, and every polynomial
$P(z)=\sum_{k=0}^d B_kz^k$ with $B_k\in M_m(\C)$,
\begin{equation}\label{eq:main}
 \|P[A]\|\le2\max_{z\in W(A)}\|P(z)\|.
\end{equation}
The constant two cannot be decreased uniformly over $n,m$, and $d$.
\end{theorem}

The estimate includes point and segment numerical ranges. Its complete
character is the uniformity in $m$: a scalar proof need not survive
matrix amplification, because coefficient matrices need not commute.
The argument below keeps their multiplication order, using the two
products $FG$ and $GF$ separately.

\subsection*{Earlier bounds and related arguments}
Crouzeix formulated the scalar constant-two question in 2004 and proved a
universal complete bound of $11.08$ in 2007
\cite{Crouzeix2004,Crouzeix2007}.
Positive boundary representations developed by Delyon and Delyon
\cite{DelyonDelyon1999} supply an important part of the numerical-range
method. Crouzeix and Palencia combined a positive double-layer potential
with the Cauchy transform of conjugate boundary data to obtain the
complete bound $1+\sqrt2$ \cite{CrouzeixPalencia2017}; Ransford and
Schwenninger simplified its final norm argument
\cite{RansfordSchwenninger2018}.
For all base matrices of order two, Badea, Crouzeix, and Delyon obtained
the complete constant two. In the nonnormal case, they make the conformal
image of the matrix a contraction by a similarity with condition number at
most two, using the numerical-range ellipse \cite{BadeaCrouzeixDelyon2006}.

Recent scalar proofs include work of Jin \cite{Jin2026},
Lorist and Schwenninger \cite{LoristSchwenninger2026}, and Luo
\cite{Luo2026}.
Lorist and Schwenninger's Theorem~3 applies to scalar rational functions
of bounded Hilbert-space operators; their Section~3(iv) explains why the
commutation used in that proof does not automatically persist under
amplification. \AA hag, Czy{\.{z}}, and Virtanen prove the complete
inequality for base matrices of order at most three, with arbitrary
coefficient dimension \cite[Theorem~1.1]{AhagCzyzVirtanen2026}.
The scalar results fix $m=1$, while the latter complete result restricts
the base dimension; Theorem~\ref{thm:main} leaves these dimensions independent.

The use of Faber polynomials in numerical-range functional calculus has
precedents in \cite{Beckermann2005,BeckermannCrouzeix2014}.
Lorist and Schwenninger use a norm-attaining vector in their scalar
argument \cite[Lemma~1]{LoristSchwenninger2026}, while Luo chooses an
explicit top singular pair \cite[Section~3, equations~(21)--(22)]{Luo2026}.
In their complete constant-two proof for weighted shift matrices, Crouzeix
and Greenbaum use a scalar extremal function and a norm-attaining vector
after a similarity reduction
\cite[Section~3, proof of Theorem~2]{CrouzeixGreenbaum2025}.
Here a Faber coefficient estimate controls the two diagonal functionals obtained by placing a test
polynomial on each side of the polynomial being estimated.

A separate structural proof of the complete inequality is given in
\cite{OpenAI2026Complete}. For a bounded convex domain $\Omega$ with
regular real-analytic boundary and $W(A)\subset\Omega$, it constructs a
positive definite $S$ with $\|S\|\|S^{-1}\|\le2$ such that
$S f(A)S^{-1}$ is a contraction, where $f:\Omega\to\D$ is an interior
conformal map and $\D=\{z\in\C:|z|<1\}$. The same $S$, obtained from a
minimizing metric, gives one continuous normalized positive boundary density representing
the calculus of $SAS^{-1}$ for every coefficient dimension and every
matrix function holomorphic near $\overline\Omega$
\cite[Theorems~1.2--1.3 and Proposition~2.1]{OpenAI2026Complete}.
The direct proof below estimates one polynomial at a time. Its exterior
kernel, marginal identities, and positive block comparison have counterparts
in \cite[Propositions~3.1 and~3.3 and Lemma~5.1]{OpenAI2026Complete};
Sections~\ref{sec:coefficients}--\ref{sec:matrix} prove the specific
coefficient, resolvent, and block estimates used here.

\subsection*{How the coefficients give the sharp bound}
First place $W(A)$ strictly inside an analytic convex domain $\Omega$.
An exterior conformal map $h$ parametrizes its boundary by the unit circle.
Expanding the Cauchy kernel at infinity defines scalar polynomials $b_k$ of degree
$k$. For $k\ge1$, the boundary value $b_k\circ h$ has the positive Fourier
term $\lambda^k$ and an otherwise strictly negative expansion. In
Section~\ref{sec:coefficients}, a nonnegative kernel with integral one in
each variable makes the map from the positive part to the negative part an
$L^2$ contraction. Thus, for $G=\sum_k b_kC_k$, its squared boundary
Hilbert--Schmidt norm lies between the square sum of its coefficient norms
and that sum with weight two on every nonconstant coefficient.

For a polynomial $F$ normalized by its boundary operator norm, choose a
unit top singular pair $x,y$ for $F[A]$. The resolvent
$R(\lambda)=\lambda h'(\lambda)(h(\lambda)I-A)^{-1}$ supplies the
coefficient arrays representing the three functionals
$y^*G[A]x$, $x^*G[A]x$, and $y^*G[A]y$. The first is bounded by a
coefficient Hilbert norm. Testing it on $FG$ and $GF$ separately gives
bounds for the other two. Their squared dual coefficient norms have reciprocal
weights: one on the constant coefficient and one half on the others.
These are exactly the weights in the squared Fourier norms of the corresponding
Hermitian diagonal compressions, after a common factor of four.

Section~\ref{sec:matrix} completes the comparison. The numerical-range
condition makes $R+R^*$ positive, so its compression to a two-by-two
block bounds the off-diagonal boundary norm by the two diagonal norms.
The cross term retains all coefficients of the first functional, including
its constant coefficient. The resulting inequality gives the sharp bound
two. Section~\ref{sec:limit} then shrinks analytic convex neighborhoods
to an arbitrary numerical range and proves sharpness with a two-by-two
nilpotent matrix. Appendix~\ref{sec:collar} supplies the exterior collar
using classical conformal mapping and reflection theorems.
\section{Exterior coordinates and coefficient estimates}\label{sec:coefficients}
In this section $\Omega$ is a bounded open convex set with regular real-analytic Jordan boundary. We work with a supplied exterior conformal map $h$ that is one-to-one on $|\lambda|>r$, including infinity on the Riemann sphere, for some $0<r<1$. It maps $|\lambda|>1$ onto $\C\setminus\overline\Omega$ and has a simple pole at infinity, with expansion
\begin{equation}\label{eq:h}
 h(\lambda)=c\lambda+c_0+O(\lambda^{-1}),\qquad c\ne0.
\end{equation}
Appendix~\ref{sec:collar} supplies such a coordinate for every domain under consideration. Here we use it to compare polynomial coefficients with boundary norms.

The map $h$ sends $\T=\{\lambda:|\lambda|=1\}$ onto $\partial\Omega$. Put $q(\lambda)=\lambda h'(\lambda)$. On $\T$, the vector $q(\lambda)$ is an outward normal and $iq(\lambda)$ is a positively oriented tangent. Hence
\begin{equation}\label{eq:support}
 \Re\bigl(\overline{q(\lambda)}(h(\lambda)-z)\bigr)\ge0
 \quad(\lambda\in\T,\ z\in\overline\Omega).
\end{equation}
Figure~\ref{fig:normal} illustrates this supporting-line relation.

\input{figures/normal.tex}

Every circle integral below uses $d\tau(e^{it})=dt/(2\pi)$.

We use the unnormalized Hilbert--Schmidt norm $\HS C=(\tr(C^*C))^{1/2}$, which makes each finite-dimensional matrix space a Hilbert space.

\begin{theorem}[Exterior Faber coefficients and the positive kernel]\label{lem:faber}
Let $\Omega$ be a bounded convex domain with regular real-analytic Jordan boundary. Let $h$ be meromorphic and one-to-one on $|\lambda|>r$ including infinity, where $0<r<1$, with a simple pole at infinity as in \eqref{eq:h}, and mapping $|\lambda|>1$ onto $\C\setminus\overline\Omega$. Put $q(\lambda)=\lambda h'(\lambda)$ and define $b_k(z)$ by expansion at infinity:
\begin{equation}\label{eq:faber}
 \frac{q(\lambda)}{h(\lambda)-z}=\sum_{k\ge0}b_k(z)\lambda^{-k}.
\end{equation}
Then $b_0=1$, and each $b_k$ is a polynomial of degree $k$ with leading coefficient $c^{-k}$. There are scalars $s_{kj}$, $k,j\ge1$, such that
\begin{equation}\label{eq:boundary-basis}
 b_k(h(\mu))=\mu^k+\sum_{j\ge1}s_{kj}\mu^{-j}\quad(k\ge1).
\end{equation}
The function
\begin{equation}\label{eq:s}
 s(\lambda,\mu)=\frac{q(\lambda)}{h(\lambda)-h(\mu)}-\frac{\lambda}{\lambda-\mu}
 =\sum_{k,j\ge1}s_{kj}\lambda^{-k}\mu^{-j}
\end{equation}
extends holomorphically across the diagonal and both infinities in $|\lambda|,|\mu|>r$. For every $r<\rho<1$ there is a constant $C_\rho$ with
$|s_{kj}|\le C_\rho\rho^{k+j}$. The series converges normally on
the exterior product collar: it converges absolutely and uniformly on
every compact subset, including subsets meeting either infinity.
In particular it converges absolutely and uniformly on $\T^2$. The continuous kernel
\[
 K(\lambda,\mu)=1+s(\lambda,\mu)+\overline{s(\lambda,\mu)}
\]
is nonnegative and has integral one in each variable with the other fixed.
\end{theorem}

\begin{proof}
Expanding the denominator in \eqref{eq:faber} after factoring $c\lambda$ shows that its $k$th coefficient is a polynomial of degree $k$ with leading term $c^{-k}z^k$. The constant coefficient is one. In particular, the $b_k$ form a basis of the scalar polynomials.

For the joint extension, consider
\[
 H(\lambda,\mu)=\frac{h(\lambda)-h(\mu)}{\lambda-\mu}.
\]
Write $u=\lambda^{-1}$, $v=\mu^{-1}$ and $h(\lambda)=c\lambda+g(u)$, where $g$ is holomorphic on $|u|<r^{-1}$. Then
\begin{equation}\label{eq:H}
 H=c-uv\frac{g(u)-g(v)}{u-v}.
\end{equation}
The divided difference of $g$ is jointly holomorphic, with diagonal value $g'(u)$, so this formula also covers either or both infinities. Off the diagonal and away from the axes, $H$ is nonzero by injectivity of $h$. On the diagonal it equals $h'(\lambda)\ne0$; on either axis it equals $c$. Thus it has no zeros on the reciprocal bidisk.

Direct differentiation gives $s=\lambda\partial_\lambda H/H=-u\partial_uH/H$. This function is holomorphic and vanishes on both reciprocal axes. Its Taylor series has precisely the strictly mixed powers in \eqref{eq:s}. For any $r<\rho<1$, Cauchy estimates on the closed reciprocal bidisk
of radius $\rho^{-1}$ give a constant $C_\rho$ with
$|s_{kj}|\le C_\rho\rho^{k+j}$. On a compact subset of the exterior
product collar, choose $\sigma>r$ below all finite coordinate moduli,
and then $r<\rho<\min(1,\sigma)$. The resulting geometric double
series dominates the Laurent series uniformly there; terms vanish on
the reciprocal axes. This proves normal convergence throughout the
product collar and absolute uniform convergence on the boundary. Comparing coefficients at $\lambda=\infty$ in \eqref{eq:s}, first for fixed finite $\mu$ in the exterior collar, yields \eqref{eq:boundary-basis}.

For distinct $\lambda,\mu\in\T$, one has $2\Re(\lambda/(\lambda-\mu))=1$, and therefore
\[
 K(\lambda,\mu)=2\Re\frac{q(\lambda)}{h(\lambda)-h(\mu)}\ge0
\]
by \eqref{eq:support}. Continuity gives the same sign on the diagonal. Every term of $s$ and of its conjugate has nonzero frequency in each variable. Their integrals in either variable vanish, proving both normalizations.
\end{proof}

To identify the basis, let $\Phi=h^{-1}$ in the exterior. Equation~\eqref{eq:boundary-basis}, which holds throughout the exterior collar, gives $b_k(z)-\Phi(z)^k=O(z^{-1})$ at infinity. Thus $b_k$ is the polynomial part of $\Phi^k$, the Faber polynomial associated with the chosen exterior coordinate. The usual normalization chooses the phase of $h$ so that $c>0$ \cite{Beckermann2005,BeckermannCrouzeix2014}.

These mixed coefficients are differentiated Grunsky coefficients.
The classical normalization gives a weighted coefficient inequality
\cite[equations~(1.1)--(1.3)]{BeckermannStylianopoulos2018};
the unweighted estimate used here follows from convexity and the two
angular marginal identities.

The two normalizations in Theorem~\ref{lem:faber} use the same exterior circle measure. Together they control the negative Fourier part of a boundary polynomial by its positive part, as follows.

\begin{proposition}[The coefficient norm estimate]\label{prop:coefficients}
For every positive integer $m$ and every $M_m(\C)$-valued polynomial $G(z)=\sum_{k=0}^N b_k(z)C_k$,
\begin{equation}\label{eq:coefficient-estimate}
 \sum_{k=0}^N\HS{C_k}^2
 \le\int_\T\HS{G(h(\mu))}^2\,d\tau(\mu)
 \le\HS{C_0}^2+2\sum_{k=1}^N\HS{C_k}^2.
\end{equation}
\end{proposition}
\begin{proof}
For $u\in L^2(\T;\mathcal H)$ with values in a Hilbert space $\mathcal H$, define
\[
 (Tu)(\mu)=\int_\T K(\lambda,\mu)u(\lambda)\,d\tau(\lambda).
\]
Positivity and the normalization in $\lambda$ imply
$\|(Tu)(\mu)\|^2\le\int K(\lambda,\mu)\|u(\lambda)\|^2d\tau(\lambda)$.
Integrating in $\mu$ and using the normalization in that variable shows that $T$ is an $L^2$ contraction.

For $u(\lambda)=\sum_{k=1}^N C_k\lambda^k$, only the $s$ term contributes to the integral, so
\begin{equation}\label{eq:kernel-fourier-action}
 (Tu)(\mu)=\sum_{j\ge1}\left(\sum_{k=1}^Ns_{kj}C_k\right)\mu^{-j}.
\end{equation}
All interchanges are justified by the absolute uniform convergence in Theorem~\ref{lem:faber}. In particular,
\[
 \sum_{j\ge1}\HS{\sum_{k=1}^Ns_{kj}C_k}^2\le\sum_{k=1}^N\HS{C_k}^2.
\]
By \eqref{eq:boundary-basis}, the boundary value of $G$ is the sum of its constant term $C_0$, its positive part $u$, and its negative part $Tu$. These have disjoint Fourier supports. Parseval's identity gives
\[
 \int_\T\HS{G\circ h}^2d\tau
 =\HS{C_0}^2+\sum_{k=1}^N\HS{C_k}^2+
   \sum_{j\ge1}\HS{\sum_{k=1}^Ns_{kj}C_k}^2,
\]
which proves both inequalities.
\end{proof}
For comparison with \cite[Proposition~3.1]{OpenAI2026Complete}, the
companion's exterior map $G$ and variables $t,w$ correspond to
$h,\lambda,\mu$, respectively.
The mixed correction is $s(\lambda,\mu)=B(\mu,\lambda)$, so
$s_{kj}=\beta_{jk}$ in that paper's notation. In particular,
\eqref{eq:kernel-fourier-action} uses this coefficient orientation and
does not require symmetry of the kernel.
\section{Singular vectors and the amplified estimate}\label{sec:matrix}
Fix $A\in M_n(\C)$ with $W(A)\subset\Omega$.
To estimate the norm of one polynomial evaluation, we form coefficient
functionals from its left and right singular vectors. The resolvent supplies
their coefficient arrays, while its positive Hermitian part compares the
resulting boundary norms. This Hermitian field is the numerical-range double-layer kernel of
\cite{DelyonDelyon1999,CrouzeixPalencia2017}; we prove the required
positivity for the original matrix $A$.

\begin{theorem}[The resolvent expansion and double-layer positivity]\label{lem:resolvent}
Let $\Omega,h,q$, and $(b_k)$ satisfy the hypotheses and conclusions of Theorem~\ref{lem:faber}. For any positive integer $n$ and $A\in M_n(\C)$ with $W(A)\subset\Omega$, on $\T$ let
\begin{equation}\label{eq:R}
 R(\lambda)=q(\lambda)(h(\lambda)I-A)^{-1}.
\end{equation}
Then
\[
 R(\lambda)=\sum_{k\ge0}b_k(A)\lambda^{-k},\qquad R(\lambda)+R(\lambda)^*\succeq0.
\]
For the fixed $A,h$, there are constants $C<\infty$ and $0<\theta<1$
such that $\|b_k(A)\|\le C\theta^k$ for all $k\ge0$. Thus the series
converges absolutely and uniformly on $\T$. In particular,
$\int_\T R\,d\tau=I$ and $\int_\T(R+R^*)\,d\tau=2I$.
\end{theorem}
\begin{proof}
Every eigenvalue of $A$ belongs to $W(A)$, by testing a unit eigenvector. Thus the exterior resolvent is defined on and outside the boundary. Compactness of the circle and strict spectral separation allow a smaller collar $|\lambda|>r_A$, with $r<r_A<1$, on which it remains holomorphic, including infinity where $R(\infty)=I$. Expansion at infinity gives the coefficients $b_k(A)$: this follows either by the geometric resolvent series for large $|h(\lambda)|$ or by substituting $A$ into the polynomial coefficient identities in \eqref{eq:faber}. Choose $r_A<\theta<1$. Cauchy estimates on the reciprocal circle of
radius $\theta^{-1}$ give the stated geometric bound. They imply
absolute uniform convergence on $\T$, and its constant coefficient
$b_0(A)=I$ gives both integrals.

For $B=h(\lambda)I-A$, direct congruence gives
\[
 B^*(R+R^*)B=\overline{q(\lambda)}B+q(\lambda)B^*.
\]
For each unit vector $v$, the quadratic form on the right is
$2\Re(\overline{q(\lambda)}(h(\lambda)-v^*Av))$, which is nonnegative by \eqref{eq:support}. Invertibility of $B$ proves positivity.
\end{proof}

\begin{theorem}[The bound on an analytic convex domain]\label{thm:domain}
For positive integers $n,m$, let $\Omega\subset\C$ be bounded, open, and convex with regular real-analytic Jordan boundary, and let $A\in M_n(\C)$ satisfy $W(A)\subset\Omega$. For every $M_m(\C)$-valued polynomial $F$ with $\|F(z)\|\le1$ on $\partial\Omega$, one has $\|F[A]\|\le2$.
\end{theorem}
\begin{proof}
Choose $h$ from Lemma~\ref{lem:exterior-collar} and apply
Theorem~\ref{lem:faber} to this coordinate.
Put $\gamma=\|F[A]\|$. There is nothing to prove if $\gamma=0$. Otherwise choose unit singular vectors $x,y\in\C^n\otimes\C^m$ such that
\begin{equation}\label{eq:singular}
 F[A]x=\gamma y,\qquad F[A]^*y=\gamma x.
\end{equation}
Write $x=\sum_{i=1}^mXe_i\otimes e_i$ and $y=\sum_{i=1}^mYe_i\otimes e_i$, where $X,Y$ are $n$-by-$m$ matrices and $(e_i)$ is the standard basis of $\C^m$. For the resolvent in Theorem~\ref{lem:resolvent}, define matrix functions
\[
 P=X^*RX,\quad Q=Y^*RY,\quad M=Y^*RX,\quad L=X^*RY.
\]
Subscripts $k\ge0$ denote the coefficients of $\lambda^{-k}$, so $M_k=Y^*b_k(A)X$, for example. By Theorem~\ref{lem:resolvent}, all four series converge absolutely and uniformly on $\T$, and their coefficient sequences are square summable. Since $b_0=1$,
\begin{equation}\label{eq:means}
 P_0=X^*X=P_0^*,\qquad Q_0=Y^*Y=Q_0^*,\qquad L_0^*=M_0.
\end{equation}
Set $a^2=\sum_{k\ge0}\HS{M_k}^2$. We will bound the squared
boundary $L^2$ Hilbert--Schmidt norms of $P+P^*$ and $Q+Q^*$
above by $4a^2/\gamma^2$ each, and that of $M+L^*$ below by $a^2$.
Positivity will then compare these quantities and force $\gamma\le2$.

\emph{The off-diagonal coefficient functional.}
For a polynomial $G=\sum_k b_kC_k$, direct expansion in the tensor basis gives
\begin{equation}\label{eq:pairing}
 y^*G[A]x=\sum_{k,i,j}(M_k)_{ij}(C_k)_{ij}.
\end{equation}
Indeed, $C_ke_j=\sum_i(C_k)_{ij}e_i$ in the coefficient factor, leaving $(Ye_i)^*b_k(A)Xe_j$ in the base factor. Equation~\eqref{eq:pairing} is the bilinear entry pairing of the two coefficient arrays. Cauchy--Schwarz gives
\begin{equation}\label{eq:crossfunctional}
 |y^*G[A]x|\le a\left(\sum_k\HS{C_k}^2\right)^{1/2}.
\end{equation}
Taking $G=F$ and using \eqref{eq:singular} shows that $a>0$.

\emph{The two ordered tests.}
Polynomial evaluation respects multiplication in its given order. Explicitly, if $F(z)=\sum_iD_iz^i$ and $G(z)=\sum_jE_jz^j$, then
\[
 (FG)[A]=\sum_{i,j}A^{i+j}\otimes D_iE_j=F[A]G[A],
\]
and the reversed product has coefficients $E_jD_i$. Hence
\begin{equation}\label{eq:ordered-products}
 y^*(FG)[A]x=\gamma x^*G[A]x,\qquad
 y^*(GF)[A]x=\gamma y^*G[A]y.
\end{equation}
Write the full finite Faber expansions as
\[
 FG=\sum_k b_kU_k,\qquad GF=\sum_k b_kV_k,
 \qquad \|H\|_\partial^2=\int_\T\HS{H(h(\mu))}^2\,d\tau(\mu).
\]
The functional in \eqref{eq:crossfunctional} uses all $M_k$, so it applies
to these full expansions for every finite degree. Apply it to the two
identities in \eqref{eq:ordered-products}. The lower coefficient estimate
in Proposition~\ref{prop:coefficients} and the two boundary multiplier
bounds give
\begin{align*}
 \gamma|x^*G[A]x|
 &\le a\Bigl(\sum_k\HS{U_k}^2\Bigr)^{1/2}
 \le a\|FG\|_\partial\le a\|G\|_\partial,\\
 \gamma|y^*G[A]y|
 &\le a\Bigl(\sum_k\HS{V_k}^2\Bigr)^{1/2}
 \le a\|GF\|_\partial\le a\|G\|_\partial.
\end{align*}
Here $\HS{F(z)G(z)}\le\|F(z)\|\HS{G(z)}$ and
$\HS{G(z)F(z)}\le\HS{G(z)}\|F(z)\|$ are used in their
respective orders. The upper coefficient estimate for $G$ now gives
\begin{equation}\label{eq:diagonal-functional}
 \max\{|x^*G[A]x|,|y^*G[A]y|\}
 \le\frac a\gamma
 \left(\HS{C_0}^2+2\sum_{k\ge1}\HS{C_k}^2\right)^{1/2}.
\end{equation}
The entries paired with $C_k$ in these two functionals are respectively those of $P_k$ and $Q_k$, by the calculation in \eqref{eq:pairing}. The weighted coefficient norm on the right gives reciprocal weights on these two coefficient sequences:
\begin{equation}\label{eq:weighted-dual}
 \HS{P_0}^2+\tfrac12\sum_{k\ge1}\HS{P_k}^2\le a^2/\gamma^2,
 \qquad
 \HS{Q_0}^2+\tfrac12\sum_{k\ge1}\HS{Q_k}^2\le a^2/\gamma^2.
\end{equation}
For the first inequality, set
$d_N=\HS{P_0}^2+\tfrac12\sum_{k=1}^N\HS{P_k}^2$
and test \eqref{eq:diagonal-functional} with $C_0=\overline{P_0}$,
$C_k=\overline{P_k}/2$ for $1\le k\le N$, and $C_k=0$ otherwise;
bars mean entrywise conjugation. The paired value is $d_N$, and the squared
weighted test norm is also $d_N$. Hence
$d_N\le(a/\gamma)\sqrt{d_N}$, which gives $d_N\le a^2/\gamma^2$
including when $d_N=0$. Letting $N\to\infty$ proves the first bound.
The same finite tests with $Q_k$ prove the second.

\emph{The boundary norms of the three blocks.}
The compression of $R+R^*$ by $[X\ Y]$ has diagonal blocks $P+P^*$,
$Q+Q^*$ and lower off-diagonal block $M+L^*$. We first compute their
boundary norms. In the diagonal fields, \eqref{eq:means} makes the
constant term twice $P_0$ or $Q_0$. For $k\ge1$, the coefficients $P_k$
and $P_k^*$ occur at frequencies $-k$ and $k$ and have equal
Hilbert--Schmidt norms; the same holds for $Q_k$ and $Q_k^*$.
Parseval therefore gives four times the reciprocal weighted sum in
\eqref{eq:weighted-dual}:
\begin{equation}\label{eq:diagonal-L2}
 \int_\T\HS{P+P^*}^2d\tau
 =4\left(\HS{P_0}^2+\tfrac12\sum_{k\ge1}\HS{P_k}^2\right)
 \le4a^2/\gamma^2,
\end{equation}
and the same identity and bound hold for $Q+Q^*$.

For the cross field, $L_0^*=M_0$ makes the constant term $2M_0$.
Its negative coefficients are $M_k$ for $k\ge1$ and its positive
coefficients are $L_k^*$ for $k\ge1$. Consequently
\begin{equation}\label{eq:cross-L2}
 \int_\T\HS{M+L^*}^2d\tau
 =4\HS{M_0}^2+\sum_{k\ge1}\bigl(\HS{M_k}^2+\HS{L_k}^2\bigr)
 \ge a^2.
\end{equation}

\emph{The positive block comparison.}
Theorem~\ref{lem:resolvent} gives $R+R^*\succeq0$. Its compression by the
$n$-by-$2m$ matrix $[X\ Y]$ is therefore
\[
 \Delta=\begin{pmatrix}P+P^*&L+M^*\\M+L^*&Q+Q^*\end{pmatrix}\succeq0.
\]
For $J=\diag(I_m,-I_m)$, the matrix $J\Delta J$ is also positive, so
\[
 0\le\tr\bigl(\Delta^{1/2}(J\Delta J)\Delta^{1/2}\bigr)
 =\tr(\Delta J\Delta J)
 =\HS{P+P^*}^2+\HS{Q+Q^*}^2-2\HS{M+L^*}^2.
\]
Integrating this inequality and using \eqref{eq:diagonal-L2} and \eqref{eq:cross-L2} yields
\[
 2a^2\le2\int_\T\HS{M+L^*}^2d\tau
 \le\int_\T\bigl(\HS{P+P^*}^2+\HS{Q+Q^*}^2\bigr)d\tau
 \le8a^2/\gamma^2.
\]
Since $a>0$, this proves $\gamma\le2$.
\end{proof}
\section{Enclosing domains and arbitrary numerical ranges}\label{sec:limit}
Theorem~\ref{thm:domain} applies on an analytic convex neighborhood. We now construct such neighborhoods even for compact convex sets with empty interior, and then shrink them to $W(A)$.

\begin{lemma}[Analytic convex outer approximation]\label{lem:approx}
Let $K\subset\C$ be nonempty, compact, and convex. There are bounded convex open domains $\Omega_j$ with regular real-analytic Jordan boundaries such that $K\subset\Omega_j$ and
\[
 \sup_{z\in\overline\Omega_j}\dist(z,K)\longrightarrow0.
\]
\end{lemma}
\begin{proof}
For $0<\delta<1$, choose a finite Euclidean $\delta$-net $D_\delta$ of unit directions that includes $1,-1,i,-i$. Let $s_K(\nu)=\max_{z\in K}\Re(\bar\nu z)$ be the support function. Choose $t_\delta>0$ with $|D_\delta|e^{-t_\delta\delta}<1$, and define
\[
 \Phi_\delta(z)=\sum_{\nu\in D_\delta}
 \exp\bigl(t_\delta(\Re(\bar\nu z)-s_K(\nu)-\delta)\bigr),
 \qquad \Omega_\delta=\{z:\Phi_\delta(z)<1\}.
\]
Each point of $K$ satisfies $\Phi_\delta<1$, so $K\subset\Omega_\delta$.
If $\Phi_\delta(z)\le1$, each positive summand is at most one, and hence
\[
 \Re(\bar\nu z)\le s_K(\nu)+\delta\qquad(\nu\in D_\delta).
\]
In particular, the four axis directions give
\[
 \begin{aligned}
 \min_{w\in K}\Re w-\delta&\le\Re z\le\max_{w\in K}\Re w+\delta,\\
 \min_{w\in K}\Im w-\delta&\le\Im z\le\max_{w\in K}\Im w+\delta.
 \end{aligned}
\]
Thus one fixed rectangle contains every closed sublevel for $0<\delta<1$.

The Hessian is a sum of positive multiples of $\nu\nu^{\mathsf T}$ after identifying $\C$ with $\mathbb R^2$. The four axis directions ensure it is positive definite. Thus $\Phi_\delta$ is strictly convex and real analytic.

The gradient cannot vanish at level one: a critical point of a differentiable convex function is a global minimum, whereas every point of $K$ has value less than one. The implicit function theorem therefore makes that level a regular real-analytic curve. The open sublevel set is bounded and convex with nonempty interior. Fix an interior point. Each ray from it crosses level one exactly once; convexity and boundedness give existence and uniqueness. Radial projection from the compact boundary to the circle is a continuous bijection, hence a homeomorphism. The boundary is a Jordan curve, and $\overline\Omega_\delta=\{\Phi_\delta\le1\}$.

It remains to bound the distance of this sublevel from $K$. For
$z\in\overline\Omega_\delta\setminus K$, let $w\in K$ be nearest to $z$,
put $d=|z-w|$ and $\nu=(z-w)/d$, and choose $\mu\in D_\delta$ with
$|\mu-\nu|\le\delta$. Choose $v\in K$ attaining $s_K(\mu)$.
Since $w+t(v-w)\in K$ for $0\le t\le1$, minimality of $w$ gives
$\Re(\bar\nu(v-w))\le0$.
Using this inequality and the support inequality for $\mu$, we obtain
\[
 \begin{aligned}
 (1-\delta)d
 &\le\Re(\bar\mu(z-w))\\
 &\le\Re(\bar\mu(v-w))+\delta\\
 &\le\delta|v-w|+\delta
 \le\delta\bigl(1+\operatorname{diam}K\bigr).
 \end{aligned}
\]
The first and third inequalities use $|\mu-\nu|\le\delta$. Points of $K$
have distance zero, so
\[
 \sup_{z\in\overline\Omega_\delta}\dist(z,K)
 \le\frac{\delta(1+\operatorname{diam}K)}{1-\delta}\longrightarrow0.
\]
Taking, for example, $\delta_j=1/(j+1)$ completes the construction.
\end{proof}

\begin{proof}[Proof of Theorem~\ref{thm:main}]
Compactness of $W(A)$ follows from compactness of the unit sphere. We recall a short proof of the Toeplitz--Hausdorff convexity theorem \cite{Toeplitz1918,Hausdorff1919}. To join two numerical-range values, compress $A$ to the span of their unit testing vectors. If that span has dimension one there is nothing to prove. In dimension two, its quadratic form on unit vectors $(u,v)$ is a complex-valued real-affine function of
\[
 (2\Re(\bar uv),\ 2\Im(\bar uv),\ |u|^2-|v|^2),
\]
which ranges over the full unit sphere in $\mathbb R^3$. The linear part of a map from $\mathbb R^3$ to $\mathbb R^2$ has a nonzero kernel. Any point of the unit ball can be moved in a kernel direction to the sphere without changing its image. Thus the images of the sphere and ball coincide, and this image is convex. Its segment between the chosen values belongs to the numerical range of the compression and hence to $W(A)$.

Apply Lemma~\ref{lem:approx} with $K=W(A)$. By scaling Theorem~\ref{thm:domain},
\[
 \|P[A]\|\le2\max_{z\in\overline\Omega_j}\|P(z)\|.
\]
If this maximum is zero, each entry of $P$ vanishes on an open set and the polynomial is identically zero, making the inequality immediate. Otherwise divide $P$ by the maximum to invoke that theorem. All $\overline\Omega_j$ lie in one compact set. Uniform continuity of the fixed function $z\mapsto\|P(z)\|$, the containment of $K$, and the uniform distance convergence imply convergence of these maxima to $\max_K\|P\|$. This proves \eqref{eq:main} without any interior assumption on $K$.

For sharpness take $n=2$, $m=1$, $P(z)=z$, and
\[
 A=\begin{pmatrix}0&2\\0&0\end{pmatrix}.
\]
Its norm is two, while $|x^*Ax|=2|x_1x_2|\le1$ for every unit $x$, with equality at $x_1=x_2=1/\sqrt2$. Thus the right-hand maximum in \eqref{eq:main} is one. No smaller universal constant is possible.
\end{proof}
\appendix
\section{The exterior conformal collar}\label{sec:collar}
We record the classical conformal inputs and prove the continuation and global injectivity required in Section~\ref{sec:coefficients}.

\begin{lemma}[Exterior coordinate and a univalent collar]
\label{lem:exterior-collar}
Let $\Omega\subset\mathbb C$ be a bounded convex domain whose boundary
is a regular real-analytic Jordan curve. There are $0<r_0<1$ and a map
$h$, meromorphic on $\{\lambda:|\lambda|>r_0\}\cup\{\infty\}$,
which is one-to-one there as a map of the sphere, has a simple pole at
infinity, and maps $|\lambda|>1$ conformally onto
$\mathbb C\setminus\overline\Omega$. It maps the unit circle onto
$\partial\Omega$ and has an expansion
\[
 h(\lambda)=c\lambda+c_0+\sum_{j\ge1}c_j\lambda^{-j},\qquad c\ne0.
\]
For $\lambda$ on the unit circle, $q(\lambda)=\lambda h'(\lambda)$
is a nonzero outward normal vector at $h(\lambda)$. In particular,
\[
 \operatorname{Re}\bigl(\overline{q(\lambda)}(h(\lambda)-z)\bigr)
 \ge0\qquad (z\in\overline\Omega).
\]
\end{lemma}

\begin{proof}
Fix $z_*\in\Omega$ and apply $z\mapsto1/(z-z_*)$, with infinity
mapped to zero, to the spherical exterior
$(\mathbb C\setminus\overline\Omega)\cup\{\infty\}$. Its image $U$ is
a bounded simply connected domain containing zero, with a regular
real-analytic Jordan boundary. Indeed, each ray from $z_*$ meets
$\partial\Omega$ at a unique positive radius; inversion turns the
exterior portions of these rays into a star-shaped domain about zero.
The Riemann mapping theorem \cite[Chapter~6, Section~1.1, Theorem~1]{Ahlfors1979}
supplies a conformal bijection
$g:\mathbb D\to U$ with $g(0)=0$. Carath\'eodory's Jordan-domain theorem
\cite[Chapter~6, Section~1.2]{Ahlfors1979} extends $g$ to a homeomorphism $\overline{\mathbb D}\to\overline U$.

We justify the stronger boundary continuation needed below. A regular
real-analytic boundary arc has a real-analytic parametrization with
nonzero derivative. Its holomorphic continuation and the holomorphic
inverse-function theorem provide a local coordinate in which the arc
is a real interval and the domain is one side of that interval. Choose
such coordinates at $\zeta\in\partial\mathbb D$ and
$p=g(\zeta)\in\partial U$. Continuity of the boundary extension lets us
shrink the source neighborhood so that $g$ maps its intersection with
$\overline{\mathbb D}$ into the target chart.
The composition representing $g$ in these
coordinates is holomorphic on a half disk, continuous on its real
interval, and real-valued there. Schwarz reflection extends it
holomorphically across the interval
\cite[Chapter~4, Section~6.5; Chapter~6, Sections~1.3--1.4]{Ahlfors1979}. Apply the same procedure to
$g^{-1}$. Shrink the neighborhoods so that the reflected maps can be
composed. Their compositions equal the identity on the original domain
side, and hence throughout a smaller neighborhood by the identity theorem.
Thus the continued $g$ has nonzero derivative at each boundary point.

To patch the local continuations, choose around every
$\zeta\in\partial\mathbb D$ a disk $B(\zeta,R_\zeta)$ carrying such a continuation, agreeing
with $g$ on its intersection with $\mathbb D$. Select finitely many of
the third-radius disks $V_i=B(\zeta_i,R_i/3)$ that cover the circle,
and denote the larger disks by $U_i=B(\zeta_i,R_i)$. If
$V_i\cap V_j\ne\varnothing$ and $R_i\ge R_j$, then
$|\zeta_i-\zeta_j|<(R_i+R_j)/3\le2R_i/3<R_i$.
The connected lens $U_i\cap U_j$ therefore contains $\zeta_j$ and
meets $\mathbb D$. The two continuations coincide there by the identity
theorem. They consequently patch with $g$ to a holomorphic map on
$\mathbb D\cup\bigcup_iV_i$, a neighborhood of the closed disk.

The extension is injective on a smaller neighborhood of the closed
disk. Otherwise, distinct colliding pairs arbitrarily close to that
compact set would have subsequential limits in the closed disk.
Continuity and injectivity on the closed disk identify their limits.
Both points of each pair would then eventually lie in one local
inverse neighborhood of that common limit, a contradiction. By compactness,
this injective neighborhood contains the disk $\{w:|w|<R_0\}$ for some $R_0>1$.
Thus $g$ is univalent on that disk. Its sole zero there
is $0$, and that zero is simple. Set
\[
 h(\lambda)=z_*+\frac1{g(1/\lambda)},\qquad r_0=R_0^{-1}.
\]
This gives all mapping and extension assertions, including the simple
pole with coefficient $c=1/g'(0)\ne0$.

Finally, at $\lambda=e^{i\theta}$ the radial and angular derivatives
are $q(\lambda)$ and $iq(\lambda)$, respectively. They are perpendicular
and nonzero. Increasing the radial parameter enters the exterior of
$\overline\Omega$, so $q(\lambda)$ points outward. The supporting
half-plane property of a smooth convex boundary proves the final
inequality.
\end{proof}
\input{references.tex}
\end{document}

```

## preprints/A-direct-proof-of-the-complete-Crouzeix-inequality-September-26-2026/build/references.tex

{"path": "preprints/A-direct-proof-of-the-complete-Crouzeix-inequality-September-26-2026/build/references.tex", "url": "https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-direct-proof-of-the-complete-Crouzeix-inequality-September-26-2026/build/references.tex", "bytes": 4313, "sha256": "6402be83926f774063d5e4e65a0075a68682419f388eb9c7c500231fb350b2b6", "git_blob": "5afd2ba6d247c20795e4aee5e5fd6bab84cc14ba", "catalogue_git_blob": "5afd2ba6d247c20795e4aee5e5fd6bab84cc14ba", "matches_catalogue": true}

```tex
\begin{thebibliography}{99}
\raggedright

\bibitem{AhagCzyzVirtanen2026}
P.~\AA hag, R.~Czy{\.{z}}, and J.~Virtanen,
\emph{The complete Crouzeix conjecture in dimension three and the
Clou\^atre--Ostermann--Ransford conjecture},
\href{https://arxiv.org/abs/2608.27346v4}{arXiv:2608.27346v4}, September 21, 2026.

\bibitem{Ahlfors1979}
L.~V. Ahlfors, \emph{Complex Analysis}, third ed., McGraw--Hill, New York, 1979.

\bibitem{BadeaCrouzeixDelyon2006}
C.~Badea, M.~Crouzeix, and B.~Delyon,
Convex domains and $K$-spectral sets,
\emph{Math. Z.} \textbf{252} (2006), 345--365.
\href{https://doi.org/10.1007/s00209-005-0857-y}{doi:10.1007/s00209-005-0857-y}.

\bibitem{Beckermann2005}
B.~Beckermann, Image num{\'e}rique, GMRES et polyn{\^o}mes de Faber,
\emph{C. R. Math.} \textbf{340} (2005), 855--860.
\href{https://doi.org/10.1016/j.crma.2005.04.027}{doi:10.1016/j.crma.2005.04.027}.

\bibitem{BeckermannCrouzeix2014}
B.~Beckermann and M.~Crouzeix,
Faber polynomials of matrices for non-convex sets,
\emph{Jaen J. Approx.} \textbf{6} (2014), 219--231.
\href{https://arxiv.org/abs/1310.1356v1}{arXiv:1310.1356v1}.

\bibitem{BeckermannStylianopoulos2018}
B. Beckermann and N. Stylianopoulos,
\emph{Bergman Orthogonal Polynomials and the Grunsky Matrix},
Constr. Approx. \textbf{47} (2018), 211--235.
\href{https://doi.org/10.1007/s00365-017-9381-7}{doi:10.1007/s00365-017-9381-7}.

\bibitem{Crouzeix2004}
M.~Crouzeix, Bounds for analytical functions of matrices,
\emph{Integral Equations Operator Theory} \textbf{48} (2004), 461--477.
\href{https://doi.org/10.1007/s00020-002-1188-6}{doi:10.1007/s00020-002-1188-6}.

\bibitem{Crouzeix2007}
M.~Crouzeix, Numerical range and functional calculus in Hilbert space,
\emph{J. Funct. Anal.} \textbf{244} (2007), 668--690.
\href{https://doi.org/10.1016/j.jfa.2006.10.013}{doi:10.1016/j.jfa.2006.10.013}.

\bibitem{CrouzeixGreenbaum2025}
M.~Crouzeix and A.~Greenbaum,
\emph{A new proof that the numerical range is a complete $2$-spectral
set for weighted shift matrices},
\href{https://arxiv.org/abs/2508.12768v1}{arXiv:2508.12768v1},
August 18, 2025.

\bibitem{CrouzeixPalencia2017}
M.~Crouzeix and C.~Palencia,
The numerical range is a $(1+\sqrt{2})$-spectral set,
\emph{SIAM J. Matrix Anal. Appl.} \textbf{38} (2017), 649--655.
\href{https://doi.org/10.1137/17M1116672}{doi:10.1137/17M1116672}.

\bibitem{DelyonDelyon1999}
B.~Delyon and F.~Delyon,
Generalization of von Neumann's spectral sets and integral representation of operators,
\emph{Bull. Soc. Math. France} \textbf{127} (1999), 25--41.
\href{https://doi.org/10.24033/bsmf.2340}{doi:10.24033/bsmf.2340}.

\bibitem{Hausdorff1919}
F.~Hausdorff, Der Wertvorrat einer Bilinearform,
\emph{Math. Z.} \textbf{3} (1919), 314--316.
\href{https://doi.org/10.1007/BF01292610}{doi:10.1007/BF01292610}.

\bibitem{Jin2026}
S.~Jin, \emph{The numerical range is a $2$-spectral set},
\href{https://www.preprints.org/manuscript/202607.1919/v4}{Preprints.org 202607.1919, version 4},
August 7, 2026.

\bibitem{LoristSchwenninger2026}
E.~Lorist and F.~L. Schwenninger,
\emph{A solution to Crouzeix's conjecture},
\href{https://arxiv.org/abs/2608.03841v2}{arXiv:2608.03841v2}, August 17, 2026.

\bibitem{Luo2026}
Q.~Luo, \emph{Two boundary-certificate proofs of the Crouzeix theorem:
Fiberwise Fourier recurrence and defect-Gram telescoping},
\href{https://www.preprints.org/manuscript/202608.1661/v2}{Preprints.org 202608.1661, version 2},
August 28, 2026.

\bibitem{OpenAI2026Complete}
OpenAI, \emph{The complete Crouzeix theorem: optimal similarity and a
common positive boundary representation},
OpenAI Math Release preprint
\href{https://github.com/openai/math/blob/main/preprints/The-complete-Crouzeix-theorem-September-23-2026/paper.pdf}{OAI:The-complete-Crouzeix-theorem-September-23-2026},
2026.

\bibitem{RansfordSchwenninger2018}
T.~Ransford and F.~L. Schwenninger,
Remarks on the Crouzeix--Palencia proof that the numerical range is a
$(1+\sqrt{2})$-spectral set,
\emph{SIAM J. Matrix Anal. Appl.} \textbf{39} (2018), 342--345.
\href{https://doi.org/10.1137/17M1143757}{doi:10.1137/17M1143757}.

\bibitem{Toeplitz1918}
O.~Toeplitz, Das algebraische Analogon zu einem Satze von Fej{\'e}r,
\emph{Math. Z.} \textbf{2} (1918), 187--197.
\href{https://doi.org/10.1007/BF01212904}{doi:10.1007/BF01212904}.

\end{thebibliography}

```

## preprints/The-complete-Crouzeix-theorem-September-23-2026/build/main.tex

{"path": "preprints/The-complete-Crouzeix-theorem-September-23-2026/build/main.tex", "url": "https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-complete-Crouzeix-theorem-September-23-2026/build/main.tex", "bytes": 69205, "sha256": "8a5de532bd3bd4c0b84cc8114c22175968813a6e984ced0d1bf48011270e621c", "git_blob": "2ace452c83a9ceb994a87ae9009441706d90a961", "catalogue_git_blob": "2ace452c83a9ceb994a87ae9009441706d90a961", "matches_catalogue": true}

```tex
\documentclass[11pt]{article}
\usepackage[T1]{fontenc}
\usepackage{lmodern}
\usepackage{amsmath,amssymb,amsthm,mathtools}
\usepackage[margin=1.05in]{geometry}
\usepackage{microtype,fancyhdr,tikz,needspace}
\usetikzlibrary{arrows.meta}
\definecolor{linkblue}{RGB}{24,45,111}
\usepackage[colorlinks=true,allcolors=blue]{hyperref}
\newcommand{\C}{\mathbb C}
\newcommand{\R}{\mathbb R}
\newcommand{\D}{\mathbb D}
\newcommand{\T}{\mathbb T}
\newcommand{\cC}{\mathcal C}
\newcommand{\cH}{\mathcal H}
\newcommand{\M}{\mathsf M}
\newcommand{\HS}{\mathrm{HS}}
\DeclareMathOperator{\tr}{tr}
\DeclareMathOperator{\vecop}{vec}
\DeclareMathOperator{\dist}{dist}
\DeclareMathOperator{\diag}{diag}
\DeclareMathOperator{\spec}{spec}
\newtheorem{theorem}{Theorem}[section]
\newtheorem{corollary}[theorem]{Corollary}
\newtheorem{proposition}[theorem]{Proposition}
\newtheorem{lemma}[theorem]{Lemma}
\theoremstyle{definition}
\theoremstyle{remark}
\newtheorem{remark}[theorem]{Remark}
\numberwithin{equation}{section}
\pagestyle{fancy}\fancyhf{}
\fancyhead[L]{\small The complete Crouzeix theorem}
\fancyhead[R]{\small Structural route}
\fancyfoot[C]{\thepage}
\setlength{\headheight}{14pt}
\setlength{\emergencystretch}{2em}
\hypersetup{pdftitle={The complete Crouzeix theorem: optimal similarity and a common positive boundary representation},pdfauthor={OpenAI}}
\title{The complete Crouzeix theorem:\\
optimal similarity and a common positive boundary representation}
\author{OpenAI}
\date{September 23, 2026}
\begin{document}
\maketitle\thispagestyle{fancy}

\begin{abstract}
We resolve the complete Crouzeix conjecture by proving the sharp
constant-two numerical-range inequality for every bounded operator on a
complex Hilbert space and every matrix-valued polynomial. No separability
assumption is needed. The closure of the numerical range is a complete
$2$-spectral set, and the bound extends to finite matrix-valued functions
holomorphic near that closure. For a finite matrix and a bounded convex
domain containing its numerical range with regular real-analytic Jordan
boundary, the optimal similarity making its conformal disk image contractive
is attained with condition number at most two. For the similar matrix, one
continuous positive boundary density of mass the identity represents the
evaluation of every matrix-valued function holomorphic near the closed domain.
\end{abstract}

\section{The structural question}
Can one choose a single controlled change of inner product and a single
positive boundary density to represent all matrix-valued analytic evaluations
of a matrix? We answer this question on an analytic convex neighborhood of
its numerical range. The metric and density depend on the matrix and the
enclosing domain, but neither depends on the coefficient size or the function
being evaluated. The resulting complete inequality also holds for every
bounded operator on an arbitrary complex Hilbert space, by a finite
compression argument in Section~\ref{sec:limit}.

\subsection*{Coordinates and evaluation}
Write $\D=\{z\in\C:|z|<1\}$ and $\T=\partial\D$, with normalized
angular measure $d\sigma(e^{i\theta})=d\theta/(2\pi)$. For
$A\in M_n(\C)$ its numerical range is
\[
 W(A)=\{x^*Ax:x\in\C^n,\ x^*x=1\}.
\]
All operator norms are Hilbert-space operator norms, and tensor products are
Hilbert tensor products with the base space first. For a matrix-valued function $v$
holomorphic near the spectrum, $v[A]$ denotes holomorphic evaluation:
on a Jordan block $J=\beta I+N$ of size $s$ it is
$\sum_{j=0}^{s-1}N^j\otimes v^{(j)}(\beta)/j!$, followed by the
change of basis on the first factor. In particular,
$v[A]=\sum_jA^j\otimes B_j$ when $v(z)=\sum_jB_jz^j$.
Inner products are conjugate-linear in the first argument, and $U\preceq V$
means that $V-U$ is positive semidefinite. The symbol ${}^*$ denotes the
adjoint on a base or coefficient Hilbert space, ${}^{\mathsf T}$ ordinary
transpose, and ${}^\dagger$ the adjoint of an operator on a function space.

Call $\Omega$ \emph{admissible} when it is a bounded open convex subset of
$\C$ with regular real-analytic Jordan boundary.

\Needspace{9\baselineskip}
\begin{lemma}[Conformal coordinates]\label{lem:conformal-coordinates}
For every admissible $\Omega$ there is a conformal bijection
$f:\Omega\to\D$ such that $f$ and $f^{-1}$ extend univalently
through $\overline\Omega$ and $\overline\D$, respectively. There is also
a conformal bijection $G:\{|t|>1\}\to\C\setminus\overline\Omega$
that extends univalently to
$\{|t|>r\}\cup\{\infty\}$ for some $0<r<1$, as a sphere map, with a
simple pole at infinity and $G(\T)=\partial\Omega$. On $\T$, $tG'(t)$ is an outward normal and
$\psi=f\circ G$ is an orientation-preserving smooth circle diffeomorphism.
\end{lemma}
The complete local Riemann-mapping, harmonic-reflection, and collar argument
is in Appendix~\ref{sec:conformal-appendix}.


Fix such an $\Omega$ with $W(A)\subset\Omega$, and choose its coordinates
$f,G$ from Lemma~\ref{lem:conformal-coordinates}. Put $T=f(A)$ and define
\begin{equation}\label{eq:minimum}
 \kappa^2=\min\{\tau\in\R:I\preceq H\preceq\tau I,
                  \ T^*HT\preceq H\text{ for some }H=H^*\}.
\end{equation}
A strictly feasible pair means that $H-I$, $\tau I-H$, and
$H-T^*HT$ are all positive definite. Existence and attainment of the
minimum are part of the first conclusion.

\begin{theorem}[The optimal metric]\label{thm:structural}
For every admissible $\Omega$, every finite $n\ge1$, every
$A\in M_n(\C)$ with $W(A)\subset\Omega$, and the interior conformal
coordinate $f$ above, the problem \eqref{eq:minimum} is strictly feasible
and has an attained minimum $1\le\kappa^2\le4$. If $H$ is a minimizing
metric, then
\[
 S=H^{1/2},\qquad A'=SAS^{-1},\qquad D=Sf(A)S^{-1}=f(A')
\]
satisfy
\[
 D^*D\preceq I,\qquad \rho(D)<1,
 \qquad \|S\|\|S^{-1}\|=\kappa\le2.
\]
\end{theorem}

\begin{theorem}[A common positive representation]\label{thm:representation}
With the same $\Omega,A,f,G$ and any chosen minimizing metric in
Theorem~\ref{thm:structural}, there is one continuous function
$\Lambda:\T\to M_n(\C)$ satisfying
\[
 \Lambda(t)\succeq0,\qquad \int_\T\Lambda(t)\,d\sigma(t)=I_n,
\]
such that, for every positive integer $m$ and every $M_m(\C)$-valued
function $v$ holomorphic on a neighborhood of $\overline\Omega$,
\begin{equation}\label{eq:representation-target}
 v[A']=\int_\T\Lambda(t)\otimes v(G(t))\,d\sigma(t),
 \qquad
 \|v[A]\|\le\kappa\max_{\overline\Omega}\|v\|.
\end{equation}
The same $S$, $\Lambda$, and $\kappa$ work for all $m$ and $v$.
\end{theorem}

\subsection*{The complete inequality and previous work}
For a bounded operator $A$ on a nonzero complex Hilbert space $\mathcal H$,
write $W(A)=\{\langle x,Ax\rangle:\|x\|=1\}$. For a matrix polynomial
$P(z)=\sum_{j=0}^dB_jz^j$, with $B_j\in M_m(\C)$, put
$P[A]=\sum_{j=0}^dA^j\otimes B_j$ on $\mathcal H\otimes\C^m$.
The operator formulation of the complete Crouzeix conjecture asks whether
$\|P[A]\|\le2\sup_{W(A)}\|P\|$ holds independently of the Hilbert
space, the finite coefficient size $m$, and the degree $d$. The scalar
problem is the case $m=1$.
Theorems~\ref{thm:structural} and~\ref{thm:representation}, together with
analytic convex outer approximation, give the finite-matrix inequality in
Corollary~\ref{cor:polynomial}. Corollary~\ref{cor:hilbert} transfers it
to all bounded Hilbert-space operators, including those on nonseparable
spaces, and gives the corresponding rational and holomorphic bounds on
$\overline{W(A)}$. The optimal similarity and the common density are the
finite-dimensional structural conclusions proved before these passages.

Crouzeix formulated the scalar constant-two question in 2004 and obtained
a universal complete bound of $11.08$ in 2007
\cite{Crouzeix2004,Crouzeix2007}. Delyon and Delyon's positive integral
representations form an important part of the numerical-range method
\cite{DelyonDelyon1999}. Crouzeix and Palencia used a positive double-layer
potential and a conjugate-data Cauchy transform to obtain the complete
bound $1+\sqrt2$ \cite{CrouzeixPalencia2017}; Ransford and Schwenninger
simplified its final norm argument \cite{RansfordSchwenninger2018}.
Recent preprints by Jin, Lorist and Schwenninger, and Luo present
scalar constant-two proofs \cite{Jin2026,LoristSchwenninger2026,Luo2026}.
Lorist and Schwenninger's Theorem~3 covers bounded Hilbert-space operators;
their Section~3(iv) explains why its commutation argument does not
immediately pass to matrix coefficients. \AA hag, Czy{\.{z}}, and Virtanen
prove the complete constant-two estimate for base matrices of order at
most three, with arbitrary coefficient size
\cite[Theorem~1.1]{AhagCzyzVirtanen2026}. The present comparison retains
both matrix multiplication orders in all finite base dimensions, which
suffices for the bounded-operator consequence by compression.

The abstract connection with controlled similarity is classical. Paulsen's
similarity theorem identifies the optimal condition number with the completely
bounded norm \cite[Section 2, unnumbered theorem]{Paulsen1984Similarity};
Arveson's dilation theorem relates complete contractivity to a normal boundary
dilation \cite[Theorem 1.2.2]{Arveson1972}. For numerical-range ellipses in
base dimension two, Badea, Crouzeix, and Delyon construct a conformal similarity
with condition number at most two
\cite[Theorem 5.2 and Corollary 5.3]{BadeaCrouzeixDelyon2006}.
Here we construct the minimizing metric, its endpoint extremal data, and the
continuous density in a fixed boundary parameter, and prove $\kappa\le2$
for the optimal metric constant in \eqref{eq:minimum}.

The direct proof in \cite{Direct} reaches the polynomial inequality
from the singular vectors of the polynomial being evaluated. Its exterior
kernel and original-matrix resolvent calculations also occur here, with
complete local proofs. The present argument instead chooses one optimal
metric first and proves a representation valid for every coefficient size
and every analytic test function. The two manuscripts have separate
complete proof paths.

\subsection*{How the two conclusions are proved}
Section~\ref{sec:metric} first attains the metric minimum and constructs
its positive disk density before estimating $\kappa$. The boundary change
of coordinates
\[
 t\in\T\ \xrightarrow{\ G\ }\ G(t)\in\partial\Omega
 \ \xrightarrow{\ f\ }\ \psi(t)\in\T
\]
has a positive angular Jacobian. Including it in the density gives
$\Lambda$. Its mass-one identity makes the map
$b\mapsto[t\mapsto(\Lambda(t)^{1/2}\otimes I_m)b]$ an isometric
embedding of $\C^n\otimes\C^m$ into boundary $L^2$ functions.
Multiplying there by $I_n\otimes v(G(t))$ and applying the embedding's
adjoint gives $v[A']$. This is the common compression at every coefficient size.
Figure~\ref{fig:coordinates} displays the two boundary parameters.

\input{figures/coordinates}


If $\kappa>1$, finite-dimensional separation supplies unit vectors
$x,y\in\C^n\otimes\C^n$ in the $\kappa$ and $1$ eigenspaces of
$S\otimes I_n$, respectively. A unitary realization gives a contractive
$M_n(\C)$-valued disk function $F_\D$ with $F_\D[D]x=y$.
This auxiliary function has coefficient
size $n$; its role is to test one base-space metric, not to restrict the
independently chosen target size $m$.

Once the extremal vectors are available, Section~\ref{sec:inputs}
introduces the local boundary tools needed to compare them: the exterior
kernel, the actual Cauchy adjoint, both analytic multiplication orders,
and the positive resolvent of the original $A$. In
Section~\ref{sec:bridge}, equality in the common compression gives the
forward and adjoint relations between the
boundary vectors $x_\Lambda(t)=(\Lambda(t)^{1/2}\otimes I_n)x$ and
$y_\Lambda(t)=(\Lambda(t)^{1/2}\otimes I_n)y$.
Partial traces of their outer products sum the diagonal base-space blocks,
leaving coefficient-space matrix fields. An ordinary transpose fixed by
the tensor convention identifies their means, including an entirely
vanishing matrix cross mean. The original-$A$ resolvent produces
a second positive block. Analytic and adjointed cross tests relate the
two blocks with factors $\kappa$ and $\kappa^{-1}$, respectively.

The decisive comparison is between the cross density and the two diagonal
densities in this second positive block. We use boundary $L^2$ norms formed
with the Hilbert--Schmidt matrix norm. Positivity bounds twice the squared
norm of the cross density by the sum of the squared norms
of the diagonal densities. Both diagonal norms are controlled by the same
nonzero projected cross density from the first system. The zero matrix mean
separates the two projected cross terms into orthogonal Fourier subspaces,
so the factor $\kappa$ gives a lower bound for the second cross density.
Section~\ref{sec:comparison} combines these bounds to prove $\kappa\le2$.
This completes the metric theorem and returns to
the common density at every target size. Section~\ref{sec:limit} applies
the result to polynomials and passes to arbitrary finite-matrix numerical
ranges, including points and segments. It then uses finite compressions
and holomorphic approximation to obtain the complete inequality for bounded
operators on arbitrary complex Hilbert spaces.
Appendix~\ref{sec:conformal-appendix}
provides the full local conformal construction used throughout.

\section{The metric, its representation, and its extremal data}\label{sec:metric}
\subsection{A metric for the disk coordinate}
The evaluation rules used below follow directly from the finite Jordan
Taylor formula. Its product rule preserves the order of matrix coefficients;
conjugating the Jordan form proves similarity on the base factor. For scalar
composition, substitute the nilpotent matrix $f(J)-f(\beta)I$ into the
Taylor series of the outer function at $f(\beta)$. The finite Taylor
composition identity gives $(v\circ f)[J]=v[f(J)]$, and the same formula
gives $\spec(f(A))=f(\spec(A))$. No diagonalizability is assumed.
The Jordan resolvent expansion and Cauchy's derivative formula give the
equivalent contour-integral evaluation.

Since $\spec(A)\subset W(A)\subset\Omega$, spectral mapping gives
$\rho(T)<1$. The positive-metric feasibility criterion is classical
\cite[Theorem 1]{Stein1952}; we construct the strictly feasible witness.
Choose $\rho(T)<\eta<1$. Jordan normal form supplies
$C_\eta$ with $\|T^j\|\le C_\eta\eta^j$. Hence
\[
 H_0=\sum_{j\ge0}T^{*j}T^j
\]
converges in norm, $H_0\succeq I$, and $H_0-T^*H_0T=I$.
For $c>1$ and $\tau>\|cH_0\|$, the pair $(\tau,cH_0)$ has all
three matrix slacks in \eqref{eq:minimum} positive definite. This is
strict feasibility of the optimization problem. Feasible pairs below any
fixed feasible upper bound form a closed bounded subset of a finite-dimensional
space, so a minimum is attained. Every feasible $\tau$ is at least one.

Fix a minimizing $H$ and put $S=H^{1/2}$. Congruence gives
$D^*D=S^{-1}T^*HTS^{-1}\preceq I$; similarity gives $\rho(D)<1$.
The inequalities $I\preceq H\preceq\kappa^2I$ give
$\|S\|\|S^{-1}\|\le\kappa$. The optimizer itself may have zero
slacks. In particular $\|D\|=1$ is allowed.

The minimum also measures the best condition number of a similarity to
a contraction. If $R$ is invertible and $\|RTR^{-1}\|\le1$, then
$H_R=R^*R$ satisfies $T^*H_RT\preceq H_R$. Dividing $H_R$ by its
least eigenvalue gives a feasible metric with
$\tau=\|R\|^2\|R^{-1}\|^2$. Consequently
$\kappa\le\|R\|\|R^{-1}\|$. Applying this to the minimizing
$S=H^{1/2}$, for which the reverse inequality was just proved, gives
\begin{equation}\label{eq:optimal-similarity}
 \kappa=\min\{\|R\|\|R^{-1}\|:
 R\text{ invertible},\ \|RTR^{-1}\|\le1\}.
\end{equation}
The minimum is attained by the positive matrix $S$, with
$\|S\|\|S^{-1}\|=\kappa$. This identity holds for any fixed finite
$T$ with an attained feasible metric problem; the stability assumption
above supplies such feasibility. The bound $\kappa\le2$ proved below
uses the additional conformal and numerical-range hypotheses.

\subsection{One density for every coefficient size}
\begin{proposition}[One density for every coefficient size]\label{prop:density}
For the fixed minimizing metric, the representation
\eqref{eq:representation-target} holds, before any bound on $\kappa$ is
proved, with
\begin{align}
 \Phi_D(\zeta)&=(I-D/\zeta)^{-1}+[(I-D/\zeta)^{-1}]^*-I,
                                                        \label{eq:phi}\\
 j(t)&=\frac{tG'(t)f'(G(t))}{\psi(t)}>0,
 &\Lambda(t)&=j(t)\Phi_D(\psi(t)).                      \label{eq:lambda}
\end{align}
\end{proposition}
The disk-resolvent formula is the positive representation of
Delyon and Delyon \cite[Section 2, equation (7)]{DelyonDelyon1999};
the common compression also belongs to the dilation tradition
\cite[Theorem I]{SzNagy1953}. We express the density in the exterior
parameter and prove every coefficient-size claim.
\begin{proof}
For $|\zeta|=1$, $E_\zeta=I-D/\zeta$ is invertible and
\[
 E_\zeta^*\Phi_D(\zeta)E_\zeta=I-D^*D\succeq0.
\]
Thus $\Phi_D$ is positive and continuous. The strict spectral-radius
bound, rather than a strict norm bound, implies $\sum_{j\ge0}\|D^j\|<\infty$.
Consequently the following series is absolutely uniformly convergent on
the circle:
\[
 \Phi_D(\zeta)=I+\sum_{j\ge1}(\zeta^{-j}D^j+\zeta^jD^{*j}),
 \qquad \int_\T\zeta^j\Phi_D(\zeta)\,d\sigma(\zeta)=D^j
 \quad(j\ge0).
\]
For any $m$ and any $M_m$-valued $h$ holomorphic near $\overline\D$,
integration of its uniformly convergent Taylor series gives
\[
 h[D]=\int_\T\Phi_D(\zeta)\otimes h(\zeta)\,d\sigma(\zeta).
\]
Apply this with $h=v\circ f^{-1}$. The conformal collar makes $h$
holomorphic near $\overline\D$, and scalar composition gives $h[D]=v[A']$.
Locally writing $\psi(e^{i\theta})=e^{i\eta(\theta)}$ shows that
$j(e^{i\theta})=\eta'(\theta)>0$. Changing variables
$\zeta=\psi(t)$ proves the first identity in
\eqref{eq:representation-target}. The zeroth moment gives
$\int\Lambda\,d\sigma=I$.

For each $m$, define
\[
 V_m:\C^n\otimes\C^m\longrightarrow
 L^2(\T,d\sigma;\C^n\otimes\C^m),\qquad
 (V_m b)(t)=(\Lambda(t)^{1/2}\otimes I_m)b.
\]
Normalization makes $V_m$ an isometry. If $M_v$ multiplies by
$I_n\otimes v(G(t))$, then
\[
 v[A']=V_m^\dagger M_vV_m,\qquad
 \|v[A']\|\le\max_{\overline\Omega}\|v\|.
\]
Similarity on the first factor gives the remaining estimate with constant
$\kappa$. Neither the definition of $S$ nor that of $\Lambda$ depends
on $m$ or $v$.
\end{proof}

\subsection{Endpoint separation and an exact extremal}
To bound the metric, we need equality for one auxiliary matrix function.
The construction passes from real separation to a dual balance, then to
endpoint supports, and finally to a finite unitary realization.
Use the vectorization convention
\[
 \vecop(X)=\sum_{j=1}^nXe_j\otimes e_j,\qquad
 \|\vecop(X)\|^2=\tr(XX^*).
\]

\begin{proposition}[Endpoint extremal]\label{prop:extremal}
If $\kappa>1$, there are $X,Y\in M_n(\C)$ with
\[
 \tr(XX^*)=\tr(YY^*)=1,\qquad SX=\kappa X,\qquad SY=Y,
 \qquad X^*Y=0,
\]
and an $M_n$-valued rational function $F_\D$, holomorphic on a neighborhood
of $\overline\D$ and contractive on $\overline\D$, such that, for
$x=\vecop(X)$ and $y=\vecop(Y)$,
\[
 F_\D[D]x=y.
\]
In particular $F_\Omega=F_\D\circ f$ is holomorphic near
$\overline\Omega$ and satisfies $F_\Omega[A']x=y$. Its boundary trace
$F=F_\Omega\circ G$ is contractive.
\end{proposition}
\begin{proof}
We first obtain positive matrices $X_0$ and $Y_0$ supported on the
$\kappa^2$ and $1$ eigenspaces of $H$, respectively. A third positive
matrix $Z_0$ will express their difference as $Z_0-TZ_0T^*$; this balance
will provide the equal Gram matrices needed for the unitary realization.

\emph{Separation, including a possible contact point.}
In the real vector space $\R\oplus\operatorname{Herm}_n^3$, the affine set
\[
 \mathcal A_T=\{(s,J-I,sI-J,J-T^*JT):s\in\R,\ J=J^*\}
\]
is disjoint from the open convex set
\[
 \mathcal O=\{(s,U,V,W):s<\kappa^2,\ U,V,W\succ0\}.
\]
Here is the finite-dimensional separation argument used for these sets;
the general convex-separation framework is treated in
\cite[Section 11, Theorem 11.2]{Rockafellar1970}.
Write $\mathcal A_T=a_0+L$, and let $\pi$ project orthogonally onto
$L^\perp$. The set $\mathcal K=\pi(\mathcal O-a_0)$ is nonempty, open
in $L^\perp$, and convex, and it does not contain zero. If
$0\notin\overline{\mathcal K}$, a nearest point $z_0$ in the closed convex
set $\overline{\mathcal K}$ satisfies
$\langle z_0,c\rangle\ge\|z_0\|^2>0$ for every $c\in\mathcal K$.

If $0\in\overline{\mathcal K}$, fix $c_*\in\mathcal K$ and set
$z_j=-c_*/j$. Each $z_j$ is outside $\overline{\mathcal K}$: otherwise
zero would lie on the open segment joining an interior point $c_*$ to a
point of the closure, and hence would belong to $\mathcal K$. To verify
that segment fact, take a ball about $c_*$ inside $\mathcal K$, approximate
the other endpoint by points of $\mathcal K$, and use convexity; a ball
about each fixed interior point of the limiting segment is still contained
in $\mathcal K$. Let $y_j$ be nearest to $z_j$ in
$\overline{\mathcal K}$. Since zero belongs to this closed set,
$\|y_j-z_j\|\le\|z_j\|$, so $y_j\to0$. A subsequence of
$\nu_j=(y_j-z_j)/\|y_j-z_j\|$ tends to a unit vector $\nu$.
The nearest-point inequality gives
$\langle\nu_j,c-y_j\rangle\ge0$, hence
$\langle\nu,c\rangle\ge0$ for every $c\in\mathcal K$.
In the first case use $\nu=z_0$. In either case
$\ell(v)=-\langle\nu,\pi v\rangle$ is nonzero and
$\ell(a)\ge\ell(o)$ for all $a\in\mathcal A_T$, $o\in\mathcal O$.

Because $\mathcal A_T$ is affine, $\ell$ is constant on it. Boundedness
above on $\mathcal O$ forces the signs
\[
 \ell(s,U,V,W)=\lambda s-\tr(Y_0U)-\tr(X_0V)-\tr(Z_0W),
 \quad\lambda\ge0,\quad X_0,Y_0,Z_0\succeq0.
\]
If $\lambda=0$, strict feasibility produces a negative value on
$\mathcal A_T$, while separation requires a value at least
$\sup_{\mathcal O}\ell=0$. Thus $\lambda>0$; scale it to one.
Constancy on $\mathcal A_T$ then gives
\begin{equation}\label{eq:dual}
 X_0-Y_0=Z_0-TZ_0T^*,\qquad \tr X_0=1.
\end{equation}
The constant value is $\tr Y_0\ge\kappa^2$. At $(\kappa^2,H)$ it is
\[
 \kappa^2-\tr(Y_0(H-I))-\tr(X_0(\kappa^2I-H))
            -\tr(Z_0(H-T^*HT))\le\kappa^2.
\]
Each subtracted trace is nonnegative, so all vanish and
$\tr Y_0=\kappa^2$.

\emph{Endpoint support and balance.}
Write
$\|B\|_{\HS}=(\tr(B^*B))^{1/2}$ for the unnormalized
Hilbert--Schmidt norm. For positive matrices $B,C$,
$\tr(BC)=\|C^{1/2}B^{1/2}\|_{\HS}^2$; vanishing implies that the
range of $B$ lies in the kernel of $C$. Therefore $X_0$ is supported on
the $\kappa^2$ eigenspace of $H$, and $Y_0$ on its $1$ eigenspace.

Choose square factors and a positive matrix $Q$ by
\[
 XX^*=\kappa^{-2}SX_0S,\quad
 YY^*=\kappa^{-2}SY_0S,\quad Q=\kappa^{-2}SZ_0S.
\]
The support and trace relations give the asserted norms and endpoint
identities. Their column ranges are orthogonal because $\kappa>1$,
so $X^*Y=0$ as a matrix. Congruence of \eqref{eq:dual} gives
\begin{equation}\label{eq:balance}
 XX^*-YY^*=Q-DQD^*.
\end{equation}

\emph{Unitary realization and transpose.}
The balance-to-isometry step is the classical interpolation mechanism of
\cite[Section~3 of the versioned preprint]{KatsnelsonKheifetsYuditskii1997}; its particular endpoint
data and finite-dimensional realization are established here.
Put $L=Q^{1/2}$. The rows $R_1=[L\ Y]$ and $R_2=[DL\ X]$ have
equal products with their adjoints. The map
$R_2^*v\mapsto R_1^*v$ is therefore a well-defined isometry of their
ranges. Extend it to a unitary using equal-dimensional orthogonal
complements, then take its adjoint. This yields
\[
 [L\ Y]=[DL\ X]
 \begin{pmatrix}a&b\\c&d\end{pmatrix},\qquad
 U=\begin{pmatrix}a&b\\c&d\end{pmatrix}\text{ unitary}.
\]
Thus $L=DLa+Xc$ and $Y=DLb+Xd$. Since $\|a\|\le1$ and
$\rho(D)<1$, iteration gives the norm-convergent identity
\begin{equation}\label{eq:realization-series}
 Y=Xd+\sum_{j\ge0}D^{j+1}Xca^jb.
\end{equation}
The transfer-function norm identity is the unitary-colligation identity
of \cite[Section 3.1, equations (3.1)--(3.4)]{Brodskii1978}.
Define, for $|\zeta|<1$,
\[
 R(\zeta)=d+\zeta c(I-\zeta a)^{-1}b,
 \qquad F_\D(\zeta)=R(\zeta)^{\mathsf T}.
\]
For $e\in\C^n$ and $v=(I-\zeta a)^{-1}be$, unitarity gives
\[
 U\binom{\zeta v}{e}=\binom{v}{R(\zeta)e},\qquad
 \|e\|^2-\|R(\zeta)e\|^2=(1-|\zeta|^2)\|v\|^2\ge0.
\]
Hence $R$ is contractive. Ordinary transpose preserves its norm and
holomorphy. Its rational entries are bounded in $\D$, so every apparent
pole on $\T$ is removable: a genuine pole would diverge on an interior
radial approach. After cancellation, finitely many remaining poles stay
away from $\overline\D$. This supplies a common neighborhood of that
closed disk on which $F_\D$ is holomorphic; continuity retains
contractivity on the circle.

Finally,
\[
 (D^k\otimes B)\vecop(X)=\vecop(D^kXB^{\mathsf T}).
\]
The Taylor coefficients of $F_\D$ are the transposes of $d$ and
$ca^jb$. Substitution in \eqref{eq:realization-series} proves
$F_\D[D]x=y$. The conformal collar and scalar composition give the
claims for $F_\Omega$. Rationality is asserted in the disk variable;
$F_\Omega$ is only required to be holomorphic near $\overline\Omega$.
\end{proof}

\section{Local boundary tools}\label{sec:inputs}
We now prepare the comparison that will bound the optimal metric. The
exterior coordinate supplies a positive kernel with two normalized marginals.
Its Fourier action controls a Cauchy projection, while the original numerical
range supplies a second positive density. We prove the shared exterior and
resolvent calculations here. They also form the analytic part of the direct
polynomial proof \cite[Sections 2--3]{Direct}; each required argument is
included in the present paper. A reader who has checked
\cite[Theorems~2.1 and~3.1]{Direct} may compare the statement of
Proposition~\ref{input:analytic} using the notation in
Remark~\ref{rem:correspondence}, and then resume at the physical Cauchy
integral preceding Proposition~\ref{prop:projection}. The projection
proof and its ordered applications remain part of the present argument.

\begin{proposition}[Exterior coefficients and the original-matrix resolvent]\label{input:analytic}
Assume the admissible $\Omega$ and the exterior map $G$ supplied above.
Write $G(t)=at+b+O(t^{-1})$ at infinity, where $a\ne0$, and
$q_G(t)=tG'(t)$. There are scalar polynomials
$b_k$, with $b_0=1$, $\deg b_k=k$, and leading coefficient $a^{-k}$,
defined by
\begin{equation}\label{eq:import-faber}
 \frac{q_G(t)}{G(t)-z}=\sum_{k\ge0}b_k(z)t^{-k}
 \quad\text{at infinity}.
\end{equation}
There is also the mixed expansion
\begin{equation}\label{eq:import-kernel}
 B(w,t)=\frac{q_G(t)}{G(t)-G(w)}-\frac{t}{t-w}
       =\sum_{i,j\ge1}\beta_{ij}w^{-i}t^{-j},
 \qquad
 b_j(G(w))=w^j+\sum_{i\ge1}\beta_{ij}w^{-i}\quad(j\ge1).
\end{equation}
Here $B$ is holomorphic through the diagonal and both infinities of the
exterior product collar. For each $r<\rho<1$ there is a constant
$C_\rho$ such that $|\beta_{ij}|\le C_\rho\rho^{i+j}$; the series
converges normally on the product collar and absolutely uniformly on
$\T^2$. The kernel
\[
 m(w,t)=1+B(w,t)+\overline{B(w,t)}
\]
is continuous and nonnegative, with each normalized-circle marginal one.

For every finite $n$ and every original matrix $A\in M_n(\C)$ with
$W(A)\subset\Omega$,
\begin{equation}\label{eq:import-resolvent}
 K_A(t)=q_G(t)(G(t)I-A)^{-1}
       =\sum_{k\ge0}b_k(A)t^{-k},\qquad
 E_A(t)=K_A(t)+K_A(t)^*\succeq0\quad(t\in\T).
\end{equation}
Its coefficients decay geometrically and its series converges absolutely
uniformly on $\T$.
The scalar case applies to every fixed $z\in\Omega$.
\end{proposition}
\begin{proof}
Expand \eqref{eq:import-faber} at infinity after factoring $at$ from the
denominator. The constant term is one; the coefficient of $t^{-k}$ is a
polynomial of degree $k$ with leading term $a^{-k}z^k$.

For the joint continuation, put
\[
 Q(w,t)=\frac{G(t)-G(w)}{t-w}.
\]
Write $u=t^{-1}$, $v=w^{-1}$, and $G(t)=at+g(u)$, with $g$
holomorphic for $|u|<r^{-1}$. Then
\[
 Q=a-uv\frac{g(u)-g(v)}{u-v}.
\]
The divided difference is jointly holomorphic, with its derivative value
on the diagonal. Off the finite diagonal, $Q\ne0$ by univalence of
$G$; on that diagonal $Q=G'(t)\ne0$; on either reciprocal axis,
including their intersection, $Q=a\ne0$. Consequently
\[
 B(w,t)=t\frac{\partial_tQ(w,t)}{Q(w,t)}
        =-u\frac{\partial_uQ}{Q}
\]
is holomorphic on the reciprocal bidisk and vanishes on both axes.
Its Taylor series has only the strictly mixed powers in
\eqref{eq:import-kernel}. Cauchy estimates on the closed reciprocal
bidisk of radius $\rho^{-1}$ give
$|\beta_{ij}|\le C_\rho\rho^{i+j}$ for every $r<\rho<1$.
For a compact subset of the product collar, choose $\rho$ above $r$
but smaller than one and than the moduli of both coordinates on that
compact set. The estimate then dominates the double series by a product
of convergent geometric series. This proves normal convergence throughout
the product collar, including at infinity, and absolute uniform convergence
on $\T^2$.
Comparing coefficients at $t=\infty$ in the defining identity for $B$,
first with fixed finite $w$ in the collar, gives the displayed boundary
formula for $b_j\circ G$.

For distinct $w,t\in\T$, the circle identity
$2\operatorname{Re}(t/(t-w))=1$ gives
\[
 m(w,t)=2\operatorname{Re}\frac{q_G(t)}{G(t)-G(w)}\ge0.
\]
Indeed $q_G(t)$ is the outward normal, so convexity gives
$\operatorname{Re}(\overline{q_G(t)}(G(t)-G(w)))\ge0$.
Continuity of the mixed-series expression supplies the same sign on the
diagonal. Every term in $B$ and its conjugate has nonzero frequency in
each variable, so integration in either variable leaves exactly one.

For the matrix resolvent, every eigenvalue of $A$ lies in $W(A)$ by
testing a unit eigenvector. Thus $G(t)I-A$ is invertible on and outside
the circle. Compactness of the circle permits a smaller exterior collar
on which the resolvent remains holomorphic, including infinity where
$K_A(\infty)=I$. Expanding for large $|t|$ gives the coefficients
$b_k(A)$ by the same polynomial identities as \eqref{eq:import-faber}.
Cauchy estimates in the reciprocal disk give geometric decay and
absolute uniform convergence on $\T$.

Finally put $R_t=G(t)I-A$. Direct congruence gives
\[
 R_t^*(K_A+K_A^*)R_t=q_G(t)R_t^*+\overline{q_G(t)}R_t.
\]
At a unit vector $x$, its quadratic form is
$2\operatorname{Re}(\overline{q_G(t)}(G(t)-x^*Ax))\ge0$,
by the supporting half-plane and $W(A)\subset\Omega$.
Invertibility of $R_t$ proves $E_A\succeq0$.
\end{proof}

These local double-layer calculations belong to the numerical-range
method of Delyon--Delyon and Crouzeix--Palencia
\cite{DelyonDelyon1999,CrouzeixPalencia2017}.
The polynomials $b_k$ are the classical Faber polynomials
\cite{Beckermann2005,BeckermannCrouzeix2014}. Indeed, putting
$\Phi=G^{-1}$ in the exterior, \eqref{eq:import-kernel} gives
$b_k(z)-\Phi(z)^k=O(z^{-1})$ at infinity; hence $b_k$ is the
polynomial part of $\Phi^k$. The mixed coefficients $\beta_{ij}$ are
differentiated Grunsky coefficients, as the logarithmic derivative of $Q$
in the proof shows. The classical coefficient normalization gives a
weighted inequality \cite[equations (1.1)--(1.3)]{BeckermannStylianopoulos2018};
the unweighted Hilbert--Schmidt contraction used here follows locally
from convexity and the two angular marginals.

We next turn this kernel into a bounded Cauchy projection on boundary
functions. For the density comparison we need estimates for its actual
adjoint and a formula relating Laurent tests to the original-matrix field
$E_A$.

For every integer $k\ge1$, use
\[
 \cH_k=L^2(\T,d\sigma;M_k(\C)),\qquad
 \langle u,v\rangle=\int_\T\tr(u^*v)\,d\sigma,
 \qquad\|u\|_2^2=\langle u,u\rangle.
\]
The pointwise norm is the unnormalized Hilbert--Schmidt norm. Let
$P_0,P_+,P_-$ be the orthogonal Fourier projections onto the constant,
strictly positive, and strictly negative frequencies, respectively, and write
$u=u_0+u_++u_-$ with $u_0=P_0u$, $u_+=P_+u$, $u_-=P_-u$.
Define
\[
 (\M u)(w)=\int_\T m(w,t)u(t)\,d\sigma(t).
\]

\begin{remark}[Correspondence with the direct proof]\label{rem:correspondence}
A reader who has already checked the exterior calculations in
\cite[Theorems~2.1 and~3.1]{Direct} can compare the conventions by setting
$h=G$, $\lambda=t$, $\mu=w$. Its correction satisfies
$s(\lambda,\mu)=B(\mu,\lambda)$ and $s_{kj}=\beta_{jk}$.
The resulting integral action is the same $\M$, not its
Hilbert adjoint. The local proof above is complete; readers familiar with
that calculation can continue with the physical Cauchy interpretation below.
\end{remark}

For continuous matrix-valued boundary data $u$, define the physical
Cauchy integral
\[
 c_u(z)=\int_\T u(t)\frac{q_G(t)}{G(t)-z}\,d\sigma(t),\qquad z\in\Omega.
\]
For finite Laurent data, the scalar case of \eqref{eq:import-resolvent}
allows termwise integration for every fixed $z\in\Omega$.
If $u(t)=\sum_jU_jt^j$ is finite, it gives
\begin{equation}\label{eq:local-bridge}
 c_u(z)=\sum_{j\ge0}b_j(z)U_j.
\end{equation}
Thus $c_u$ is an entire polynomial, and the physical integral of $t^j$
is $b_j$ for $j\ge0$, zero for $j<0$. The boundary trace is taken
\emph{after} this interior identity is proved; no singular boundary
substitution in the integral is needed.

\begin{proposition}[The local projection theorem]\label{prop:projection}
For finite Laurent data $u$, the polynomial $c_u$ has boundary trace
$\cC u=c_u\circ G$. This map extends to a bounded projection on every
$\cH_k$. With $\widetilde\cC u=(\cC(u^*))^*$, one has
\[
 \cC=P_0+P_++\M P_+,\qquad
 \widetilde\cC u=(\cC(u^*))^*.
\]
Its actual Hilbert-space adjoints satisfy
\begin{equation}\label{eq:adjoints}
 \cC^\dagger u=u_0+u_++\M^\dagger u_-,\qquad
 \widetilde\cC^\dagger u=u_0+u_-+\M^\dagger u_+
                         =(\cC^\dagger(u^*))^*.
\end{equation}
All four operators preserve the mean, and
\begin{equation}\label{eq:weighted}
 \|\cC^\dagger u\|_2^2+\|(\cC^\dagger u)_0\|_2^2
 \le2\|u\|_2^2\qquad(u\in\cH_k).
\end{equation}
If $F=F_\Omega\circ G$ with $F_\Omega$ holomorphic near
$\overline\Omega$ and $M_k$-valued, then for every $u\in\cH_k$,
\begin{equation}\label{eq:modules}
 \cC(F\cC u)=F\cC u,\qquad
 \cC((\cC u)F)=(\cC u)F.
\end{equation}

For every finite coefficient size and every matrix Laurent polynomial $u$,
\begin{equation}\label{eq:resolvent-contract}
 \int_\T E_A\otimes u\,d\sigma
 =c_u[A]+c_{u^*}[A]^*.
\end{equation}
In particular, $\int E_A\,d\sigma=2I_n$.
\end{proposition}
\begin{proof}
Positivity and the two marginal identities give the contraction locally:
Jensen's inequality at each $w$ and then integration imply
\[
 \|(\M u)(w)\|_{\HS}^2
 \le\int_\T m(w,t)\|u(t)\|_{\HS}^2\,d\sigma(t),
 \qquad \|\M u\|_2\le\|u\|_2.
\]
The mixed expansion in \eqref{eq:import-kernel} gives, for $j>0$,
\[
 \M(t^j)(w)=\sum_{i\ge1}\beta_{ij}w^{-i},\qquad
 \M(t^{-j})(w)=\sum_{i\ge1}\overline{\beta_{ij}}w^i.
\]
Both marginal identities say that $\M$ fixes constants and preserves
means. The real kernel makes it commute with pointwise matrix adjoint.
Its actual adjoint has kernel $m(t,w)$, and hence, for $i>0$,
\[
 \M^\dagger(t^{-i})(w)=\sum_{j\ge1}\overline{\beta_{ij}}w^j,
 \qquad
 \M^\dagger(t^i)(w)=\sum_{j\ge1}\beta_{ij}w^{-j}.
\]
It is a contraction, fixes constants, preserves means, and commutes with
pointwise adjoint. No symmetry of $m$ is used.
By boundedness and density of Fourier polynomials, the displayed actions
extend to the closed strictly positive and strictly negative Fourier subspaces.

Equations \eqref{eq:import-kernel} and \eqref{eq:local-bridge} give
$\cC u=u_0+u_++\M u_+$ for finite Laurent data. The three terms
are orthogonal, so $\|\cC u\|_2^2\le2\|u\|_2^2$. Density
defines the bounded extension, and the same formula gives $\cC^2=\cC$.
Taking its adjoint and using the strict Fourier exchange proves
\eqref{eq:adjoints}; conjugation by the antiunitary map $u\mapsto u^*$
gives the second formula. The weighted estimate follows from
\[
 \|\cC^\dagger u\|_2^2+\|(\cC^\dagger u)_0\|_2^2
 =2\|u_0\|_2^2+\|u_++\M^\dagger u_-\|_2^2
 \le2\|u\|_2^2.
\]

We need the physical interpretation also for analytic boundary traces.
If $v=v_\Omega\circ G$ and $v_\Omega$ is holomorphic near
$\overline\Omega$, then $v$ is holomorphic on an annulus about $\T$.
On a smaller closed annulus its Laurent series converges absolutely
uniformly. If $r<|w|<1$, then $G(w)\in\Omega$: an exterior or
boundary value would also have a preimage with modulus at least one,
contradicting univalence on the collar. For $|w|<1$ sufficiently close
to one, expansion of
$t/(t-w)+B(w,t)$ in the Cauchy integral gives
\[
 c_v(G(w))=\sum_{j\ge0}v_jw^j+
             \sum_{i,j\ge1}\beta_{ij}w^{-i}v_j.
\]
The series converge uniformly after shrinking the annulus again, by
the geometric Laurent bounds for $v_j$ and the normally convergent
mixed expansion. At the boundary the expression is $\cC v$.
Cauchy's formula gives $c_v=v_\Omega$ in $\Omega$, and thus
$\cC v=v$ on $\T$. For Laurent data $u$, both $F_\Omega c_u$ and
$c_uF_\Omega$ are holomorphic near $\overline\Omega$ by
\eqref{eq:local-bridge}. Their traces are fixed by $\cC$, giving both
identities in \eqref{eq:modules} for finite Laurent $u$. Left and right
multiplication by the bounded $F$ are bounded on $\cH_k$; Laurent
approximation extends the two identities to arbitrary $u\in\cH_k$.

Lastly, integrating \eqref{eq:import-resolvent} against a finite Laurent
polynomial gives
\[
 \int_\T K_A\otimes u\,d\sigma
 =\sum_{j\ge0}b_j(A)\otimes U_j=c_u[A]
\]
by \eqref{eq:local-bridge} and the prescribed base-first evaluation.
Applying the same formula to $u^*$ and taking the full matrix adjoint
proves \eqref{eq:resolvent-contract}. The constant case gives mass $2I_n$.
\end{proof}

In the density comparison below, we evaluate the physical Cauchy
representative only for the Laurent test functions in
\eqref{eq:resolvent-contract}. Arbitrary $L^2$ data
in \eqref{eq:modules} are obtained by bounded extension and density.
No continuation of a general $\cC u$ through the boundary is assumed.
Also, $E_A$ is different from the normalized density $\Lambda$ in
Proposition~\ref{prop:density}:
they have different masses and represent different expressions.

\section{From extremal vectors to two positive density systems}\label{sec:bridge}
We now return to the endpoint vectors constructed in
Proposition~\ref{prop:extremal}. The boundary tools just proved provide
two different positive systems: the mass-one density $\Lambda$ for $A'$,
and the mass-two resolvent field $E_A$ for $A$. We compare their
coefficient-space partial traces using the same vectors.
Assume $\kappa>1$ and write
$R_S=S\otimes I_n$. Then
\begin{equation}\label{eq:endpoints}
 \|x\|=\|y\|=1,\qquad R_Sx=\kappa x,\qquad R_Sy=y,
 \qquad F_\Omega[A']x=y.
\end{equation}
The partial-trace densities introduced below are $n$-by-$n$
coefficient-space matrices; $\Lambda$ and $E_A$ remain base-space fields.

\subsection{Equality in the common positive representation}
Use the isometry $V=V_n$ of Proposition~\ref{prop:density}, and set
\[
 x_\Lambda=Vx=(\Lambda^{1/2}\otimes I_n)x,\qquad
 y_\Lambda=Vy=(\Lambda^{1/2}\otimes I_n)y.
\]
Let $M_F$ multiply by $I_n\otimes F(t)$. The interpolation identity gives
\[
 1=\|V^\dagger M_FVx\|\le\|M_FVx\|\le\|Vx\|=1.
\]
Equality in the first inequality puts $M_FVx$ in the range of $V$:
the orthogonal projection $VV^\dagger$ cannot preserve the norm of a
vector with a nonzero perpendicular component. Thus $M_FVx=Vy$.
Equality in the second inequality says that the positive operator
$I-M_F^\dagger M_F$ has zero quadratic form at $Vx$, so it annihilates
$Vx$. Consequently, almost everywhere,
\begin{equation}\label{eq:fiber-equality}
 y_\Lambda=(I_n\otimes F)x_\Lambda,\qquad
 x_\Lambda=(I_n\otimes F^*)y_\Lambda.
\end{equation}

Take the partial trace over the base factor, meaning the sum of the
diagonal base-space blocks, leaving a coefficient-space matrix:
\begin{equation}\label{eq:partial-traces}
 p=\operatorname{Tr}_{\rm base}(x_\Lambda x_\Lambda^*),\quad
 q=\operatorname{Tr}_{\rm base}(y_\Lambda y_\Lambda^*),\quad
 r=\operatorname{Tr}_{\rm base}(y_\Lambda x_\Lambda^*).
\end{equation}
They are bounded, hence in $\cH_n$, and $p,q\succeq0$. To see each
multiplication order, write
$x_\Lambda=\sum_a e_a\otimes\xi_a$ and
$y_\Lambda=\sum_a e_a\otimes\eta_a$. Then
$r=\sum_a\eta_a\xi_a^*$, while \eqref{eq:fiber-equality} gives
$\eta_a=F\xi_a$ and $\xi_a=F^*\eta_a$. Therefore
\begin{equation}\label{eq:ordered-densities}
 p=F^*r,\qquad r=Fp,\qquad q=rF^*.
\end{equation}

The same convention identifies the mean without losing matrix information:
\begin{equation}\label{eq:transpose-densities}
 p=(X^*\Lambda X)^{\mathsf T},\quad
 q=(Y^*\Lambda Y)^{\mathsf T},\quad
 r=(X^*\Lambda Y)^{\mathsf T}.
\end{equation}
Indeed, the $(j,k)$ entry of the cross density is
\[
 \sum_a(\Lambda^{1/2}Y)_{aj}
       \overline{(\Lambda^{1/2}X)_{ak}}
 =(X^*\Lambda Y)_{kj}.
\]
Integrating \eqref{eq:transpose-densities} gives
\begin{equation}\label{eq:matrix-zero}
 r_0=(X^*Y)^{\mathsf T}=0,\qquad \tr(p_0)=1.
\end{equation}
Thus the entire matrix mean vanishes; the scalar identity $\tr(r_0)=0$
would not provide the Fourier orthogonality used below.

For every $u\in\cH_n$, the cross density has the testing orientation
\begin{equation}\label{eq:testing}
 \langle r,u\rangle
 =\int_\T y_\Lambda^*(I_n\otimes u)x_\Lambda\,d\sigma
 =y^*\left(\int_\T\Lambda\otimes u\,d\sigma\right)x.
\end{equation}
This follows from $\tr(r^*u)=\sum_a\eta_a^*u\xi_a$.
The diagonal formulas use $(x,x)$ for $p$ and $(y,y)$ for $q$.

\subsection{The original-matrix positive block}
Use $E_A\succeq0$ from Proposition~\ref{input:analytic}, and define
\[
 x_e=(E_A^{1/2}\otimes I_n)x,\qquad
 y_e=(E_A^{1/2}\otimes I_n)y.
\]
Define $p_e,q_e,r_e$ by the same three partial traces as in
\eqref{eq:partial-traces}, now using $x_e,y_e$.
Writing $x_e=\sum_a e_a\otimes\alpha_a$ and
$y_e=\sum_a e_a\otimes\beta_a$ yields
\begin{equation}\label{eq:positive-block}
 \Delta=\begin{pmatrix}p_e&r_e^*\\r_e&q_e\end{pmatrix}
 =\sum_a\binom{\alpha_a}{\beta_a}
          \binom{\alpha_a}{\beta_a}^{\!*}\succeq0.
\end{equation}
This positivity uses $W(A)\subset\Omega$ for the original matrix.
No numerical-range containment for $A'=SAS^{-1}$ is used.

We now identify the new densities with projected versions of the first ones.
For $M_n(\C)$-valued $v$ holomorphic near $\overline\Omega$, similarity and
\eqref{eq:endpoints} give
\begin{align}
 v[A]&=R_S^{-1}v[A']R_S,
 &v[A]^*&=R_Sv[A']^*R_S^{-1},\notag\\
 y^*v[A]x&=\kappa\,y^*v[A']x,
 &y^*v[A]^*x&=\kappa^{-1}y^*v[A']^*x.\label{eq:kappa-factors}
\end{align}
For diagonal pairings, the factors cancel for both the analytic operator
and its adjoint.

Take a matrix Laurent polynomial $u$. Its physical representative $c_u$
is holomorphic near $\overline\Omega$, so
\eqref{eq:resolvent-contract}, \eqref{eq:kappa-factors}, and
\eqref{eq:testing} give
\begin{align*}
 \langle r_e,u\rangle
 &=y^*\bigl(c_u[A]+c_{u^*}[A]^*\bigr)x\\
 &=\kappa\langle r,\cC u\rangle
       +\kappa^{-1}\langle r,\widetilde\cC u\rangle\\
 &=\langle\kappa\cC^\dagger r
          +\kappa^{-1}\widetilde\cC^\dagger r,u\rangle.
\end{align*}
In the second term the boundary test is $(\cC(u^*))^*$, which is
$\widetilde\cC u$; it is not an independent analytic function evaluated
at $A$. The corresponding diagonal computations have no similarity
factor. Since Laurent polynomials are dense in $\cH_n$, we obtain
\begin{equation}\label{eq:projected-densities}
 \begin{split}
 p_e&=\cC^\dagger p+\widetilde\cC^\dagger p,\qquad
 q_e=\cC^\dagger q+\widetilde\cC^\dagger q,\\
 r_e&=\kappa\cC^\dagger r+\kappa^{-1}\widetilde\cC^\dagger r.
 \end{split}
\end{equation}
All functions here lie in the same Hilbert--Schmidt $L^2$ space.

\section{The ordered comparison and the constant two}\label{sec:comparison}
The preceding construction supplies the hypotheses of the following
comparison. We state it for arbitrary coefficient size to expose its
dimension-free content. The comparison uses one nonzero field
$g=\cC^\dagger r$: the diagonal norms are at most $2\|g\|_2$, whereas
the cross norm is at least $\kappa\|g\|_2$. Positivity of the block then
forces $\kappa\le2$.
The proof below keeps the left and right multiplication orders separate
when obtaining the two diagonal bounds.

\begin{lemma}[Ordered density comparison]\label{lem:comparison}
Let $k\ge1$, and let $F=F_\Omega\circ G$ be $M_k$-valued, with
$F_\Omega$ holomorphic near $\overline\Omega$ and $\|F(t)\|\le1$ on
$\T$. Suppose $p,q,r\in\cH_k$ satisfy
\[
 p=p^*,\quad q=q^*,\quad p=F^*r,\quad q=rF^*,\quad
 r_0=0,\quad\tr(p_0)>0.
\]
For a positive number $\kappa$, define
\[
 p_e=\cC^\dagger p+\widetilde\cC^\dagger p,\qquad
 q_e=\cC^\dagger q+\widetilde\cC^\dagger q,\qquad
 r_e=\kappa\cC^\dagger r+\kappa^{-1}\widetilde\cC^\dagger r.
\]
If the $2k$-by-$2k$ block
\[
 \Delta(t)=\begin{pmatrix}p_e(t)&r_e(t)^*\\r_e(t)&q_e(t)\end{pmatrix}
 \succeq0
\]
for almost every $t\in\T$, then $\kappa\le2$.
\end{lemma}
\begin{proof}
Put $g=\cC^\dagger r$, $P_1=\cC^\dagger p$,
$P_2=\cC^\dagger q$. On $\cH_k$, the adjoint of left multiplication
by $F$ is left multiplication by $F^*$; the adjoint of right
multiplication is right multiplication by $F^*$, because
\[
 \tr((uF)^*v)=\tr(F^*u^*v)=\tr(u^*vF^*).
\]
Taking the Hilbert adjoints of both identities in \eqref{eq:modules}
therefore gives, with the factors on their original sides,
\begin{equation}\label{eq:ordered-projection}
 P_1=\cC^\dagger(F^*g),\qquad
 P_2=\cC^\dagger(gF^*).
\end{equation}
If $g=0$, the first identity makes $P_1=0$, contradicting mean
preservation and $\tr(p_0)>0$. Thus $g\ne0$.

Each $P_j$ has only nonnegative Fourier powers, and its mean is
Hermitian. Fourier orthogonality gives
\[
 \|P_j+P_j^*\|_2^2
 =4\|(P_j)_0\|_2^2+2\|(P_j)_+\|_2^2
 =2\bigl(\|P_j\|_2^2+\|(P_j)_0\|_2^2\bigr).
\]
Since $\|F\|\le1$, both $F^*g$ and $gF^*$ have Hilbert--Schmidt
$L^2$ norm at most $\|g\|_2$. Apply \eqref{eq:weighted} separately
to the two inputs in \eqref{eq:ordered-projection}. Using the star
relation in \eqref{eq:adjoints} and $p=p^*$, $q=q^*$, we obtain
\begin{equation}\label{eq:diagonal-bound}
 \|p_e\|_2^2\le4\|g\|_2^2,\qquad
 \|q_e\|_2^2\le4\|g\|_2^2.
\end{equation}

Put $h=\widetilde\cC^\dagger r$. Mean preservation and the whole
matrix equality $r_0=0$ put $g$ in the strictly positive Fourier
subspace and $h$ in the strictly negative one. Therefore
\begin{equation}\label{eq:cross-bound}
 \|r_e\|_2^2=\kappa^2\|g\|_2^2+\kappa^{-2}\|h\|_2^2
 \ge\kappa^2\|g\|_2^2.
\end{equation}
Finally, set $J=\diag(I_k,-I_k)$. Positivity of both $\Delta$ and
$J\Delta J$ gives
\[
 0\le\tr\bigl(\Delta^{1/2}(J\Delta J)\Delta^{1/2}\bigr)
 =\tr(\Delta J\Delta J)
 =\|p_e\|_{\HS}^2+\|q_e\|_{\HS}^2-2\|r_e\|_{\HS}^2.
\]
The entries are in $L^2$, so this inequality is integrable. Combining
it with \eqref{eq:diagonal-bound} and \eqref{eq:cross-bound} yields
\[
 2\kappa^2\|g\|_2^2\le2\|r_e\|_2^2
 \le\|p_e\|_2^2+\|q_e\|_2^2\le8\|g\|_2^2.
\]
Since $g\ne0$, division proves $\kappa\le2$.
\end{proof}

\begin{proof}[Completion of Theorems~\ref{thm:structural} and~\ref{thm:representation}]
If $\kappa=1$, the required bound already holds. Otherwise
Proposition~\ref{prop:extremal} and Section~\ref{sec:bridge} supply all
the hypotheses of Lemma~\ref{lem:comparison} at auxiliary size $k=n$:
\eqref{eq:ordered-densities} gives both multiplication orders,
\eqref{eq:matrix-zero} gives the zero matrix mean and positive trace,
\eqref{eq:positive-block} supplies positivity, and
\eqref{eq:projected-densities} identifies its entries. Hence
$\kappa\le2$. Proposition~\ref{prop:density} already used this same
metric and density for every independently chosen coefficient size $m$,
which proves all statements of the two theorems.
\end{proof}

\section{From admissible domains to bounded Hilbert-space operators}\label{sec:limit}
We first pass from admissible enclosing domains to arbitrary finite-matrix
numerical ranges. The Gaussian-distance construction below supplies the
required domains, including when the numerical range is a point or a segment.
A finite support-exponential construction gives an alternative
\cite[Section 4]{Direct}. We then transfer the polynomial estimate by finite
compression and pass to the rational and holomorphic functional calculi.

\begin{corollary}[The sharp complete polynomial inequality for matrices]\label{cor:polynomial}
For every pair of positive integers $n,m$, every $A\in M_n(\C)$,
every nonnegative integer $d$, and every choice of matrices
$B_0,\ldots,B_d\in M_m(\C)$, the polynomial
$P(z)=\sum_{j=0}^dB_jz^j$ satisfies
\[
 \|P[A]\|=\left\|\sum_{j=0}^dA^j\otimes B_j\right\|
 \le2\max_{z\in W(A)}\|P(z)\|.
\]
The constant is independent of both matrix sizes and the degree.
No smaller constant holds uniformly over these choices.
\end{corollary}

\begin{lemma}[Gaussian analytic outer approximation]\label{lem:gaussian}
For every nonempty compact convex $K\subset\R^2$ and every $\epsilon>0$,
there is an admissible $\Omega_\epsilon$ such that
\[
 K\subset\Omega_\epsilon,\qquad
 \overline\Omega_\epsilon\subset\{x:\dist(x,K)<\epsilon\}.
\]
\end{lemma}
\begin{proof}
The distance function $d_K$ is convex and $1$-Lipschitz. For convexity,
choose nearest points in $K$ to two given points, use their convex
combination as a competitor, and apply the triangle inequality.
Let $Z$ be a standard Gaussian in $\R^2$ and put
\[
 h_\delta(x)=\mathbb E\,d_K(x-\delta Z)+\delta|x|^2,
 \qquad c=\mathbb E|Z|.
\]
The Lipschitz bound gives the uniform estimate
\[
 \big|\mathbb E\,d_K(x-\delta Z)-d_K(x)\big|\le c\delta.
\]
The convolution is real analytic: write it against the translated
Gaussian density, complexify both coordinates of $x$, and use Gaussian
domination on every compact set of complex coordinates. The factor
$d_K(y)$ has at most linear growth, so the integral defines a holomorphic
function of those coordinates. Convexity passes through convolution;
therefore $h_\delta$ is proper and strictly convex, with Hessian at least
$2\delta I$.

Put $R_K=\max_{x\in K}|x|$, and choose $\delta>0$ with
$c\delta+\delta R_K^2<\epsilon/2$ and $c\delta<\epsilon/2$.
Then $h_\delta<\epsilon/2$ on $K$, while
$h_\delta\le\epsilon/2$ implies
$d_K\le h_\delta+c\delta<\epsilon$. Thus
$\Omega_\epsilon=\{h_\delta<\epsilon/2\}$ has the desired
containments and is bounded, open, and convex. The chosen level is
above the minimum. A critical point of a differentiable convex function
is a global minimum, so the gradient is nonzero on this level.
The implicit function theorem gives a regular real-analytic boundary.
From an interior point, each ray meets this compact boundary exactly
once. Radial projection is a continuous bijection onto the circle and
hence a homeomorphism. The boundary is therefore a Jordan curve.
\end{proof}

\begin{proof}[Proof of Corollary~\ref{cor:polynomial}]
For completeness, the Toeplitz--Hausdorff convexity theorem
\cite{Toeplitz1918,Hausdorff1919} follows here from two-dimensional
compression. Compress to the span of unit vectors realizing any two chosen
values. In dimension two, the rank-one orthogonal projections are
\[
 \frac12\begin{pmatrix}1+u&v+iw\\v-iw&1-u\end{pmatrix},
 \qquad u^2+v^2+w^2=1,\quad u,v,w\in\R.
\]
Taking their trace against the compression is a real-affine map into
$\C\simeq\R^2$. Its linear part has a nonzero kernel. Each point of the
unit ball can be moved in a kernel direction to the sphere without
changing its image, so the images of the sphere and ball coincide.
That image is convex. The one-dimensional compression case is immediate. Compactness
of $W(A)$ follows from compactness of the unit sphere.

Apply Lemma~\ref{lem:gaussian} to $K=W(A)$. For each fixed polynomial
$P(z)=\sum_{j=0}^dB_jz^j$, with arbitrary $B_j\in M_m(\C)$,
Theorems~\ref{thm:structural} and~\ref{thm:representation} give
\[
 \left\|\sum_{j=0}^dA^j\otimes B_j\right\|
 \le2\max_{\overline\Omega_\epsilon}\|P(z)\|.
\]
Uniform continuity on a fixed compact neighborhood of $K$ makes the
maxima on the right tend to $\max_K\|P\|$. This includes point and
segment numerical ranges. It is a limit of scalar bounds for a fixed
polynomial; no limiting similarity or boundary density on $K$ is asserted.
For sharpness take $n=2$, $m=1$, $P(z)=z$, and
$A=\begin{psmallmatrix}0&2\\0&0\end{psmallmatrix}$. Its norm is two,
whereas, for every unit $x\in\C^2$,
\[
 |x^*Ax|=2|x_1x_2|\le |x_1|^2+|x_2|^2=1,
\]
with equality when $x_1=x_2=1/\sqrt2$. Hence
$\max_{W(A)}|P|=1$, proving optimality uniformly over all finite base
sizes, coefficient sizes, and degrees.
\end{proof}

The passage to arbitrary Hilbert spaces uses only finitely many iterates of
the input to a polynomial. The closure of the numerical range is needed for
the compact spectral-set formulation, because an infinite-dimensional
numerical range need not be closed.

\begin{corollary}[The sharp complete inequality for bounded operators]\label{cor:hilbert}
Let $\mathcal H$ be a complex Hilbert space, with no separability assumption,
and let $A\in\mathcal B(\mathcal H)$. Suppose first that
$\mathcal H\ne\{0\}$, and put
\[
 W(A)=\{\langle x,Ax\rangle:x\in\mathcal H,\ \|x\|=1\},
 \qquad K=\overline{W(A)}.
\]
Then $K$ is compact and convex and contains $\spec(A)$. For every positive
integer $m$, every nonnegative integer $d$, and every matrix polynomial
$P(z)=\sum_{k=0}^d B_kz^k$ with $B_k\in M_m(\C)$, the operator
$P[A]=\sum_{k=0}^d A^k\otimes B_k$ on $\mathcal H\otimes\C^m$ satisfies
\begin{equation}\label{eq:hilbert-polynomial}
 \|P[A]\|\le 2\sup_{z\in W(A)}\|P(z)\|
             =2\max_{z\in K}\|P(z)\|.
\end{equation}
More generally, if $U$ is an open neighborhood of $K$ and
$F=(f_{ij}):U\to M_m(\C)$ is holomorphic, its entrywise holomorphic
evaluation, in the same base-first tensor convention, satisfies
\begin{equation}\label{eq:hilbert-holomorphic}
 F[A]:=\sum_{i,j=1}^m f_{ij}(A)\otimes E_{ij},
 \qquad \|F[A]\|\le2\max_{z\in K}\|F(z)\|.
\end{equation}
Here $E_{ij}$ are the standard matrix units and $f_{ij}(A)$ is given by the
holomorphic functional calculus. In particular, $K$ is a complete
$2$-spectral set for $A$: the same estimate holds at every finite coefficient
size for every matrix-valued rational function whose poles lie outside $K$,
with evaluation by the rational functional calculus. The constant two is
optimal uniformly over all these choices.

If $\mathcal H=\{0\}$, every evaluation is the zero operator. With the
supremum over the empty numerical range defined to be zero, the corresponding
supremum-norm inequalities are $0\le0$; the compact spectral-set assertion
above is stated for nonzero $\mathcal H$.
\end{corollary}
\begin{proof}
Assume $\mathcal H\ne\{0\}$. We first prove the polynomial bound. With
$e_1,\ldots,e_m$ the standard basis of $\C^m$, every vector in the Hilbert
tensor product has the exact form
$\xi=\sum_{j=1}^m\xi_j\otimes e_j$, with $\xi_j\in\mathcal H$.
For $\xi\ne0$, define the nonzero finite-dimensional subspace
\[
 E=\operatorname{span}\{A^k\xi_j:0\le k\le d,\ 1\le j\le m\},
 \qquad A_E=Q_EA|_E,
\]
where $Q_E$ is the orthogonal projection onto $E$. Induction gives
$A_E^k\xi_j=A^k\xi_j$ for $0\le k\le d$: at each step the next iterate
already belongs to $E$. Hence, as vectors in $E\otimes\C^m$,
\[
 P[A]\xi=\sum_{k=0}^d\sum_{j=1}^m A^k\xi_j\otimes B_ke_j
         =\sum_{k=0}^d\sum_{j=1}^m A_E^k\xi_j\otimes B_ke_j
         =P[A_E]\xi.
\]
For each unit $x\in E$, orthogonality of $Q_E$ gives
$\langle x,A_Ex\rangle=\langle x,Q_EAx\rangle=\langle x,Ax\rangle$.
With the conjugate-linear-first convention, these are exactly the
numerical-range values used in Corollary~\ref{cor:polynomial}.
Thus $W(A_E)\subset W(A)$. Applying Corollary~\ref{cor:polynomial} in an
orthonormal basis of $E$ yields
\[
 \|P[A]\xi\|\le2\max_{z\in W(A_E)}\|P(z)\|\,\|\xi\|
              \le2\sup_{z\in W(A)}\|P(z)\|\,\|\xi\|.
\]
Taking the supremum over unit $\xi$ proves the inequality. This argument
uses no sequence of subspaces exhausting $\mathcal H$.

The same two-vector compression argument used in the proof of
Corollary~\ref{cor:polynomial} shows that $W(A)$ is convex. It is bounded by
$\|A\|$, so $K$ is compact and convex. Continuity of $P$ and density of
$W(A)$ in $K$ give the equality of the supremum and maximum in
\eqref{eq:hilbert-polynomial}. To check spectral containment, let
$\lambda\notin K$ and $\delta=\dist(\lambda,K)>0$. For every
$x\in\mathcal H$, Cauchy--Schwarz gives
\[
 \|(\lambda I-A)x\|\,\|x\|
 \ge |\langle x,(\lambda I-A)x\rangle|
 \ge\delta\|x\|^2.
\]
Since $W(A^*)=\{\overline z:z\in W(A)\}$,
the same argument gives
$\|(\overline\lambda I-A^*)y\|\ge\delta\|y\|$ for every $y$.
The first lower bound makes $\lambda I-A$ injective with closed range, and the
second makes it dense because its orthogonal complement is the kernel of
$\overline\lambda I-A^*$. Thus $\lambda I-A$ is invertible, proving
$\spec(A)\subset K$.

Now fix $U$ and $F$ as in the statement. Choose $\epsilon>0$ such that the
compact convex neighborhood
\[
 K_\epsilon=\{z\in\C:\dist(z,K)\le\epsilon\}
\]
is contained in $U$. Its complement is connected. Runge's polynomial
approximation theorem, obtained by rational approximation and movement of
poles to infinity in the connected complement
\cite[pp.~235--238]{Runge1885}, gives matrix polynomials $P_\ell$ with
\[
 \max_{z\in K_\epsilon}\|P_\ell(z)-F(z)\|\longrightarrow0.
\]
Indeed, apply the scalar theorem to each of the finitely many entries;
entrywise uniform convergence implies convergence in matrix operator norm.
By Lemma~\ref{lem:gaussian}, choose an admissible $\Omega$ with
$K\subset\Omega$ and $\overline\Omega\subset K_\epsilon$, and let
$\Gamma=\partial\Omega$ have positive orientation. The holomorphic
functional calculus, entry by entry, reads
\[
 F[A]=\frac{1}{2\pi i}\int_\Gamma
        (zI-A)^{-1}\otimes F(z)\,dz.
\]
The integral converges in operator norm. For a polynomial, Cauchy's theorem
moves the contour to a large circle, where the resolvent's Neumann expansion
gives the prescribed base-first evaluation. Consequently
\[
 \|F[A]-P_\ell[A]\|
 \le\frac{\operatorname{length}(\Gamma)}{2\pi}
     \max_{z\in\Gamma}\|(zI-A)^{-1}\|
     \max_{z\in\Gamma}\|F(z)-P_\ell(z)\|
 \longrightarrow0.
\]
The maxima of $\|P_\ell\|$ on $K$ also converge to that of $\|F\|$.
Applying \eqref{eq:hilbert-polynomial} to $P_\ell$ and taking the limit
proves \eqref{eq:hilbert-holomorphic}. The larger compact neighborhood is
used to obtain convergence on the fixed contour, not just on $K$.

A matrix-valued rational function whose poles lie outside $K$ is holomorphic
on a neighborhood $U$ of $K$ that avoids all its poles; the preceding choice
then puts every pole outside $\overline\Omega$. Spectral containment makes
its rational evaluation well-defined, and this agrees with the displayed contour
evaluation. For example, the resolvent identity identifies the contour
evaluation of $(z-a)^{-1}$ with $(A-aI)^{-1}$ when $a\notin\overline\Omega$;
differentiation in $a$ gives the higher pole orders, and partial
fractions give every rational function. This proves the complete spectral-set
assertion. Finally, the $2$-by-$2$ scalar-coefficient example in the proof of
Corollary~\ref{cor:polynomial} is already a bounded Hilbert-space operator
and is both rational and holomorphic. It proves the stated uniform sharpness.
\end{proof}

\appendix
\section{Local conformal reconstruction}
\label{sec:conformal-appendix}

We give the classical extremal proof of Riemann mapping and the
harmonic-reflection argument \cite[Chapter~6, Section~1.1; Chapter~4,
Section~6.5]{Ahlfors1979}, then prove the collar patching and global
univalence needed in Lemma~\ref{lem:conformal-coordinates}. The extension argument is stated for a
general analytic Jordan domain, since the inversion used for the exterior
coordinate need not preserve convexity. For general background on boundary
behavior of conformal maps, see \cite{Pommerenke1992}.

\begin{proof}[Proof of Lemma~\ref{lem:conformal-coordinates}]
\emph{A disk coordinate for a bounded simply connected domain.}
Let $U\subset\C$ be a bounded simply connected domain and fix $z_*\in U$.
Consider the injective holomorphic maps $\phi:U\to\D$ satisfying
$\phi(z_*)=0$. This family is nonempty, since a sufficiently small multiple
of $z-z_*$ belongs to it. The supremum $\alpha$ of $|\phi'(z_*)|$ over the
family is positive and finite: a disk centered at $z_*$ with closure in $U$
gives a uniform upper bound by Cauchy's derivative estimate.

Choose a sequence approaching this supremum. Cauchy's estimates and compact
exhaustion give a subsequence converging locally uniformly to a holomorphic
function $\phi$. Its derivative at $z_*$ has modulus $\alpha$, so it is
nonconstant; the maximum principle then gives $\phi(U)\subset\D$.
The limit is injective. Indeed, if two distinct points had the same image,
choose disjoint small closed disks about them on whose boundaries the limit
minus this common image does not vanish. The argument principle preserves
at least one zero in each disk for every sufficiently late member of the
sequence, contradicting its injectivity.

Suppose that $w\in\D\setminus\phi(U)$. Necessarily $w\ne0$. The function
\[
 q(z)=\frac{\phi(z)-w}{1-\overline w\phi(z)}
\]
is holomorphic and nonvanishing on the simply connected domain $U$, and
therefore has a holomorphic square root $h$. It satisfies $|h|<1$ and is
injective, since $h^2=q$ is injective. Set $\beta=h(z_*)$, so that
$|\beta|=\sqrt{|w|}$. The injective disk-valued function
\[
 \psi(z)=\frac{h(z)-\beta}{1-\overline\beta h(z)}
\]
vanishes at $z_*$ and has derivative magnitude
\[
 |\psi'(z_*)|
 =\frac{1-|w|^2}{2\sqrt{|w|}(1-|w|)}\,|\phi'(z_*)|
 =\frac{1+|w|}{2\sqrt{|w|}}\,\alpha
 >\alpha.
\]
This is impossible. Thus $\phi$ maps $U$ conformally onto $\D$.

\medskip
\emph{Reflection at a regular analytic boundary.}
Suppose now that $\partial U$ is a regular real-analytic Jordan curve.
For each $0<r<1$, the set $\phi^{-1}(r\overline\D)$ is a compact subset
of $U$, because the conformal inverse is continuous on $\D$.
Consequently $|\phi(z)|\to1$ as $z$ approaches $\partial U$ from inside.

Fix $p\in\partial U$. A regular real-analytic parametrization of the
boundary near $p$ extends holomorphically with nonzero derivative. Its
local holomorphic inverse straightens the boundary. After shrinking and
choosing its sign, we therefore have a holomorphic coordinate
$z=\chi(\xi)$ taking $0$ to $p$, a real diameter to the boundary arc, and
the upper half of a small disk to the part of $U$ in this coordinate
neighborhood. Choose the neighborhood disjoint from $z_*$. Then
\[
 u(\xi)=\log|\phi(\chi(\xi))|
\]
is harmonic and strictly negative on the upper half disk, and is
continuous with value zero on its real diameter.

Here the harmonic reflection can be obtained directly. On the boundary
of a smaller full disk, prescribe $u$ on the upper semicircle and the
negative of its reflected values on the lower semicircle. These boundary
values are continuous, including at the endpoints of the diameter.
Their Poisson extension is odd under reflection in the real axis, hence
vanishes on the diameter. Uniqueness for the Dirichlet problem on the
upper half disk shows that it agrees there with $u$. Denote the resulting
harmonic extension by $\widehat u$.

The gradient of $\widehat u$ at zero does not vanish. To see this, its
first nonzero homogeneous Taylor term has the form
\[
 c\,\operatorname{Im}(\xi^k),\qquad c\in\R\setminus\{0\},\quad k\ge1,
\]
because $\widehat u$ is harmonic and vanishes on the real diameter.
Such a term exists since $u<0$ on the upper half disk. If $k\ge2$,
$\sin(k\theta)$ takes both signs for $0<\theta<\pi$; along two
corresponding rays the leading term would force $u$ to take both signs
near zero. Thus $k=1$.

Take a harmonic conjugate $\widehat v$ on the full disk. The function
$\exp(\widehat u+i\widehat v)$ is holomorphic and nonvanishing, with
nonzero derivative at zero. On the upper half disk it has the same
modulus as $\phi\circ\chi$, so their quotient is a constant of modulus
one. Adjusting that constant and returning to the physical coordinate
extends $\phi$ holomorphically across $p$, with nonzero derivative there.

\medskip
\emph{Patching and univalence on a neighborhood of the closure.}
We spell out the passage from these local extensions to one extension,
including overlaps that may lie outside $U$. For each boundary point
$p$, choose an extension disk $B(p,R_p)$ contained in its reflected
coordinate neighborhood. Its extension agrees with $\phi$ throughout
$U\cap B(p,R_p)$; shrink $R_p$ so that its derivative is nonzero on the
disk. Select finitely many points $p_i$ such that the smaller disks
\[
 V_i=B(p_i,R_i/3),\qquad R_i=R_{p_i},
\]
cover $\partial U$, and let $\phi_i$ denote the extension on
$U_i=B(p_i,R_i)$.
If $V_i\cap V_j\ne\varnothing$ and $R_i\ge R_j$, then
\[
 |p_i-p_j|<\frac{R_i+R_j}{3}\le\frac{2R_i}{3}<R_i.
\]
Thus the connected open lens $U_i\cap U_j$ contains the boundary point
$p_j$ and meets $U$ in a nonempty open set. Both extensions agree with
$\phi$ there, so the identity theorem makes them equal on the entire
lens. Their restrictions therefore patch with $\phi$ to a holomorphic
function on
\[
 U\,\cup\,\bigcup_i V_i,
\]
an open neighborhood of $\overline U$. We continue to call it $\phi$.

The extended map takes $\partial U$ into $\T$. Its nonzero derivative
makes the restriction to the boundary a local diffeomorphism onto an
arc of $\T$. The boundary image is consequently open in $\T$, and it
is also nonempty and compact, so it is all of $\T$.
There cannot be two distinct boundary points with the same image
$\eta\in\T$. Indeed, choose disjoint local inverse neighborhoods about
them. Each inverse, restricted to a sufficiently small neighborhood
of $\eta$, takes its disk side into $U$: the boundary arc is mapped
to $\T$, and the interior side is mapped into $\D$. Points in $\D$
sufficiently close to $\eta$ would then have two preimages in $U$,
contradicting interior injectivity. Since interior and boundary images
lie in $\D$ and $\T$, respectively, $\phi$ is injective on
$\overline U$.

It is in fact injective on an open neighborhood of $\overline U$.
Otherwise there would be distinct pairs $z_j,w_j$, approaching the
compact set $\overline U$, with $\phi(z_j)=\phi(w_j)$. Subsequence
limits $z,w\in\overline U$ have the same image, hence $z=w$.
Both sequences would eventually lie in one local inverse neighborhood
of $z$, a contradiction. The image of a sufficiently small such
neighborhood is open and contains $\overline\D$. Its holomorphic
inverse gives a univalent extension of $\phi^{-1}$ to a neighborhood
of $\overline\D$.

Applying these conclusions to the admissible domain $\Omega$ gives the
interior coordinate $f$ and both of its asserted extensions.

\medskip
\emph{The exterior coordinate.}
Fix $z_0\in\Omega$ and apply the inversion
\[
 \iota(z)=\frac{1}{z-z_0},\qquad \iota(\infty)=0,
\]
to the exterior of $\overline\Omega$, including infinity. Its image
$U_{\mathrm{ext}}$ is a bounded domain containing zero. More explicitly,
convexity and $z_0\in\Omega$ give a finite positive boundary radius
$R(\theta)$ on each ray $z_0+r e^{i\theta}$, and
\[
 U_{\mathrm{ext}}
 =\{0\}\,\cup\,
   \bigl\{s e^{-i\theta}:0<s<R(\theta)^{-1}\bigr\}.
\]
This domain is star-shaped about zero, hence simply connected.
Boundedness follows also from a positive disk about $z_0$ contained
in $\Omega$; a neighborhood of zero is in the image because $\Omega$
is bounded. Inversion preserves the regular real-analytic Jordan
boundary, since its pole $z_0$ is not on that boundary.

By the preceding arguments there is a conformal map
$\phi_{\mathrm{ext}}:U_{\mathrm{ext}}\to\D$ with
$\phi_{\mathrm{ext}}(0)=0$, whose inverse $h$ extends univalently
to a disk $\{\zeta:|\zeta|<\rho\}$ for some $\rho>1$.
Here $h(0)=0$ is its only zero on this larger disk, and it is simple.
Define
\[
 G(t)=z_0+\frac{1}{h(1/t)},\qquad |t|>r_0:=\rho^{-1}.
\]
The function $G$ is univalent on this region. It maps $|t|>1$ onto
the exterior of $\overline\Omega$, takes infinity to infinity, and
has a simple pole there. Its convergent Laurent expansion is therefore
\[
 G(t)=at+b+\sum_{\ell\ge1}c_\ell t^{-\ell},
 \qquad a=h'(0)^{-1}\ne0.
\]
In particular its restriction to $\T$ is a smooth diffeomorphism onto
$\partial\Omega$.

\medskip
\emph{Orientation and normal direction.}
For $t=e^{i\theta}$, the radial and angular derivatives are
\[
 \left.\frac{\partial}{\partial r}G(re^{i\theta})\right|_{r=1}
 =tG'(t),
 \qquad
 \frac{d}{d\theta}G(e^{i\theta})=itG'(t).
\]
They are nonzero and perpendicular. Increasing $r$ enters the exterior
of $\overline\Omega$, so $tG'(t)$ points in the outward normal direction.
The tangent $itG'(t)$ is consequently the positive boundary tangent.
The interior conformal map $f$ preserves boundary orientation: locally
it maps the interior side of $\partial\Omega$ to the interior side of
$\T$, and its derivative preserves orientation in the plane.
Thus $f\circ G:\T\to\T$ is a smooth orientation-preserving
diffeomorphism. This proves every assertion of the lemma.
\end{proof}

\input{references}
\end{document}

```

## preprints/The-complete-Crouzeix-theorem-September-23-2026/build/references.tex

{"path": "preprints/The-complete-Crouzeix-theorem-September-23-2026/build/references.tex", "url": "https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-complete-Crouzeix-theorem-September-23-2026/build/references.tex", "bytes": 4948, "sha256": "f3b98c87d0d9f657061b21b80d14718fb211b366c60ad0d56af3a493f4dbc56b", "git_blob": "3b3a2ffc61c2a4a63df6287b2865f8895bd3b5ac", "catalogue_git_blob": "3b3a2ffc61c2a4a63df6287b2865f8895bd3b5ac", "matches_catalogue": true}

```tex
\begin{thebibliography}{99}
\raggedright

\bibitem{AhagCzyzVirtanen2026}
P.~\AA hag, R.~Czy{\.{z}}, and J.~Virtanen,
\emph{The complete Crouzeix conjecture in dimension three and the
Clou\^atre--Ostermann--Ransford conjecture},
\href{https://arxiv.org/abs/2608.27346v4}{arXiv:2608.27346v4}, September 21, 2026.

\bibitem{Ahlfors1979}
L.~V. Ahlfors, \emph{Complex Analysis}, third ed., McGraw--Hill, New York, 1979.

\bibitem{Arveson1972}
W. Arveson, Subalgebras of $C^*$-algebras II,
\emph{Acta Math.} \textbf{128} (1972), 271--308.

\bibitem{BadeaCrouzeixDelyon2006}
C. Badea, M. Crouzeix, and B. Delyon, Convex domains and $K$-spectral sets,
\emph{Math. Z.} \textbf{252} (2006), 345--365.

\bibitem{Beckermann2005}
B. Beckermann, Image num\'erique, GMRES et polyn\^omes de Faber,
\emph{C. R. Math.} \textbf{340} (2005), 855--860.

\bibitem{BeckermannCrouzeix2014}
B. Beckermann and M. Crouzeix, Faber polynomials of matrices for non-convex sets,
\emph{Jaen J. Approx.} \textbf{6} (2014), 219--231.

\bibitem{BeckermannStylianopoulos2018}
B. Beckermann and N. Stylianopoulos, Bergman Orthogonal Polynomials and the
Grunsky Matrix, \emph{Constr. Approx.} \textbf{47} (2018), 211--235.

\bibitem{Brodskii1978}
M. S. Brodski\u\i, Unitary operator colligations and their characteristic
functions, \emph{Russian Math. Surveys} \textbf{33}:4 (1978), 159--191.

\bibitem{Crouzeix2004}
M.~Crouzeix, Bounds for analytical functions of matrices,
\emph{Integral Equations Operator Theory} \textbf{48} (2004), 461--477.
\href{https://doi.org/10.1007/s00020-002-1188-6}{doi:10.1007/s00020-002-1188-6}.

\bibitem{Crouzeix2007}
M.~Crouzeix, Numerical range and functional calculus in Hilbert space,
\emph{J. Funct. Anal.} \textbf{244} (2007), 668--690.
\href{https://doi.org/10.1016/j.jfa.2006.10.013}{doi:10.1016/j.jfa.2006.10.013}.

\bibitem{CrouzeixPalencia2017}
M. Crouzeix and C. Palencia, The numerical range is a
$(1+\sqrt2)$-spectral set,
\emph{SIAM J. Matrix Anal. Appl.} \textbf{38} (2017), 649--655.

\bibitem{DelyonDelyon1999}
B. Delyon and F. Delyon, Generalization of von Neumann's spectral sets
and integral representation of operators,
\emph{Bull. Soc. Math. France} \textbf{127} (1999), 25--41.

\bibitem{Hausdorff1919}
F. Hausdorff, Der Wertvorrat einer Bilinearform,
\emph{Math. Z.} \textbf{3} (1919), 314--316.

\bibitem{Jin2026}
S.~Jin, \emph{The numerical range is a $2$-spectral set},
\href{https://www.preprints.org/manuscript/202607.1919/v4}{Preprints.org 202607.1919, version 4},
August 7, 2026.

\bibitem{KatsnelsonKheifetsYuditskii1997}
V. E. Katsnelson, A. Ya. Kheifets, and P. M. Yuditskii,
An abstract interpolation problem and the extension theory of isometric operators,
in \emph{Topics in Interpolation Theory}, OTAA \textbf{95},
Birkh\"auser, 1997, 283--298.
Preprint version: \href{https://arxiv.org/abs/0706.1896v1}{arXiv:0706.1896v1}.

\bibitem{LoristSchwenninger2026}
E.~Lorist and F.~L. Schwenninger,
\emph{A solution to Crouzeix's conjecture},
\href{https://arxiv.org/abs/2608.03841v2}{arXiv:2608.03841v2}, August 17, 2026.

\bibitem{Luo2026}
Q.~Luo, \emph{Two boundary-certificate proofs of the Crouzeix theorem:
Fiberwise Fourier recurrence and defect-Gram telescoping},
\href{https://www.preprints.org/manuscript/202608.1661/v2}{Preprints.org 202608.1661, version 2},
August 28, 2026.

\bibitem{Direct}
OpenAI, \emph{A direct proof of the complete Crouzeix inequality},
OpenAI Math Release preprint
\href{https://github.com/openai/math/blob/main/preprints/A-direct-proof-of-the-complete-Crouzeix-inequality-September-26-2026/paper.pdf}{OAI:A-direct-proof-of-the-complete-Crouzeix-inequality-September-26-2026},
2026.

\bibitem{Paulsen1984Similarity}
V. I. Paulsen, Completely bounded homomorphisms of operator algebras,
\emph{Proc. Amer. Math. Soc.} \textbf{92} (1984), 225--228.

\bibitem{Pommerenke1992}
C. Pommerenke, \emph{Boundary Behaviour of Conformal Maps},
Springer-Verlag, 1992.

\bibitem{RansfordSchwenninger2018}
T.~Ransford and F.~L. Schwenninger,
Remarks on the Crouzeix--Palencia proof that the numerical range is a
$(1+\sqrt{2})$-spectral set,
\emph{SIAM J. Matrix Anal. Appl.} \textbf{39} (2018), 342--345.
\href{https://doi.org/10.1137/17M1143757}{doi:10.1137/17M1143757}.

\bibitem{Rockafellar1970}
R. T. Rockafellar, \emph{Convex Analysis}, Princeton University Press, 1970.

\bibitem{Runge1885}
C.~Runge, Zur Theorie der eindeutigen analytischen Functionen,
\emph{Acta Math.} \textbf{6} (1885), 229--244.
\href{https://doi.org/10.1007/BF02400416}{doi:10.1007/BF02400416}.

\bibitem{Stein1952}
P. Stein, Some General Theorems on Iterants,
\emph{J. Res. Nat. Bur. Stand.} \textbf{48} (1952), 82--83.

\bibitem{SzNagy1953}
B. Sz.-Nagy, Sur les contractions de l'espace de Hilbert,
\emph{Acta Sci. Math. (Szeged)} \textbf{15} (1953), 87--92.

\bibitem{Toeplitz1918}
O. Toeplitz, Das algebraische Analogon zu einem Satze von Fej\'er,
\emph{Math. Z.} \textbf{2} (1918), 187--197.

\end{thebibliography}

```

## External primary excerpt: https://arxiv.org/html/2608.27346v3

Selected HTML sections: S9, S11. Equations use the HTML alttext.

```text


9. Equality and quantitative estimates

At $\tau=1/2$, both square-function estimates are needed to identify
the reducing subspace associated with the singular value $2$. The
results in this section are first stated for bounded operators. For an
operator $T$ satisfying these estimates, put

$E_{T}=\ker(4I-T^{*}T),\qquad F_{T}=\frac{1}{2}TE_{T}.$

Theorem 9.1.

Let $T\in\mathcal{B}(H)$ satisfy

$\sum_{k=0}^{\infty}4^{-k}T^{*k}T^{k}\preceq 2I,\qquad\sum_{k=0}^{\infty}4^{-k}T^{k}T^{*k}\preceq 2I.$

Then $E_{T}\perp F_{T}$, the subspace $E_{T}\oplus F_{T}$ reduces $T$, and,
after identifying $E_{T}$ with $F_{T}$ by $x\mapsto Tx/2$,

$T\simeq_{u}\begin{pmatrix}0&0\\
2I_{E_{T}}&0\end{pmatrix}\oplus R.$

If $\left\lVert T\right\rVert=2$ is attained, then $E_{T}\neq\{0\}$. If $H$ is
finite-dimensional and $\left\lVert T\right\rVert=2$, then $\left\lVert R\right\rVert<2$, and $T$ is not
diagonalizable.

Proof.

Put $E=E_{T}$. The map $U=T|_{E}/2$ is an isometry from $E$ onto
$F=F_{T}$. Let $x\in E$. The first square-function estimate gives

$\displaystyle 2\left\lVert x\right\rVert^{2}$
$\displaystyle\geq\sum_{k=0}^{\infty}4^{-k}\left\lVert T^{k}x\right\rVert^{2}$

$\displaystyle=2\left\lVert x\right\rVert^{2}+\sum_{k=2}^{\infty}4^{-k}\left\lVert T^{k}x\right\rVert^{2}.$

Thus $T^{2}x=0$. If $y=Ux$, then

$Ty=0,\qquad T^{*}y=2x.$

The second square-function estimate applied to $y$ gives
$(T^{*})^{2}y=0$, and therefore $T^{*}x=0$.

If $x,z\in E$, then

$\left\langle x,Uz\right\rangle=\frac{1}{2}\left\langle T^{*}x,z\right\rangle=0.$

Hence $E\perp F$, and

$TE=2F,\qquad TF=0,\qquad T^{*}F=2E,\qquad T^{*}E=0.$

Thus $E\oplus F$ reduces $T$ and gives the stated block.

If $\left\lVert T\right\rVert=2$ is attained at a unit vector $x$, then
$T^{*}Tx=4x$, so $x\in E$. Suppose now that $H$ is finite-dimensional and
$\left\lVert T\right\rVert=2$. Then $E\neq\{0\}$. If the restriction $R$ to
$(E\oplus F)^{\perp}$ had norm $2$, a unit vector at which its norm is
attained would belong to $E\cap(E\oplus F)^{\perp}$, a contradiction.
Hence $\left\lVert R\right\rVert<2$. The nonzero nilpotent summand shows that $T$ is not
diagonalizable.
∎

Remark 9.2.

As a consequence, we obtain another proof that $\psi(A)<2$ if $A=V\Lambda V^{-1}$ is diagonalizable. Indeed, $\psi(A)$ is attained, say at a scalar-valued function $f$ with $\|f\|_{W(A)}=1$. If $\psi(A)=2$, then $T=f(A)$ satisfies $\|T\|=2$, and Theorem 1.3 with $\tau=1/2$ allows us to apply the preceding theorem to conclude that $T$ is not diagonalizable. On the other hand,
$T=f(A)=Vf(\Lambda)V^{-1}$, so $T$ is diagonalizable, which is a contradiction.

When the norm is not attained, $E_{T}$ may be trivial. The next theorem
replaces it by two-dimensional subspaces on which $T$ approaches the
nilpotent equality block.

Theorem 9.3.

Let $T\in\mathcal{B}(H)$ satisfy the two square-function estimates in
Theorem 9.1, and assume that $\left\lVert T\right\rVert=2$. Then
there are orthogonal decompositions

$H=\mathcal{M}_{j}\oplus\mathcal{M}_{j}^{\perp},\qquad\dim\mathcal{M}_{j}=2,$

and operators $D_{j}\in\mathcal{B}(\mathcal{M}_{j}^{\perp})$ such that, in a
suitable orthonormal basis of $\mathcal{M}_{j}$,

$\left\lVert T-\left(\begin{pmatrix}0&0\\
2&0\end{pmatrix}\oplus D_{j}\right)\right\rVert\longrightarrow 0.$

Proof.

Since $4=\left\lVert T^{*}T\right\rVert$ belongs to the spectrum of the positive operator
$T^{*}T$, there are unit vectors $x_{j}$ such that

$\left\lVert(T^{*}T-4I)x_{j}\right\rVert\longrightarrow 0.$

After discarding finitely many indices, put

$s_{j}=\left\lVert Tx_{j}\right\rVert>0,\qquad y_{j}=\frac{Tx_{j}}{s_{j}}.$

Then $s_{j}\to 2$ and

$\left\lVert T^{*}y_{j}-2x_{j}\right\rVert\longrightarrow 0.$

The first square-function estimate gives
$\left\lVert T^{2}x_{j}\right\rVert\to 0$, and hence $\left\lVert Ty_{j}\right\rVert\to 0$. Since
$\left\lVert T^{*}y_{j}\right\rVert\to 2$, the second square-function estimate gives
$\left\lVert(T^{*})^{2}y_{j}\right\rVert\to 0$. Indeed,

$2T^{*}x_{j}=(T^{*})^{2}y_{j}-T^{*}(T^{*}y_{j}-2x_{j})\longrightarrow 0,$

and

$\left\lvert\left\langle y_{j},x_{j}\right\rangle\right\rvert=\frac{\left\lvert\left\langle Tx_{j},x_{j}\right\rangle\right\rvert}{s_{j}}=\frac{\left\lvert\left\langle x_{j},T^{*}x_{j}\right\rangle\right\rvert}{s_{j}}\longrightarrow 0.$

Write

$\beta_{j}=\left\langle y_{j},x_{j}\right\rangle,\qquad\rho_{j}=(1-\left\lvert\beta_{j}\right\rvert^{2})^{1/2},\qquad e_{j}=\frac{y_{j}-\beta_{j}x_{j}}{\rho_{j}},$

after discarding finitely many further indices. Put
$\mathcal{M}_{j}=\operatorname{span}\{x_{j},e_{j}\}$. Then
$\{x_{j},e_{j}\}$ is orthonormal and

$Tx_{j}-2e_{j}\longrightarrow 0,\qquad Te_{j}\longrightarrow 0,\qquad T^{*}x_{j}\longrightarrow 0,\qquad T^{*}e_{j}-2x_{j}\longrightarrow 0.$

Let $P_{j}$ be the orthogonal projection onto $\mathcal{M}_{j}$, let
$N_{j}x_{j}=2e_{j}$ and $N_{j}e_{j}=0$, and set

$D_{j}=(I-P_{j})T|_{\mathcal{M}_{j}^{\perp}}.$

The four preceding limits give

$\left\lVert P_{j}TP_{j}-N_{j}\right\rVert\longrightarrow 0,\qquad\left\lVert(I-P_{j})TP_{j}\right\rVert\longrightarrow 0,\qquad\left\lVert P_{j}T(I-P_{j})\right\rVert\longrightarrow 0.$

These are the nonzero blocks of $T-(N_{j}\oplus D_{j})$, and the result
follows.
∎

We next solve the optimization problem used in the quantitative
estimates. For $0<s\leq 2$, let $\tau_{s}$ be the unique
number in $[1/2,3/4)$ satisfying

(9.1)

$2s^{2}\tau_{s}(1-\tau_{s})^{2}+4\tau_{s}-3=0,$

and put

$\eta(s)=\left(\frac{2\tau_{s}-1}{2\tau_{s}^{3}(1-\tau_{s})^{2}}\right)^{1/2}.$

Thus $\eta(2)=0$. The functions $L_{\tau}$ and $L$ were defined in
(4.5).

Lemma 9.4.

For $0<s\leq 2$,

(9.2)

$\eta(s)=\min_{0<\tau<1}\frac{1}{\tau^{2}}\left(\frac{\tau}{1-\tau}-s^{2}\tau^{2}\right)^{1/2}.$

Moreover,

(9.3)

$\eta(s)\leq 2\sqrt{4-s^{2}},$

with strict inequality when $s<2$. For $0<s<2$,

(9.4)

$L(s)=\max_{0<\tau<1}L_{\tau}(s)>L_{1/2}(s)=\frac{s^{4}}{4(4-s^{2})}.$

The functions $s\mapsto\tau_{s}$ and $s\mapsto\eta(s)$ are continuous on
$(0,2]$, and $L$ is continuous on $(0,2)$.

Proof.

Put

$q_{s}(\tau)=2s^{2}\tau(1-\tau)^{2}+4\tau-3.$

Its derivative satisfies

$q_{s}^{\prime}(\tau)=2s^{2}(1-\tau)(1-3\tau)+4\geq 4-\frac{2s^{2}}{3}>0.$

Also, $q_{s}(0)=-3$, $q_{s}(1)=1$,
$q_{s}(1/2)=s^{2}/4-1\leq 0$, and $q_{s}(3/4)=3s^{2}/32>0$.
Thus (9.1) has the asserted unique solution.

The square of the expression minimized in (9.2) is

$d_{s}(\tau)=\frac{1}{\tau^{3}(1-\tau)}-\frac{s^{2}}{\tau^{2}}.$

A direct calculation gives

$d_{s}^{\prime}(\tau)=\frac{q_{s}(\tau)}{\tau^{4}(1-\tau)^{2}}.$

Since $d_{s}(\tau)$ tends to infinity at both endpoints, its unique
minimum occurs at $\tau_{s}$. Substitution of (9.1) gives

$d_{s}(\tau_{s})=\frac{2\tau_{s}-1}{2\tau_{s}^{3}(1-\tau_{s})^{2}}.$

This proves (9.2). Choosing $\tau=1/2$ gives
(9.3). The inequality is strict for $s<2$ because
then $\tau_{s}>1/2$.

For $0<s<2$, the denominator in $L_{\tau}(s)$ is positive. Differentiation
gives

$\frac{\partial}{\partial\tau}L_{\tau}(s)=-\frac{s^{4}\tau^{2}q_{s}(\tau)}{\{1-s^{2}\tau(1-\tau)\}^{2}}.$

Hence the unique maximum occurs at $\tau_{s}$. Since $\tau_{s}>1/2$,
(9.4) follows. Continuity follows from the implicit
function theorem applied to (9.1).
∎

Put

$\vartheta(s)=\min\{s^{2},\eta(s)\},\qquad 0<s\leq 2.$

Theorem 9.5.

Let $T_{1},\ldots,T_{q}\in\mathcal{B}(H)$ satisfy, for every $0<\tau<1$,

(9.5)

$\sum_{k=0}^{\infty}\tau^{2k}\sum_{\alpha\in\mathcal{W}_{k}}T_{\alpha}^{*}T_{\alpha}\preceq\frac{1}{1-\tau}I.$

Let

$s=\left\lVert(T_{1},\ldots,T_{q})^{\mathsf{T}}\right\rVert>0,$

and suppose that this norm is attained at a unit vector $x$. Then
$s\leq 2$ and

(9.6)

$\left(\sum_{i,j=1}^{q}\left\lVert T_{i}T_{j}x\right\rVert^{2}\right)^{1/2}\leq\vartheta(s).$

The function $\vartheta$ cannot be replaced by a smaller function of
$s$, since the scalar case $q=1$ is sharp.

Proof.

Keeping the terms of degrees zero and one in
(9.5), and taking $\tau=1/2$, gives
$s\leq 2$. Applying the quadratic form at $x$ and retaining the terms
through degree two gives

$\tau^{4}\sum_{i,j=1}^{q}\left\lVert T_{i}T_{j}x\right\rVert^{2}\leq\frac{\tau}{1-\tau}-\tau^{2}s^{2}.$

Lemma 9.4 gives the bound by $\eta(s)$. On the
other hand, the definition of the column norm gives

$\sum_{i,j=1}^{q}\left\lVert T_{i}T_{j}x\right\rVert^{2}\leq s^{2}\sum_{j=1}^{q}\left\lVert T_{j}x\right\rVert^{2}=s^{4}.$

Taking the smaller of these two bounds proves
(9.6). The sharp scalar examples are given
in Theorem 9.7.
∎

The same optimization gives a lower bound on every eigenvector
condition number that realizes a diagonalization in dimension three.

Corollary 9.6.

Let $A\in M_{3}(\mathbb{C})$ be diagonalizable, write
$A=V\Lambda V^{-1}$, and put

$C=\psi_{\mathrm{cb}}(A),\qquad\kappa=\cond(V).$

Then

(9.7)

$\kappa^{4}\geq L(C)>\frac{C^{4}}{4(4-C^{2})}.$

In particular, if $A_{j}=V_{j}\Lambda_{j}V_{j}^{-1}\in M_{3}(\mathbb{C})$ are
diagonalizable and $\psi_{\mathrm{cb}}(A_{j})\to 2$, then
$\cond(V_{j})\to\infty$ for every choice of eigenvector matrices $V_{j}$.

Proof.

Choose a minimal scalar, column, or row extremal as in the proof of
Theorem 1.5. Apply
(4.8) to that scalar, column, or adjoint row
tuple. This gives (9.7). The final
assertion follows.
∎

Theorem 9.7.

Let $T\in\mathcal{B}(H)$ and assume that, for every $0<\tau<1$,

$\sum_{k=0}^{\infty}\tau^{2k}T^{*k}T^{k}\preceq\frac{1}{1-\tau}I,\qquad\sum_{k=0}^{\infty}\tau^{2k}T^{k}T^{*k}\preceq\frac{1}{1-\tau}I.$

Assume that $s=\left\lVert T\right\rVert>0$ is attained, and choose unit singular vectors
$x,y$ such that

$Tx=sy,\qquad T^{*}y=sx.$

Then $s\leq 2$ and

$\left\lVert T^{2}x\right\rVert,\ \left\lVert(T^{*})^{2}y\right\rVert\leq\vartheta(s).$

The estimate for $\left\lVert T^{2}x\right\rVert$ is sharp for every $0<s\leq 2$, already
among three-dimensional nilpotent weighted shifts. Taking adjoints gives
sharpness for $\left\lVert(T^{*})^{2}y\right\rVert$. More precisely,

$\vartheta(s)=\begin{cases}s^{2},&0<s\leq 3/2,\\
\eta(s),&3/2\leq s\leq 2.\end{cases}$

Proof.

Theorem 9.5, applied with $q=1$, gives
$s\leq 2$ and $\left\lVert T^{2}x\right\rVert\leq\vartheta(s)$. Applying the same theorem
to $T^{*}$ and $y$ gives
$\left\lVert(T^{*})^{2}y\right\rVert\leq\vartheta(s)$.

For $s>0$ and $a\geq 0$, let

$W_{s,a}=\begin{pmatrix}0&0&0\\
s&0&0\\
0&a&0\end{pmatrix}.$

Let $e_{1},e_{2},e_{3}$ be the standard basis vectors of $\mathbb{C}^{3}$. Then
$W_{s,a}e_{1}=se_{2}$, $W_{s,a}e_{2}=ae_{3}$, and

$\displaystyle\sum_{k=0}^{\infty}\tau^{2k}W_{s,a}^{*k}W_{s,a}^{k}$
$\displaystyle=\diag\bigl(1+s^{2}\tau^{2}+s^{2}a^{2}\tau^{4},1+a^{2}\tau^{2},1\bigr),$

$\displaystyle\sum_{k=0}^{\infty}\tau^{2k}W_{s,a}^{k}W_{s,a}^{*k}$
$\displaystyle=\diag\bigl(1,1+s^{2}\tau^{2},1+a^{2}\tau^{2}+s^{2}a^{2}\tau^{4}\bigr).$

Suppose first that $0<s\leq 3/2$ and take $a=s$. Put $b=s^{2}$ and

$R_{b}(\tau)=1-b\tau+b\tau^{2}-b^{2}\tau^{3}+b^{2}\tau^{4}.$

Since

$\frac{1}{1-\tau}-(1+b\tau^{2}+b^{2}\tau^{4})=\frac{\tau R_{b}(\tau)}{1-\tau}$

and

$\frac{\partial R_{b}(\tau)}{\partial b}=-\tau(1-\tau)(1+2b\tau^{2})\leq 0,$

one has

$R_{b}(\tau)\geq R_{9/4}(\tau)=\frac{(3\tau-2)^{2}(9\tau^{2}+3\tau+4)}{16}\geq 0.$

Thus $W_{s,s}$ satisfies both square-function estimates. Its norm is
$s$ and $\left\lVert W_{s,s}^{2}e_{1}\right\rVert=s^{2}$.

Now suppose that $3/2\leq s\leq 2$. Evaluating
(9.2) at $\tau=2/3$ gives

$\eta(s)^{2}\leq\frac{81}{8}-\frac{9}{4}s^{2}\leq s^{4}.$

Set $a=\eta(s)/s$. Then $0\leq a\leq s$, and the definition of
$\eta(s)$ gives

$1+s^{2}\tau^{2}+\eta(s)^{2}\tau^{4}\leq\frac{1}{1-\tau}\qquad(0<\tau<1).$

Each remaining diagonal entry of either square function is bounded by
$1+s^{2}\tau^{2}+\eta(s)^{2}\tau^{4}$ or by $1+s^{2}\tau^{2}$. Moreover,
$1+s^{2}\tau^{2}\leq(1-\tau)^{-1}$ because $s\leq 2$. Hence
$W_{s,a}$ satisfies both estimates, $\left\lVert W_{s,a}\right\rVert=s$, and

$\left\lVert W_{s,a}^{2}e_{1}\right\rVert=sa=\eta(s).$

This proves sharpness and the displayed formula for $\vartheta$.
∎

We next obtain an operator-norm estimate. More precisely, we choose a
two-dimensional subspace $\mathcal{M}$ and compare $T$ with
$\left(\begin{smallmatrix}0&0\\
2&0\end{smallmatrix}\right)\oplus D$
relative to the decomposition
$H=\mathcal{M}\oplus\mathcal{M}^{\perp}$.

Theorem 9.8.

Let $T\in\mathcal{B}(H)$ satisfy

$\sum_{k=0}^{\infty}4^{-k}T^{*k}T^{k}\preceq 2I,\qquad\sum_{k=0}^{\infty}4^{-k}T^{k}T^{*k}\preceq 2I.$

Assume that $\left\lVert T\right\rVert$ is attained, and put

$s=\left\lVert T\right\rVert,\qquad\delta=1-\frac{s^{2}}{4}.$

If $\delta\leq 1/16$, then there are an orthogonal decomposition
$H=\mathcal{M}\oplus\mathcal{M}^{\perp}$, with $\dim\mathcal{M}=2$, and an
operator $D\in\mathcal{B}(\mathcal{M}^{\perp})$ such that

$\left\lVert T-\left(\begin{pmatrix}0&0\\
2&0\end{pmatrix}\oplus D\right)\right\rVert\leq 8\sqrt{\delta}.$

The displayed $2\times 2$ matrix is written in a suitable orthonormal
basis of $\mathcal{M}$.

Proof.

Choose unit singular vectors $x,y$ such that

$Tx=sy,\qquad T^{*}y=sx.$

Since $s\geq\sqrt{15}/2>\sqrt{2}$, the vectors $x$ and $y$ are linearly
independent. Indeed, if $y$ were a constant of modulus one times $x$,
then the first square-function series on $x$ would be a geometric series
with ratio $s^{2}/4>1/2$, and its sum would be larger than $2$. Put

$\beta=\left\langle y,x\right\rangle,\qquad\rho=(1-\left\lvert\beta\right\rvert^{2})^{1/2},\qquad e=\frac{y-\beta x}{\rho},\qquad\mathcal{M}=\operatorname{span}\{x,e\}.$

Then $\{x,e\}$ is an orthonormal basis of $\mathcal{M}$ and
$y=\beta x+\rho e$. Let $P$ be the orthogonal projection onto
$\mathcal{M}$. Define $N$ on $\mathcal{M}$ by

$Nx=2e,\qquad Ne=0,$

and put $D=(I-P)T|_{\mathcal{M}^{\perp}}$.

First,

$(PTP-N)x=s\beta x+(s\rho-2)e,$

while

$\left\lVert(PTP-N)e\right\rVert\leq\frac{\left\lVert Ty\right\rVert+s\left\lvert\beta\right\rvert}{\rho}.$

Using the Hilbert–Schmidt norm of $(PTP-N)|_{\mathcal{M}}$ gives

(9.8)

$\left\lVert PTP-N\right\rVert\leq\left(s^{2}\left\lvert\beta\right\rvert^{2}+\left\lvert s\rho-2\right\rvert^{2}+\frac{(\left\lVert Ty\right\rVert+s\left\lvert\beta\right\rvert)^{2}}{\rho^{2}}\right)^{1/2}.$

Moreover,

(9.9)

$\left\lVert(I-P)TP\right\rVert\leq\frac{\left\lVert Ty\right\rVert}{\rho}.$

Indeed, $(I-P)TPx=0$, and the estimate on $e$ follows from
$e=(y-\beta x)/\rho$. If $w=(I-P)T^{*}x$, then

$(I-P)T^{*}Px=w,\qquad(I-P)T^{*}Pe=-\frac{\beta}{\rho}w,$

because $T^{*}y=sx$. Hence

(9.10)

$\left\lVert PT(I-P)\right\rVert\leq\frac{\left\lVert T^{*}x\right\rVert}{\rho}.$

The norm of
$PT(I-P)+(I-P)TP$ is the larger of the two bounds in
(9.9) and
(9.10).

The two square-function estimates give

$\left\lVert T^{2}x\right\rVert,\ \left\lVert(T^{*})^{2}y\right\rVert\leq 4\sqrt{\delta}.$

Since $T^{2}x=sTy$, $(T^{*})^{2}y=sT^{*}x$, and
$s^{2}=4(1-\delta)$, one obtains

$\left\lVert Ty\right\rVert,\ \left\lVert T^{*}x\right\rVert\leq\frac{11}{5}\sqrt{\delta},\qquad\left\lvert\beta\right\rvert\leq\frac{\sqrt{\delta}}{1-\delta}\leq\frac{4}{15}.$

Thus $\rho\geq 15/16$, $s\left\lvert\beta\right\rvert\leq(11/5)\sqrt{\delta}$, and

$2-s\rho\leq 2\delta+2\left\lvert\beta\right\rvert^{2}\leq\frac{11}{10}\sqrt{\delta}.$

It follows from (9.8) that

$\left\lVert PTP-N\right\rVert<\frac{28}{5}\sqrt{\delta},$

and $PT(I-P)+(I-P)TP$ has norm smaller than
$(12/5)\sqrt{\delta}$. The triangle inequality gives the stated bound.
∎

Corollary 9.9.

Let $A\in M_{n}(\mathbb{C})$ and let $f\in\mathcal{A}(W(A))$ satisfy
$\left\lVert f\right\rVert_{W(A)}=1$. If

$\left\lVert f(A)\right\rVert\geq 2-\varepsilon,\qquad 0\leq\varepsilon\leq 2-\frac{\sqrt{15}}{2},$

then there are an orthogonal decomposition
$\mathbb{C}^{n}=\mathcal{M}\oplus\mathcal{M}^{\perp}$, with
$\dim\mathcal{M}=2$, and a matrix $D$ on $\mathcal{M}^{\perp}$ such that

$\left\lVert f(A)-\left(\begin{pmatrix}0&0\\
2&0\end{pmatrix}\oplus D\right)\right\rVert\leq 8\sqrt{\varepsilon}.$

The displayed block is written in a suitable orthonormal basis of
$\mathcal{M}$.

Proof.

Put $T=f(A)$. The bound on $\varepsilon$ gives
$\left\lVert T\right\rVert\geq\sqrt{15}/2$, so Theorem 9.8
applies. Since

$1-\frac{\left\lVert T\right\rVert^{2}}{4}\leq 2-\left\lVert T\right\rVert\leq\varepsilon,$

the result follows.
∎

11. Polynomial equality and equality in dimension three

We first characterise equality for scalar polynomials in every finite
dimension. We then combine the scalar rigidity theorem with the
complete bound to classify equality in dimension three.

We write $A\simeq B$ for unitary similarity. For a matrix $A$, put
$w(A)=\max_{z\in W(A)}|z|$. For $m\geq 1$, let
$C_{m}\in M_{m+1}(\mathbb{C})$ have nonzero entries only on the first
superdiagonal. For $m=1$, its only nonzero entry is $2$. For $m\geq 2$,
its first and last superdiagonal entries are $\sqrt{2}$, and all
intervening entries are $1$. These are the Crabb–Choi–Crouzeix
matrices. They satisfy

$W(C_{m})=\overline{\mathbb{D}},\qquad\left\lVert C_{m}^{m}\right\rVert=2$

[22, Section 4].

Proposition 11.1.

Let $A\in M_{d}(\mathbb{C})$ satisfy $W(A)\subset\overline{\mathbb{D}}$, and let $p$ be
a nonzero polynomial. Then

$\left\lVert p(A)\right\rVert=2\max_{|z|\leq 1}|p(z)|$

if and only if there are $c\neq 0$ and an integer $1\leq m<d$ such that
$p(z)=cz^{m}$ and $A$ is unitarily similar to $C_{m}\oplus B$, where
$w(B)\leq 1$. The block $B$ is omitted when $m+1=d$.

Proof.

Divide $p$ by its supremum norm on $\overline{\mathbb{D}}$. Thus
$\left\lVert p\right\rVert_{\overline{\mathbb{D}}}=1$ and $\left\lVert p(A)\right\rVert=2$. Suppose that
$Av=\lambda v$, $\left\lVert v\right\rVert=1$, and $|\lambda|=1$. Since

$I-\Ree(\overline{\lambda}A)\geq 0,\qquad\left\langle(I-\Ree(\overline{\lambda}A))v,v\right\rangle=0,$

positivity gives $\Ree(\overline{\lambda}A)v=v$. It follows that
$A^{*}v=\overline{\lambda}v$, so $\mathbb{C}v$ reduces $A$. Removing these
reducing subspaces successively gives

$A\simeq A_{0}\oplus D,\qquad A_{0}\in M_{d_{0}}(\mathbb{C}),\qquad\sigma(A_{0})\subset\mathbb{D},$

where $D$ is diagonal and $\sigma(D)\subset\mathbb{T}$. Either block may be
absent before equality is used. Since $\left\lVert p(D)\right\rVert\leq 1$, equality
implies that $A_{0}$ is present and $\left\lVert p(A_{0})\right\rVert=2$.

Apply Proposition 10.1 to $(A_{0},\mathbb{D})$. Its
bound gives $\psi_{\mathbb{D}}(A_{0})\leq 2$, and $p$ attains equality. Thus $p$
is a normalized extremal function. By the same proposition, which
uses Crouzeix’s finite-dimensional extremal theorem
[10, Theorem 2.1], $p$ is a finite Blaschke product
of degree at most $d_{0}-1$. A polynomial finite Blaschke product
is a unimodular monomial. Indeed, any nonzero zero $\alpha\in\mathbb{D}$
in its Blaschke factorisation would produce a pole at
$1/\overline{\alpha}$, which cannot cancel against a numerator zero
in $\mathbb{D}$. Consequently $p(z)=\eta z^{m}$, where $|\eta|=1$. A constant
polynomial cannot have norm $2$ at $A_{0}$, so $1\leq m<d$.

Now $\left\lVert A^{m}\right\rVert=2$. The numerical-radius power inequality gives

$2=\left\lVert A^{m}\right\rVert\leq 2w(A^{m})\leq 2w(A)^{m}\leq 2,$

so $w(A)=1$. The equality theorem for powers, proved from Crabb’s
theorem in [22, Theorems 12 and 14], gives a
unitary decomposition $A\simeq C_{m}\oplus B$, with $w(B)\leq 1$.
This proves necessity and allows us to remove the normalization of
$p$.

Conversely, if $A\simeq C_{m}\oplus B$ and $w(B)\leq 1$, then
$W(A)=\overline{\mathbb{D}}$. The numerical-radius power inequality gives
$\left\lVert B^{m}\right\rVert\leq 2$, while $\left\lVert C_{m}^{m}\right\rVert=2$. Hence
$\left\lVert p(A)\right\rVert=2|c|=2\left\lVert p\right\rVert_{\overline{\mathbb{D}}}$ for $p(z)=cz^{m}$.
∎

Jin’s rigidity theorem states that $\psi(A)=2$ forces $W(A)$ to be a
nondegenerate disk in every finite dimension
[25, Theorem 1]. Together with the preceding
proposition, it gives the following classification. The matrix
decomposition for monomials is the theorem of Hnětynková and
Tichý cited above. The additional conclusion is that, after an
affine change of variable, every polynomial attaining equality must
be a monomial.

Theorem 11.2.

Let $A\in M_{d}(\mathbb{C})$ and let $p$ be a polynomial with $p(A)\neq 0$.
Then

$\left\lVert p(A)\right\rVert=2\max_{z\in W(A)}|p(z)|$

if and only if there are $a\in\mathbb{C}$, $r>0$, $c\neq 0$, and an integer
$1\leq m<d$ such that

$p(z)=c(z-a)^{m},\qquad A\simeq aI+r(C_{m}\oplus B),\qquad w(B)\leq 1.$

The block $B$ is omitted when $m+1=d$.

Proof.

Equality and the scalar bound give $\psi(A)=2$. Jin’s rigidity
theorem [25, Theorem 1] gives
$W(A)=a+r\overline{\mathbb{D}}$, with $r>0$. Put $T=(A-aI)/r$ and
$q(z)=p(a+rz)$. Proposition 11.1 gives
$q(z)=c_{0}z^{m}$ and $T\simeq C_{m}\oplus B$, with $1\leq m<d$ and
$w(B)\leq 1$. Therefore $p(z)=c_{0}r^{-m}(z-a)^{m}$, as required.
The converse follows from the converse in
Proposition 11.1 by the same affine change
of variable.
∎

The next consequence answers the degree question in
[20, Section 8.4].

Corollary 11.3.

Let $A\in M_{d}(\mathbb{C})$ and let $p$ be a polynomial with
$\deg p\geq d$ and $p(A)\neq 0$. Then

$\left\lVert p(A)\right\rVert<2\max_{z\in W(A)}|p(z)|.$

Proof.

The scalar bound gives the non-strict inequality. Equality would
give $\deg p<d$ by Theorem 11.2.
∎

In dimension three, Theorem 1.4
transfers Jin’s rigidity theorem to the complete constant.

Corollary 11.4.

Let $A\in M_{d}(\mathbb{C})$, where $d\leq 3$. If $W(A)$ is not a
nondegenerate disk, then $\psi_{\mathrm{cb}}(A)<2$.

Proof.

Theorem 1.1 gives
$\psi_{\mathrm{cb}}(A)\leq 2$. Equality would give $\psi(A)=2$ by
Theorem 1.4, and then $W(A)$ would be
a nondegenerate disk by [25, Theorem 1].
∎

Crouzeix classified the matrices of order three with unit-disk
numerical range and scalar constant two
[13, Lemma 10.2]. The preceding results remove the
disk assumption and give the complete equality classification.

Corollary 11.5.

For $A\in M_{3}(\mathbb{C})$, the following statements are equivalent.

(i) 

$\psi(A)=2$.

(ii) 

$\psi_{\mathrm{cb}}(A)=2$.

(iii) 

There are $a\in\mathbb{C}$ and $b\in\mathbb{C}\setminus\{0\}$ such that $A$
is unitarily similar to $aI+bB_{\xi}$ or $aI+bM_{s}$, where

$B_{\xi}=\begin{pmatrix}0&0&2\\
0&\xi&0\\
0&0&0\end{pmatrix},\qquad|\xi|\leq 1,$

and

$M_{s}=\begin{pmatrix}0&\sqrt{2(1-s^{2})}&2s\\
0&-s&\sqrt{2(1-s^{2})}\\
0&0&0\end{pmatrix},\qquad 0\leq s\leq 1.$

Proof.

Statements (i) and (ii) are equivalent by
Theorem 1.4. If (i) holds, Jin’s
rigidity theorem gives $W(A)=a+r\overline{\mathbb{D}}$, with $r>0$.
Apply [13, Lemma 10.2] to $(A-aI)/r$. Its two
families are precisely $B_{\xi}$ and $e^{i\vartheta}M_{s}$, with
$s=\sin\phi$, $0\leq\phi\leq\pi/2$. Absorbing the unimodular
factor into $b$ gives (iii). Conversely, the same lemma gives
$\psi(B_{\xi})=\psi(M_{s})=2$. Unitary similarity and a nonconstant
affine change preserve $\psi$, so (iii) implies (i).
∎

We finish with algebraic consequences of equality that apply in
arbitrary finite dimension. Write $r_{A}(\lambda)$ for the size of the
largest Jordan block of $A$ at $\lambda$, and put
$D(z_{0},r)=\{z\in\mathbb{C}:|z-z_{0}|<r\}$.

Lemma 11.6.

Let $A$ be a matrix and let $f$ be holomorphic on a neighborhood of
$\sigma(A)$. Then

$\alg(f(A))=\alg(A)$

if and only if

(i) 

$f$ is injective on $\sigma(A)$.

(ii) 

$f^{\prime}(\lambda)\neq 0$ whenever $r_{A}(\lambda)\geq 2$.

Proof.

The inclusion $\alg(f(A))\subset\alg(A)$ is automatic. Suppose first
that $A=q(f(A))$ for a polynomial $q$. If
$\lambda,\nu\in\sigma(A)$, then

$q(f(\lambda))=\lambda,\qquad q(f(\nu))=\nu.$

Thus $f$ is injective on $\sigma(A)$. If $r_{A}(\lambda)\geq 2$,
comparison of first derivatives on a Jordan block at $\lambda$ gives
$q^{\prime}(f(\lambda))f^{\prime}(\lambda)=1$.

Conversely, assume (i) and (ii). For each $\lambda\in\sigma(A)$, the
function $f$ has a local holomorphic inverse at $f(\lambda)$ when
$r_{A}(\lambda)\geq 2$. When $r_{A}(\lambda)=1$, only the value of an
inverse is needed. Since the points $f(\lambda)$ are distinct, Hermite
interpolation gives a polynomial $q$ whose derivatives through order
$r_{A}(\lambda)-1$ agree at $f(\lambda)$ with those of the corresponding
local inverse. It follows that $q(f(A))=A$.
∎

Theorem 11.7.

Let $A\in M_{n}(\mathbb{C})$ and let $\Omega$ be a bounded convex domain whose
boundary is a Jordan curve. Assume

$W(A)\subset\overline{\Omega},\qquad\sigma(A)\subset\Omega.$

Let $f\in\mathcal{A}(\overline{\Omega})$ satisfy

$\left\lVert f\right\rVert_{\overline{\Omega}}=1,\qquad\left\lVert f(A)\right\rVert=2.$

If $\alg(f(A))=\alg(A)$, then there are $z_{0}\in\Omega$ and $c\neq 0$
such that

$\Omega=z_{0}+c\mathbb{D},\qquad f(z_{0}+c\zeta)=\zeta\quad(\zeta\in\mathbb{D}).$

Proof.

Put $F=f(A)$. Theorem 1.3 gives

$2=\left\lVert F\right\rVert\leq 2\left\lVert f\right\rVert_{W(A)}\leq 2.$

Thus $F$ satisfies the two square-function estimates at $\tau=1/2$.
By Theorem 9.1, there is a two-dimensional reducing
subspace $V_{0}$ such that, in a suitable orthonormal basis,

$F|_{V_{0}}=N,\qquad N=\begin{pmatrix}0&0\\
2&0\end{pmatrix}.$

Choose a polynomial $q$ such that $A=q(F)$. Then $V_{0}$ also reduces
$A$, and

$A|_{V_{0}}=q(N)=z_{0}I+cN,\qquad z_{0}=q(0),\qquad c=q^{\prime}(0).$

The identity $f(A|_{V_{0}})=N$ gives
$f(z_{0})=0$ and $cf^{\prime}(z_{0})=1$. Hence $c\neq 0$. The number $z_{0}$ is the
eigenvalue of $A|_{V_{0}}$, so $z_{0}\in\sigma(A)\subset\Omega$.

Since $W(N)=\overline{\mathbb{D}}$,

$\{z:|z-z_{0}|\leq|c|\}=W(A|_{V_{0}})\subset W(A)\subset\overline{\Omega}.$

Convexity gives $D(z_{0},|c|)\subset\Omega$. The function
$g(\zeta)=f(z_{0}+c\zeta)$ satisfies $|g|\leq 1$ on $\mathbb{D}$. Since
$g^{\prime}(0)=1$, it is nonconstant, and the maximum principle shows that it
maps $\mathbb{D}$ into $\mathbb{D}$. Moreover, $g(0)=0$ and $g^{\prime}(0)=1$. Equality in
Schwarz’s lemma gives $g(\zeta)=\zeta$. The identity theorem gives
$f(z)=(z-z_{0})/c$ on $\Omega$. The bound $\left\lVert f\right\rVert_{\overline{\Omega}}=1$
then gives $\Omega\subset z_{0}+c\mathbb{D}$. The reverse inclusion was proved
above, so $\Omega=z_{0}+c\mathbb{D}$.
∎

Corollary 11.8.

Under the assumptions of Theorem 11.7, suppose that
$\Omega$ is not a disk. Then either

(i) 

$f(\lambda)=f(\nu)$ for two distinct eigenvalues
$\lambda,\nu\in\sigma(A)$, or

(ii) 

$f^{\prime}(\lambda)=0$ for some $\lambda\in\sigma(A)$ with
$r_{A}(\lambda)\geq 2$.

Proof.

Otherwise Lemma 11.6 would give
$\alg(f(A))=\alg(A)$, and Theorem 11.7 would imply
that $\Omega$ is a disk.
∎

Proposition 11.9.

Let $A$ be a matrix, and let $f\in\mathcal{A}(W(A))$ be holomorphic on a
neighborhood of $\sigma(A)$. Assume

$M=\max_{z\in W(A)}\left\lvert f(z)\right\rvert>0,\qquad\left\lVert f(A)\right\rVert=2M.$

Then there are an eigenvalue $\lambda$ of $A$, a Jordan block of size
$r$ at $\lambda$, and an integer $m\geq 1$ such that $f$ has a zero of
order $m$ at $\lambda$ and

(11.1)

$m<r<3m.$

Proof.

After replacing $f$ by $f/M$, Theorem 9.1 shows
that the Jordan form of $f(A)$ contains a block $J_{2}(0)$. Applying $f$
to the Jordan blocks of $A$, there must be a block $J_{r}(\lambda)$ for
which the Jordan form of $f(J_{r}(\lambda))$ contains $J_{2}(0)$. Hence
$f(\lambda)=0$. If the zero has order $m$, write

$f(J_{r}(\lambda))=N^{m}g(N),\qquad N=J_{r}(\lambda)-\lambda I,$

where $g(N)$ is invertible and commutes with $N$. For every $k\geq 1$,

$(N^{m}g(N))^{k}=N^{mk}g(N)^{k}.$

The matrix $g(N)^{k}$ is invertible and commutes with $N$. Hence
$(N^{m}g(N))^{k}$ and $N^{mk}$ have kernels of the same dimension for every
$k$, so $f(J_{r}(\lambda))$ and $N^{m}$ have the same Jordan block sizes.

Write $r=qm+s$, where $q\geq 0$ and $0\leq s<m$. The Jordan blocks
of $N^{m}$ have sizes $q+1$, repeated $s$ times, and $q$, repeated
$m-s$ times. Blocks of size zero are omitted. A block of size two
occurs
exactly when either $q=1$ and $s>0$, or $q=2$ and $s<m$. These
conditions are equivalent to (11.1).
∎


```

## External primary excerpt: https://arxiv.org/html/2002.01027v1

Selected HTML sections: S2.SS1. Equations use the HTML alttext.

```text


2.1 2 by 2 Nonnormal Matrices

For any 2 by 2 matrix $W(A)$ is an ellipse, and Crouzeix [4] proved that an exact expression for the supremum in (1) is

$C(W(A),2)=2\exp\left(-\displaystyle\sum_{n\geq 1}\dfrac{(-1)^{n+1}}{n}\dfrac{2}{1+\rho^{n}}\right),$

where

$~\rho=\dfrac{1+\sqrt{1-\epsilon^{2}}}{\epsilon},$

and $\epsilon$ is eccentricity of the ellipse $W(A)$. Here we give an equivalent expression for the bound $C(W(A),2)$ and prove that $\hat{B}$ (or $\hat{f}$) is unique.

It can be shown that, after a proper translation and rotation, any $2\times 2$ matrix $A\neq cI$ (trivial case) is unitarily similar to a matrix of the form

$\left[\begin{matrix}0&a\\
d&0\end{matrix}\right],$

where $a>0,d\geq 0$. If $a<d$, it is equivalent to consider $A^{T}$, so without loss of generality we can assume $a\geq d\geq 0$. The matrix $A$ is normal if and only if $a=d$, and in this case $||f(A)||_{2}\leq\max_{z\in W(A)}|f(z)|$; otherwise, $W(A)$ is an ellipse. G. Szegö[9] showed that the conformal mapping of the interior of an ellipse with foci points $\pm 1$ onto $\mathbb{D}$, with the origin mapping to itself, is

$\phi_{0}(z)=\sqrt{k}~\text{sn}\left(\dfrac{2K}{\pi}\sin^{-1}z\right).$

(4)

Here $\text{sn}(z)$ is one kind of Jacobi elliptical function, $k$ is the elliptical modulus and $K$ is the quarter period.
We can multiply $A$ by the scalar $\sqrt{k/(ad)}$ and write

$A=\left[\begin{matrix}0&\sqrt{\dfrac{k}{b}}\\
\sqrt{kb}&0\\
\end{matrix}\right],$

where $0\leq b=\frac{d}{a}\leq 1$ and $0<k=k(b^{2})<1$, and then, the conformal mapping maps $A$ to itself, since it maps the eigenvalues of $A$, $\pm\sqrt{k}$, to themselves.

$\phi(A)=A=\left[\begin{matrix}1&0\\
0&\sqrt{\dfrac{k}{b}}\end{matrix}\right]^{-1}\left[\begin{matrix}0&1\\
k&0\end{matrix}\right]\left[\begin{matrix}1&0\\
0&\sqrt{kb}\end{matrix}\right]=V^{-1}TV.$

Since $||T||_{2}=1$ and $\kappa(V)=\sqrt{k/b}$, for any Blaschke product $B$

$||B(\phi(A))||_{2}\leq\sqrt{\dfrac{k}{b}}$

by von Neumann’s inequality[8], and the equality holds when

$\hat{B}(z)=z.$

See Figure 2.1.

Further, the extremal $B$ is unique if $A$ is nonnormal ($a>d$ or $b<1$). Suppose an extremal $B$ is of the form

$B(z)=\dfrac{z-\alpha}{1-\bar{\alpha}z},~|\alpha|\leq 1,$

We will show that $\alpha$ must be 0.

From Theorem 5.1 in [2], an extremal Blaschke product $B$ satisfies

$B(\phi(A))v_{1}=||B(\phi(A))||_{2}u_{1},$

and

$u_{1}^{*}v_{1}=0,$

where $u_{1}$ and $v_{1}$ are the first left and right singular vectors of $B(\phi(A))$. Taking

$V=[v_{1}~v_{2}]=[v_{1}~u_{1}],$

we have

$V^{*}V=VV^{*}=I,$

and the diagonal elements of $V^{*}B(\phi(A))V$ are $0$, i.e., the eigenvalues of $V^{*}B(\phi(A))V$ or $B(\phi(A))$ are of the form $\pm\lambda$; i.e.,

$\dfrac{\sqrt{k}-\alpha}{1-\bar{\alpha}\sqrt{k}}=-\dfrac{-\sqrt{k}-\alpha}{1+\bar{\alpha}\sqrt{k}},~0<{k}\leq 1,$

which gives us

$\alpha=\bar{\alpha}k.$

When $0<b<1$, we know $0<k<1$ and

$\alpha=0;$

when $b=1$, we know $k=1$ and matrix A is normal.

Figure 2.1: $||\hat{B}(\phi(A))||_{2}=\sqrt{\frac{k}{b}}$ vs. $b$


```

## BCD 2006: complete ellipse similarity, Section 5.2

URL: https://arxiv.org/pdf/math/0501184

```text
5.2   The case of 2 × 2 matrices
We turn now to the case of 2 × 2 matrices. In this case it is known that the
numerical range is an ellipse whose foci are the eigenvalues. This ellipse is
degenerate only if the matrix is normal.

                                     21
Theorem 5.2. Let A be a 2 × 2 (non normal) matrix. Then there exists
a conformal function a mapping the ellipse W (A) onto the unit disk D and
an invertible matrix S such that kSk kS −1 k ≤ 2 and kS a(A) S −1 k ≤ 1.

Proof. If the eigenvalues of A are equal, then W (A) is a disk and the result
follows from (5.1). Suppose now that A has distinct eigenvalues. Since any
matrix is unitary similar to an upper triangular matrix, we can assume that
A is upper triangular. Furthermore, it is clear that if the theorem holds for
a matrix A, then it also holds for λA + βI for any λ 6=0 and β∈ C. Finally,
                                                          1 γ
we only have to look at matrices of the form A =                   and we can
                                                          0 −1
furthermore assume that γ > 0. Then W (A) is the ellipse of foci 1, −1 and
minor axis γ (see [13] for instance). If ρ > 1 is chosen such that γ = ρ − 1/ρ,
then the major axis is ρ + 1/ρ. Also (see [15]), the function

                           2z       X (−1)n+1 2 t2n (z) 
                 a(z) =       exp −                       ,
                            ρ            n    1 + ρ4n
                                       n≥1

where tn denotes the nth Chebyshev polynomial, is the Riemann confor-
mal function mapping (the interior of) W (A) onto D. Notice that a(1) =
−a(−1); thus a(A) = a(1)A.
   We choose now
                          1 + a(1)2 a(1)2 ρ − 1/ρ
                                                  
                   S=                                ;
                              0      a(1)(ρ + 1/ρ)

then we have
                                               a(1) 1−a(1)2
                                                           
                                  −1
                   B := Sa(A)S         =                      .
                                                0    −a(1)
It is easy to verify that kBk = 1. Some simple computations show that the
quantity kSk kS −1 k is the largest root of the equation

                             1 + ρ2 a(1)2
                      X2 −                X + 1 = 0,
                                ρ a(1)
                                    P           (−1)n+1   2
                                                             
which is X = ρ a(1) = 2 exp −           n≥1        n    1+ρ4n . It is easy to verify
that 1 < X < 2.

Corollary 5.3. In the two dimensional case we have

                      sup Ccb (Ω, 2) = sup C(Ω, 2) = 2.
                       Ω                   Ω


                                        22
Proof. We know from the previous subsection that C(D, 2) = 2, thus it is
sufficient to prove, for any 2 × 2 matrix A, that Ccb (W (A), 2) ≤ 2. Let
R be a rational function bounded in W (A) ; we set Q(z) = R(a−1 (z)) and
B = S a(A) S −1 . We have

                     R(A) = Q(a(A)) = S −1 Q(B)S.

Using the von Neumann inequality for the contraction B, we obtain

        kR(A)k ≤ 2 kQ(B)k ≤ 2 sup kQ(z)k = 2        sup kR(ζ)k;
                                   z∈D            ζ∈W (A)

thus Ccb (W (A), 2) ≤ 2.

Remark 5.1. The equality C(Ω, 2) = Ccb (Ω, 2) follows also from [23].

5.3    The case of ellipses
Theorem 5.4. Let E be (the interior of ) an ellipse in C with foci µ1 and
µ2 and let γ be the length of the minor axis. Let A be an
```
