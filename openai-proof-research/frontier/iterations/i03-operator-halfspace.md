# Round 3: explicit invariant half-spaces for the dyadic sum

Date: 2026-10-08. Status: **the specified operator has explicit ordinary invariant half-spaces, for every measurable $a$ with $1\leq a\leq2$ a.e.** This eliminates this entire candidate family as counterexamples to the ordinary Hilbert-space invariant-subspace problem. It does **not** meet the project's substantial-new-theorem success gate. The proof is an elementary weighted reflection argument, and no new-to-literature claim is made.

This report does not audit the earlier report or its sections 3–7. The independent review is left untouched. No conclusion about quasinilpotence, point spectra, finite multicyclicity, or finite-rank perturbations from that report is needed below. In particular, none of those conclusions is used to manufacture the half-space.

## 1. Source contract and exact operator

Rules read: `AGENTS.md`, `sources/upstream.json`, `frontier/iterations/README.md`; the manuscript catalogue and previous construction report were also consulted. All pinned upstream theorems are accepted premises.

The revision is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The actual source is *Backward intertwiners and a transitive commutant*, especially `build/sections/weights.tex` (definitions of $a_j,\beta_j,w_j$) and `build/sections/intertwiner.tex` (equations `eq:b-recursion`, `eq:commuting-coefficients`, `eq:V-definition`, and Lemma `lem:normalization`). The complete relevant sections, including the actual normalizer, are cached in [the round-3 sources](../sources/i03_operator/). Their pinned raw URLs, SHA-256 and Git blob hashes are in [upstream_manifest.json](../sources/i03_operator/upstream_manifest.json).

Let $X=\mathbb Z_2$, with Haar probability measure, $E=L^2(X)$, and $H=\ell^2(\mathbb Z;E)$. All functions and identities below are modulo null sets. The actual operators are
\[
 (Sf)_j(x)=\beta_{j-1}(x)f_{j-1}(x),\qquad
 (Vf)_j(x)=b_{j+1}(x-1)f_{j+1}(x-1).
\]
Here $\beta_j=e^{-a_j}>0$, $\beta_{-1}=\beta_0=e^{-10}$, and
\[
 w_0=1,\qquad w_{j+1}=\beta_j w_j\quad(j\in\mathbb Z).
\tag{1}
\]
For every **fixed** $j$, both $w_j$ and $1/w_j$ belong to $L^\infty(X)$. Indeed each $a_j$ is a bounded function of finitely many residues, and each $w_j$ is a finite product of weights or their reciprocals. In particular $w_{-1}=e^{10}$ and $w_1=e^{-10}$. There is no uniform boundedness assertion as $j$ varies.

The source defines $\widetilde b_0=1$,
\[
 \widetilde b_{j+1}(x)\beta_j(x)
 =\widetilde b_j(x)\beta_{j-1}(x+1),\qquad
 L(x)=\sup_{j\in\mathbb Z}\widetilde b_j(x).
\]
On the source's translation-invariant conull set $X_*$, $1\leq L(x)<\infty$ and $b_j=\widetilde b_j/L$. Off $X_*$, $b_j=0$. We use **this exact $L$**, not a finite-coordinate maximum or a substitute normalization.

Fix any real measurable $a$ satisfying $1\leq a\leq2$ a.e., and put
\[
 T=T_a=S+M_a V.
\tag{2}
\]
This is bounded since $\|S\|=e^{-10}$, $\|V\|\leq1$, and $\|M_a\|\leq2$. The multiplier $M_a$ acts at the output base point. Thus its contribution to the displayed formula for $V$ is $a(x)$, not $a(x-1)$.

## 2. Exact coordinate identity, without a global similarity

Define a bounded operator on $E$ by
\[
 (Cg)(x)=q(x)g(x-1),\qquad
 q(x)=\frac{e^{-10}a(x)}{L(x-1)}.
\tag{3}
\]
Set $q=0$ on the irrelevant exceptional null set. Then $0<q\leq2e^{-10}$ a.e. Consequently $C$ is bounded, injective, and has dense range: translation is unitary and multiplication by a bounded function positive a.e. is injective with dense range. The same statements hold for each positive power $C^j$. No bounded inverse of $C$ is asserted.

The recurrence and (1) imply
\[
 \frac{b_{j+1}(x)w_{j+1}(x)}{w_j(x+1)}
 =\frac{b_j(x)w_j(x)}{w_{j-1}(x+1)}
 =\frac{e^{-10}}{L(x)}
 \quad(j\in\mathbb Z).
\tag{4}
\]
For the first equality substitute $w_{j+1}=\beta_jw_j$ and $w_j(x+1)=\beta_{j-1}(x+1)w_{j-1}(x+1)$. The constant is evaluated at $j=0$, using $b_0=1/L$ and $w_{-1}=e^{10}$. Thus the identity holds at every integer index, not only nonnegative ones.

For $f\in H$, write $h_j=w_j^{-1}f_j\in E$, separately for each $j$. Equation (4), with $x$ replaced by $x-1$, gives
\[
 w_j^{-1}(Tf)_j=h_{j-1}+Ch_{j+1}.
\tag{5}
\]
These are identities in $E$, valid for every fixed coordinate. The sequence $(h_j)$ is **not assumed to belong to unweighted $\ell^2(\mathbb Z;E)$**. In particular, (5) is not being used as a bounded similarity of $T$ with a constant-coefficient Laurent operator. All subsequent closure arguments take place in the original $H$.

## 3. A closed invariant half-space

**Proposition.** For every $a$ as above,
\[
 \mathcal M_+=\left\{f\in H:
       w_{-j}^{-1}f_{-j}=C^j w_j^{-1}f_j
       \text{ for every }j\geq1\right\}
\tag{6}
\]
is a closed $T_a$-invariant subspace of infinite dimension and infinite codimension.

**Closedness.** For every fixed $j\geq1$, the map
\[
 \Lambda_j:H\longrightarrow E,\qquad
 \Lambda_j f=w_{-j}^{-1}f_{-j}-C^j w_j^{-1}f_j
\]
is bounded. Therefore $\mathcal M_+=\bigcap_{j\geq1}\ker\Lambda_j$ is closed. No uniform bound on $\|\Lambda_j\|$ is necessary.

**Infinite dimension.** Every vector supported at coordinate $0$ belongs to $\mathcal M_+$. This is a copy of the infinite-dimensional space $E$.

**Properness and infinite codimension.** The map $\Lambda_1$ is onto $E$: given $g\in E$, use the vector with $f_{-1}=w_{-1}g$ and all other coordinates zero. Since $\mathcal M_+\subseteq\ker\Lambda_1$, the induced bounded map $H/\mathcal M_+\to E$ is onto. Hence $H/\mathcal M_+$ is infinite-dimensional. For a closed Hilbert subspace this is exactly infinite codimension. In particular a nonzero vector supported only at coordinate $-1$ lies outside $\mathcal M_+$.

**Invariance.** Take $f\in\mathcal M_+$, set $h_j=w_j^{-1}f_j$, and let $k_j=w_j^{-1}(Tf)_j$. For $j\geq2$, (5) gives
\[
 \begin{aligned}
 k_{-j}
 &=h_{-(j+1)}+Ch_{-(j-1)}\\
 &=C^{j+1}h_{j+1}+C^j h_{j-1}
 =C^j k_j.
 \end{aligned}
\]
At the boundary index $j=1$,
\[
 k_{-1}=h_{-2}+Ch_0=C^2h_2+Ch_0=Ck_1.
\]
Since $Tf\in H$ by boundedness of $T$, these identities show $Tf\in\mathcal M_+$. This proves the proposition. \$\square$

For a completely explicit version of the defining relation, put
\[
 K_j=M_{w_{-j}} C^j M_{1/w_j}.
\]
Each $K_j:E\to E$ is bounded, and (6) says $f_{-j}=K_jf_j$. Its formula is
\[
 (K_jg)(x)=
 \frac{e^{-10j}w_{-j}(x)}{w_j(x-j)}
 \left(\prod_{r=0}^{j-1}\frac{a(x-r)}{L(x-r-1)}\right)g(x-j).
\tag{7}
\]
Thus the half-space is expressed directly in the original normalized dyadic data.

The proof of this proposition actually works for every bounded complex $a$, including those with zeros; only boundedness of $C$ is needed for the proposition. Positivity, injectivity, and dense range are used in some additional conclusions below. The requested $1\leq a\leq2$ family is fully covered.

## 4. Orbit closure and a second half-space

There is a useful exact description that also closes the orbit-closure route:
\[
 \mathcal M_+=\overline{\operatorname{span}}
       \{T^n(g\otimes e_0):g\in E,\ n\geq0\}.
\tag{8}
\]
The inclusion from right to left follows from Section 3. To prove the reverse inclusion, first note that truncating $f\in\mathcal M_+$ to coordinates $[-N,N]$ preserves all its defining relations and converges to $f$ in $H$.

Let $P_n(g)$, for $n\geq1$, be the finite vector whose normalized coordinates are $h_n=g$, $h_{-n}=C^ng$, with all others zero; let $P_0(g)=g\otimes e_0$. Repeated use of (5) gives the finite algebraic formula
\[
 w_{n-2\ell}^{-1}\big(T^n(g\otimes e_0)\big)_{n-2\ell}
    ={n\choose\ell}C^\ell g\qquad(0\leq\ell\leq n).
\tag{9}
\]
Group the terms with opposite coordinates. Their leading pair is $P_n(g)$, and every remaining pair is some $P_{n-2\ell}({n\choose\ell}C^\ell g)$ with smaller nonnegative index (including the single central term when $n$ is even). Induction on $n$ therefore puts every $P_n(g)$ in the span on the right of (8). Every finite truncation from the previous paragraph is a finite sum of such vectors. This proves (8) without any finite-to-infinite cyclicity inference.

There is also an antisymmetric companion:
\[
 \mathcal M_-=\{f\in H:h_0=0,\ h_{-j}=-C^j h_j\ (j\geq1)\}.
\tag{10}
\]
It is closed by the same bounded-coordinate-map argument. It contains all vectors with $h_1=g,h_{-1}=-Cg$ and other coordinates zero, so is infinite-dimensional. Its codimension is infinite because the coordinate-zero map vanishes on it and maps $H$ onto $E$.

For invariance, the calculation in Section 3 acquires a minus sign for $j\geq2$. At the remaining indices,
\[
 k_0=h_{-1}+Ch_1=0,\qquad
 k_{-1}=-C^2h_2=-Ck_1
\]
because $h_0=0$. Hence $T\mathcal M_-\subseteq\mathcal M_-$.

For $1\leq a\leq2$, injectivity of $C$ shows $\mathcal M_+\cap\mathcal M_-=\{0\}$. Their sum is dense: for a finite pair of target normalized coordinates $(h_j,h_{-j})=(u,v)$, choose $r$ with $C^jr$ arbitrarily close to $v$, and set $p=(u+r)/2$, $s=(u-r)/2$. The sum of the plus-pair generated by $p$ and the minus-pair generated by $s$ has positive coordinate $u$ and negative coordinate $C^jr$. Fixed-coordinate multiplication by $w_{-j}$ preserves convergence. Finite-coordinate vectors are dense in $H$. **No claim is made that this sum is closed, that it is an orthogonal decomposition, or that the associated reflection extends to a bounded involution.**

## 5. What kind of subspace this is

Each $K_j$ in (7) is a positive weighted composition operator, so $K_j|g|=|K_jg|$. Consequently $\mathcal M_+$ is a closed vector sublattice in the natural function lattice $H$. It is not an ideal: take $f_1=1,f_{-1}=K_1 1$, with other coordinates zero. Then $f\in\mathcal M_+$ is positive, whereas retaining only its nonzero negative coordinate gives $0\leq v\leq f$ with $v\notin\mathcal M_+$. Therefore an absence-of-invariant-ideals result would not exclude this half-space.

It is not hyperinvariant for $T$. Indeed $S$ commutes with $T=S+M_aV$, since $S$ commutes with both $V$ and $M_a$. But if $g\ne0$, then $g\otimes e_0\in\mathcal M_+$ and $S(g\otimes e_0)$ has only normalized coordinate $h_1=g$. It violates (6) because $Cg\ne0$. Thus it is not even $S$-invariant. Neither von Neumann algebra generation nor recovery of $S$ by analytic polynomials in $T$ has been assumed.

The suggested variable $y=2x+j$ is consistent with the proof: the points $(-j,x)$ and $(j,x-j)$ paired in (7) have the same $y$. Both steps of $T$ increase $y$ by one. The actual mechanism is the bounded-coordinate graph relation and its boundary identity at $j=1$, not this reparameterization. The constructed spaces are $T$-invariant, not merely invariant under $T^2$ on parity components.

## 6. Positive-operator and growth prior art: hypotheses checked

Primary literature was checked early, before using any positivity shortcut. It is not an input to the proof above.

- Abramovich–Aliprantis–Burkinshaw, *Invariant Subspace Theorems for Positive Operators*, JFA 124 (1994), 95–111, [publisher record and abstract](https://www.sciencedirect.com/science/article/pii/S0022123684710998), [DOI](https://doi.org/10.1006/jfan.1994.1099). The abstract supplies sufficient conditions involving compact domination, a commuting positive kernel operator, or a quasinilpotent Dunford–Pettis operator. It does not state that positivity and quasinilpotence on an arbitrary nonatomic lattice suffice. Only the primary abstract was available in this check; no full-text theorem beyond it is invoked.
- V. G. Troitsky, *A remark on invariant subspaces of positive operators*, Proc. AMS 141 (2013), 4345–4348, [DOI](https://doi.org/10.1090/S0002-9939-2013-11709-0), [author manuscript](https://www.math.ualberta.ca/~vtroitsky/papers/math/done/positive-non-qnilp-is/positive-non-qnilp-is.pdf), Theorem 1. Its chain is $A\leftrightarrow B\leftrightarrow R\leq K$, with all four operators positive and nonzero, $B$ nonscalar and $K$ compact; it concludes that $A$ has an invariant subspace. The compact upper bound on a suitable $R$ is essential to the stated hypothesis. The primary search extract included the theorem, but direct downloads returned HTTP 403; the complete paper is not represented as locally cached or fully read.
- V. Gillet, *Typical properties of positive contractions and the invariant subspace problem*, [arXiv:2409.14481v1](https://arxiv.org/abs/2409.14481v1), definition on p. 1, Theorem 1.1 and Corollary 1.2. The full primary PDF and text were retrieved. Positivity there is defined relative to the coefficients of the specified basis. Its commuting locally quasinilpotent positive-operator criterion cannot be applied just because our nonatomic $L^2$ happens to admit a Hilbert basis: positivity relative to that basis has not been established. The natural nonatomic lattice is not an atomic coordinate lattice.
- C. Hu and Y. Ji, *Power Set of Some Quasinilpotent Weighted shifts on $l^p$*, [arXiv:2306.00387v1](https://arxiv.org/abs/2306.00387v1), Proposition 1.2 and the following paragraph. The full primary paper distinguishes linear hyperinvariant growth sets from closed ones and records failures of closedness. A growth exponent or a separation of formal orbit rates alone therefore does not supply a closed subspace. No such inference is made here; Section 4 identifies the orbit closure exactly.

The accessible PDFs, extracted text, download errors, URLs, and hashes are recorded in [literature_manifest.json](../sources/i03_operator/literature_manifest.json). In particular, failed PDF requests were not treated as successful full-text retrievals.

Here are concrete checks preventing inappropriate use of the extra hypotheses.

**Compactness and Dunford–Pettis.** Let $r_n(x)=(-1)^{\epsilon_n(x)}$, where $\epsilon_n$ is the $n$-th binary digit. These are orthonormal in $E$, hence weakly null. For $f_n=r_n\otimes e_0$, the coordinate $1$ of $Tf_n$ is $e^{-10}r_n$. Thus $\|Tf_n\|\geq e^{-10}$: $T$ is neither compact nor Dunford–Pettis (weakly-null sequences need not be sent to norm-null sequences). All the real $f_n$ belong to the order interval $[-1\otimes e_0,1\otimes e_0]$; their image distances are at least $\sqrt2e^{-10}$. Thus $T$ is not AM-compact either. More generally the coordinate $m$ of $T^mf_n$ is $w_m r_n$, since reaching $m$ in $m$ steps requires every step to be forward. The fixed-coordinate lower bound $\operatorname{ess\,inf}w_m>0$ proves the same noncompactness and non-Dunford–Pettis assertions for every positive power.

**Positive compact domination.** There is no nonzero positive compact $K\leq T$. To see this, decompose into input and output coordinate blocks. Positivity and domination force every block of $K$ to vanish except the two blocks allowed by $T$ in each column. Each remaining block is compact and dominated by a positive weighted composition $M_dU$ on $E$, with $U$ an invertible positive translation. After composing with $U^{-1}$, it is a positive compact operator $B\leq M_d$. Such $B$ preserves supports: for $g\geq0$ supported in a measurable set $A$, $0\leq Bg\leq dg$. On a probability space this implies $B1_A=1_A B1$, and by simple-function approximation $B=M_b$ for $b=B1$. A nonzero multiplication operator on nonatomic $L^2$ is not compact: a set on which $|b|\geq\varepsilon>0$ supplies an infinite orthonormal sequence of normalized disjoint indicators. Hence every block is zero and $K=0$.

Nor is $T\leq K$ possible for a positive compact $K$. Its input-zero/output-one corner would be a positive compact operator on $E$ dominating $e^{-10}I_E$. Normalized disjoint positive indicators contradict compactness. These observations concern domination by or of $T$ itself; they do not exclude every possible auxiliary chain in Troitsky's theorem. No such auxiliary chain was established or needed.

**Kernel assumption.** In the usual measurable integral-kernel sense on the given nonatomic measure space, $T$ is not a positive kernel operator. Its zero-to-one corner is $e^{-10}I_E$. If the identity had a positive measurable integral kernel, applying it to indicators in a countable generating algebra would require almost every kernel row to be the point mass at its base point, which is not absolutely continuous with respect to nonatomic Haar measure. This does not exclude the possible existence of some different positive kernel operator commuting with $T$; no such witness is asserted.

## 7. Algebraic checks and final novelty screen

[check_halfspace.py](../experiments/i03_operator/check_halfspace.py) uses only the Python standard library. It passed:

- 76,864 exact integer-log checks of the *unnormalized* identity behind (4), covering $x=0,\ldots,63$ and $j=-600,\ldots,600$, including weight-block boundaries;
- 21 exact rational block-commutation identities and 70 symmetric/antisymmetric output relations using noncommuting $2\times2$ coordinate weights;
- the central Laurent/binomial formula for powers $0$ through $10$.

The output includes both newly reached outer coordinates, so no artificial truncation boundary is used. The script never substitutes a finite maximum for $L$. These are transcription checks only; the universal identities and all infinite-dimensional closure and codimension claims are proved in Sections 2–4. Results are in [output.json](../experiments/i03_operator/output.json). Local input hashes are in [input_manifest.json](../sources/i03_operator/input_manifest.json); primary-source access limits are recorded in [primary_screen.json](../sources/i03_operator/primary_screen.json).

The argument needs little of the special dyadic asymptotics. Abstractly, let bounded bilateral forward and backward operator-weighted shifts $A,D$ commute, with each forward block $A_j:E\to E$ individually boundedly invertible. Normalize $W_0=I$, $W_{j+1}=A_jW_j$. If $D_j$ is the backward block from $j$ to $j-1$, commutation says $A_{j-1}D_j=D_{j+1}A_j$, so
\[
 W_{j-1}^{-1}D_jW_j=C
\]
is independent of $j$. The same coordinate proof constructs (6) for $A+D$, with $w_j$ replaced by $W_j$. This elementary commuting-shift reflection mechanism explains why the result should be classified as a candidate obstruction rather than a substantial advance on ISP. It does not assert the direct sum of the $W_j$ is bounded or invertible.

A final screen checked the actual relevant pinned manuscript and its companion *Invariant projection counterexamples for every irrational rotation*, including the main theorem/corollaries in `00-introduction.tex` and the atomic/diffuse distinctions in `product-structure.tex`. Four full dyadic sections and fourteen companion source files were retrieved and hash-verified; the source manifest enumerates them. The companion's obstruction is about invariant projections in its specified factor, not the assertion that this $T_a$ has no ordinary invariant half-space. Neither inspected manuscript states the present reflection half-space for $S+M_aV$. This is a bounded relevant-source screen, not a claim to have read every manuscript in the corpus.

The primary external screen also found Tang–Gu–Lu–Shi, *Reducing subspaces for the product of a forward and a backward operator-weighted shifts*, JMAA 501 (2021), 125206, [publisher article](https://www.sciencedirect.com/science/article/abs/pii/S0022247X21002857), [DOI](https://doi.org/10.1016/j.jmaa.2021.125206). Its abstract concerns products $S_2^*S_1$ and $S_1S_2^*$ for multivariable shifts, not the present sum; only the primary abstract/introduction extract was inspected. Searches for commuting forward/backward sums and Laurent reflection did not identify an exact prior statement of (6). That search outcome is not evidence of substantial novelty. The construction is the familiar algebraic symmetry of the expression $z+Cz^{-1}$, with its only necessary analytic care supplied by fixed-coordinate boundedness.

**Disposition.** There is no remaining existence, closure, invariance, or properness gap for an ordinary invariant half-space of the specified $T_a$: (6) and (10) provide two. There remains no demonstrated substantial new theorem toward the high-importance MathDB objective. Classification of the entire invariant-subspace lattice, closedness of $\mathcal M_++\mathcal M_-$, and any different operator construction are not settled here. The broader research objective stays open; this report closes only the candidate-specific ordinary-subspace question.
