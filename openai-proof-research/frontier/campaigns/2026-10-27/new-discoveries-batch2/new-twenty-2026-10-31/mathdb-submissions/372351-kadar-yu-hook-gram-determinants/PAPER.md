# One-cup Gram determinants of Kadar–Yu cell modules for hooks: a corrected form of Morris–Martin Conjecture 3.31.1, with a written proof and a machine-checked proof

*Revised manuscript (revision r1 of the residual-core manuscript). Section numbers below are those of this revision; `CHANGES.md` maps every referee item to them.*

## Abstract

Morris and Martin (arXiv:2512.24535v1, Conjecture 3.31.1, p. 31) conjecture closed formulas (3.3.7)–(3.3.10) for the Gram determinants of the one-cup cell modules indexed by the hook $(a+1,1)$ and its transpose $(2,1^a)$. The formulas consist of a monic constant factor $C$ and a Chebyshev series $P$.

**(a) Literal statement.** As printed, the conjecture is false. At height $a=5$ and tail length $k=0$ the determinant has degree $174$, while the product of the printed (3.3.7) and (3.3.9) has degree $166$ (§3.1).

**(b) Corrected statement.** We prove corrected formulas for both hook families: the ordinary hook for every $a\ge 2$, the transposed hook for every $a\ge 1$, and in both cases every $k\ge 0$. The corrections are as follows. In (3.3.7) the exponent of $x$ becomes $(a+3)(a+2)(a-2)/6$. In (3.3.10) the missing operator is a plus. The recurrence is used with the minus sign of (3.1.2)–(3.1.3) and (3.2.9), not the plus printed in (3.1.1). Formulas (3.3.8) and (3.3.9) stand as printed (§3.2).

The theorem is kernel-checked in Lean 4 with Mathlib (58 modules, axioms `propext`, `Classical.choice`, `Quot.sound` only). This revision also gives a complete written proof. The proof evaluates the full core of the one-cup Gram matrix and its marked boundary resolvent. It uses an exact factorization of the core through ordered pairs and triples of sites, followed by a short Sylvester/Schur chain that ends in a $2\times2$ block matrix in the span of $I$ and the all-ones matrix $J$. An independent exact-arithmetic script (`scripts/verify_brauer_hook.py`) recomputes the Gram determinants from the source's diagram definitions and checks the matrix identities and determinant formulas at the finite ranges listed in §6, alongside symbolic checks of the scalar algebra.

---

## 1. Source statement and conventions

### 1.1 The conjecture, quoted

Source: B. Morris and P. Martin, *On semisimplicity criteria and non-semisimple representation theory for the Kadar–Yu algebras*, arXiv:2512.24535v1 [math.RT], 31 Dec 2025, p. 31. We used the PDF fetched from `arxiv.org/pdf/2512.24535v1`, SHA-256 `2d6f180bf33021ca6ab819928dfe51c91d44bed2eba8ccf03d2e443ed6bf5c86`, which is the same file the earlier lane recorded. The source writes $\alpha$ for the loop parameter; we write $x$. The source writes $l,l',l''$ for the height; we write $a$ in each clause.

> **Conjecture 3.31.1.** Formulae (3.3.7),(3.3.8),(3.3.9), and (3.3.10), hold for all $l \ge 1$, $l' \ge 4$ and $l'' \ge 2$.

The four displays, with the ranges printed beside them, are as follows.

* (3.3.7), ordinary hook $(l'+1,1)$, "valid for $l'\ge 4$":
$$C^{(a+1,1)}=(x-3)^{\frac{(a-1)(a+1)(a+3)}3}(x-2)^{\frac{(a-1)(a+2)}2}\,x^{\frac{a(a+3)}2}\,(x+a-3)^{\frac{a(a+1)}2}(x+a-1)^{\frac{(a+1)(a+2)}2}(x+2a)(x+2a+2).$$
* (3.3.8), transposed hook $(l+1,1)^T=(2,1^l)$, "holds for $l\ge 1$":
$$C^{(a+1,1)^T}=(x+4)^{\frac{a(a+1)(a+2)}6}(x+2)^{\frac{a(a+1)}2}(x+1)^{\frac{(a-1)(a+1)(a+3)}3}(x-a+1)^{\frac{a(a+1)}2}(x-a-1)^{\frac{(a+1)(a+2)}2}.$$
* (3.3.9), ordinary hook, "holds for $l''\ge 2$":
$$P^{(a+1,1)}_{a+4+k}=P^U_{k+6}+2(2a-3)P^U_{k+5}+(5a^2-21a+13)P^U_{k+4}+(a-2)\bigl[(2a^2-17a+7)P^U_{k+3}-(6a^2-19a+5)P^U_{k+2}\bigr]$$
$$\qquad+4(a^3-6a^2+8a-1)P^U_{k+1}-(a-3)(2a^2-4a-1)P^U_k-(3a^2-3a-4)P^U_{k-1}-(a+1)P^U_{k-2}.$$
* (3.3.10), transposed hook, "holds for $l\ge 1$". The rendered text is
$$P^{(a+1,1)^T}_{a+4+k}=P^U_{k+5}-2(a-1)P^U_{k+4}+a(a-5)P^U_{k+3}+3a(a-1)P^U_{k+2}\quad[\text{line break}]\quad 2(a^2-2a-1)P^U_{k+1}+a(a-1)P^U_k-(a+1)P^U_{k-1}.$$
  No operator joins the two lines.

The normal form is that of Theorem 3.19. For $n\ge l+4$ we have $D^{(n)}_{(n-2,\lambda)}=C^{(\lambda)}\,(P^{(\lambda)}_n)^{d_\lambda}$ up to an overall complex scalar, with $C$ monic and $P$ a Chebyshev series with the ramping property (reduced, and for $n\ge l+4$ monic with degree increasing by one; source (3.7)). We write $n=a+4+k$, so the Gram range is $k\ge 0$. The conjecture does not quantify $k$ separately. The source's Remark 3.33 states that $P$ at lower indices is the unique bilateral extension by the recurrence.

### 1.2 Chebyshev convention and the sign in (3.1.1)

We use $P^U_j=U_{j-1}(x/2)$ for all $j\in\mathbb Z$. Thus $P^U_0=0$, $P^U_1=1$, $P^U_{j+1}=xP^U_j-P^U_{j-1}$ and $P^U_{-j}=-P^U_j$ (Lean `nativeU`, `nativeU_step`, `nativeU_neg`). The source prints the recurrence in (3.1.1) as $P_{n+1}=xP_n+P_{n-1}$. That plus sign conflicts with the rest of the source:

* the definition (3.1.2) $U_n(\cos\theta)\sin\theta=\sin((n+1)\theta)$;
* the examples in (3.4), $P_3=x^2-1$ and $P_4=x(x^2-2)$;
* the negative-index rule (3.1.3);
* the tridiagonal expansion (3.2.7);
* the path recurrence (3.2.9), $\det\Gamma_{l,n+2e_k}=\alpha\det\Gamma_{l,n+e_k}-\det\Gamma_{l,n}$.

The Gram tail forces the minus sign (Lemma 5.2). We use the minus sign throughout, and treat the printed plus in (3.1.1) as a separate typographical defect.

---

## 2. The native model

Everything is stated in the native model of the source's §3.2.1, with sites numbered from zero. The identification of each item below with the source's definitions was carried out by the earlier lane (`NATIVE-CLAUSE-CROSSWALK.md` in `brauer-hook-372351-native-determinants-formal-sol62-20261118-r1`). It is formalized in the inherited modules `CupDiagram`, `HookFiber`, `TransposedFiber`, `PairingBridge` and `NativeGram`, and recomputed from the source's definitions by our script for small parameters (§6, check N1).

**2.1 Rank and cups.** Fix a height $a\ge 1$ and a tail length $k\ge 0$. The rank is $n=a+4+k$ and the sites are $0,\dots,n-1$. By (3.2.1) a *cup* is a pair $c=\{l_c<r_c\}$ with $r_c\le a+2$ or $r_c=l_c+1$. Put $m=a+3$ and $d=a+1$. The cups are of two kinds (`eligible_core_or_tail`, `coreTailEquiv`):

* the $\binom m2$ *core cups*, which are all pairs inside the core sites $\{0,\dots,m-1\}$;
* the $k+1$ *tail cups* $\tau_t=\{a+2+t,\;a+3+t\}$ for $0\le t\le k$.

A core cup is *marked* if it contains the last core site $m-1=a+2$, that is, if it is $\{t,a+2\}$ with $0\le t\le a+1$.

**2.2 Through strands, active and inactive.** A one-cup diagram with cup $c$ has $n-2$ through strands, at the sites off $c$. We list them in increasing order $s_0(c)<\dots<s_{n-3}(c)$ (`throughOrder`) and call $i$ the *label* of $s_i(c)$. The Specht module $S^\lambda$, $\lambda\vdash a+2$, is attached to the first $a+2$ labels $0,\dots,a+1$, which we call the *active* labels. The remaining $k$ labels are *inactive*; they correspond to sites $\ge a+4$ and are fixed by every gluing permutation (`transport_fixes_inactive`, `activeTransport`). For a core cup $p$ the active through sites are the $a+1$ core sites off $p$ together with the site $a+3=m$, which lies outside the core. So the **last active** label $a+1$ always sits at site $m$. When $k>0$ this is not the last through label overall.

**2.3 Gluing.** Glue a source cup $c$ to a target cup $c'$, following (3.13).

* If $c=c'$, one closed loop forms (factor $x$) and the through permutation is the identity.
* If $c,c'$ are disjoint, two propagating lines are lost and the result is $0$ in the cell module.
* If $c=\{b,v\}$ and $c'=\{b,u\}$ share exactly the site $b$, then the line at the free site $s$ of $c$ leaves at the site $\tau_{uv}(s)$ of $c'$, where $\tau_{uv}$ is the transposition of $u$ and $v$ (`trace_shared`). We write $\pi_{c\to c'}$ for the induced permutation of labels: $\pi(i)$ is the label of $\tau_{uv}(s_i(c))$ in $c'$. It permutes the active labels among themselves (`activeTransport`).

**2.4 Fibre.** Let $\mathfrak S_{a+2}$ act on $\mathbb Q^{a+2}$ by permuting coordinates, and let $V_0$ be the sum-zero subspace. The ordinary hook $S^{(a+1,1)}$ is $V_0$ (`HookFiber`, `standard_eq_polytabloid_span`). The transposed hook $S^{(2,1^a)}\cong \mathrm{sgn}\otimes S^{(a+1,1)}$ is $V_0$ with $\sigma$ acting by $\operatorname{sgn}(\sigma)$ times the permutation (`TransposedFiber`, `transpose_span_eq`, `transImage_equivariant`). We use the basis $E_i=e_i-e_{a+1}$, $i\in\mathsf E:=\{0,\dots,a\}$, so $d=\dim S^\lambda=a+1$; coordinates $f\in\mathbb Q^{\mathsf E}$ stand for $\sum_i f_iE_i$ (`expand`, `standardCoords`). The invariant form is the restricted dot product, $\langle E_i,E_j\rangle=\delta_{ij}+1$. Every nonzero invariant bilinear form is a scalar multiple of it, and the sign twist does not change it (`invariant_hook_pairing`, `transpose_signs_cancel`).

**2.5 Gram matrix versus normalized operator.** Index the basis (3.2.2) by pairs $(c,i)$ with $c$ a cup and $i\in\mathsf E$. By (3.13) the Gram matrix is
$$\Gamma_{(c',i),(c,j)}=[c=c']\,x\,\langle E_i,E_j\rangle+[\,|c\cap c'|=1\,]\,\langle E_i,\ \pi_{c\to c'}\cdot E_j\rangle .$$
Let $A_{(c',i),(c,j)}$ be the $i$-th coordinate of $\pi_{c\to c'}\cdot E_j$ when $|c\cap c'|=1$, and $0$ otherwise (`nativeMove`, `interaction`). The entries of $A$ are integers. Then
$$\Gamma=M\,(xI+A),\qquad M=\operatorname{blockdiag}_c(I+J_{\mathsf E}),\qquad \det M=(a+2)^{\binom m2+k+1}$$
(`gram_eq_metric_char`, `nativeDet_eq`, `metric_det_ne`). The determinant value is elementary, since $\det(I+J_d)=d+1$; Lean proves only $\det M\neq0$. We call $xI+A$ the **normalized operator**; it is not the Gram matrix. Only $xI+A$ is used below. Its determinant is a characteristic polynomial, hence monic, of degree $d(\binom m2+k+1)$ (`nativeDet_degree`). The source's orthonormal-basis form $xI+\Gamma'$ in (3.2.3) has the same determinant up to a nonzero constant, which Theorem 3.19 allows. We write $D_n:=\det\Gamma$ (Lean `nativeDet a k b`, where `b` selects the transposed hook).

**2.6 Gauge.** Let $c$ be a cup at the seed rank $a+4$ (so $k=0$ and all through strands are active). Let $\theta(c)\in\{\pm1\}$ be the sign of the permutation of $\{0,\dots,a+3\}$ given by the word
$$\bigl(s_0(c),\dots,s_{a+1}(c),\ l_c,\ r_c\bigr),$$
that is, the through sites in increasing order followed by the two cup endpoints in increasing order. We take it relative to the same word for the first tail cup $\tau_0=\{a+2,a+3\}$, which is the identity word (`cupOrientation`, `coreOrientation`). Counting inversions gives $(n-2-l_c)+(n-1-r_c)$ with $n=a+4$, so
$$\theta(c)=(-1)^{\,l_c+r_c+1},\qquad \theta(\tau_0)=1 .$$
The **gauge** is $g(p)=1$ for the ordinary hook and $g(p)=\theta(p)$ for the transposed hook (`gauge`). On core indices we put $G=\operatorname{diag}(g(p))$, so $G^2=I$. The closed form is checked in §6 (N3.gauge_closed_form).

**2.7 Blocks.** Order the cups as core cups first, then $\tau_0,\dots,\tau_k$.

**Lemma 2.1 (block structure).** In this order,
$$xI+A=\begin{pmatrix}K&F&0&\cdots&0\\ F^{*}&xI_d&I_d&&\\0&I_d&xI_d&\ddots&\\ \vdots&&\ddots&\ddots&I_d\\0&&&I_d&xI_d\end{pmatrix},$$
where $K=xI+A_{\rm core}$ is the core block and $F$ (core rows, $\tau_0$ columns) and $F^*$ ($\tau_0$ rows, core columns) are supported on marked core cups. Moreover $K$, $F$ and $F^*$ do not depend on $k$.

*Proof.* The cups $\tau_t$ and $\tau_{t+1}$ share the site $b=a+3+t$, with $v=a+2+t$ and $u=a+4+t$. The strand at $u$ has label $a+2+t$ on $\tau_t$, and its new site $v$ has the same label on $\tau_{t+1}$. All other strands keep their sites, so $\pi$ is the identity (`activeTransport_adjacent`, `native_tail_block`). Non-adjacent tail cups are disjoint. A core cup and $\tau_t$ with $t\ge1$ are disjoint. A core cup meets $\tau_0$ exactly when it contains $a+2$ (`native_in_block`, `native_out_block`, `native_normal_blocks`). Every transport among cups inside $\{0,\dots,a+3\}$ fixes the sites $\ge a+4$, so it is the seed-rank transport extended by the identity (`coreMatrix_stable`, `boundaryIn_stable`, `boundaryOut_stable`). $\square$

We call $F^*$ the **reverse boundary block**. Its entries are the transports from core cups *to* $\tau_0$. Because the basis $E_i$ is not orthonormal, $F^*$ is in general **not** the transpose of $F$; the explicit formulas are in Lemma 5.11, and §6 records $F^*\ne F^{\mathsf T}$ (N3.Fstar_not_transpose).

---

## 3. The literal statement and the corrections

### 3.1 (a) Literal refutation

**Proposition 3.1.** The conjunction of the two ordinary clauses of Conjecture 3.31.1, (3.3.7) for $a\ge4$ and (3.3.9) for $a\ge2$, is false. In particular, at $a=5$, $k=0$ no nonzero constant $s$ satisfies $D_9=s\,C^{(6,1)}_{\rm printed}\,(P^{(6,1)}_{9})^{6}$.

*Proof.* At $a=5$, $k=0$ there are $\binom82+1=29$ cups and $d=6$, so $\deg D_9=174$ by §2.5 (`native_height_five_degree`). The printed exponents in (3.3.7) at $a=5$ are $64,14,20,15,21,1,1$, with sum $136$ (`printedC_five_degree`). In (3.3.9) at $k=0$ the leading term is $P^U_6$, of degree $5$, and all other terms have smaller degree, including the negative-index ones by (3.1.3). The polynomial is $x^5+14x^4+29x^3-126x^2-237x+210$ (`printedP_five_polynomial`). The printed product therefore has degree $136+6\cdot5=166\ne174$. A nonzero constant does not change the degree (`height_five_printed_negation`, `printed_ordinary_clauses_negation`). $\square$

The refutation uses only the two unambiguous ordinary clauses. It does not depend on how the missing operator in (3.3.10) is read.

### 3.2 (b) What is corrected

| Printed item | Status | Correction |
|---|---|---|
| (3.3.7), exponent of $x$ | wrong for $a\ne4$ | $x^{a(a+3)/2}\ \to\ x^{(a+3)(a+2)(a-2)/6}$. The two agree only at $a=4$ in the stated range; they first differ at $a=5$ (by $8$). At $a=3$ the corrected product is the source's separately displayed $C^{(4,1)}=(x-3)^{16}(x-2)^5x^{11}(x+2)^{10}(x+6)(x+8)$. All other factors are as printed. Lean: `ordinaryCCorrected`. |
| (3.3.7), range | extended | The corrected formula holds for all $a\ge2$, with coincident factors combined: at $a=3$, $x+a-3=x$. |
| (3.3.8) | correct as printed | Range $a\ge1$. Lean: `transposeCPrinted`. |
| (3.3.9) | correct as printed | Range $a\ge2$. Lean: `printedOrdinaryP`. |
| (3.3.10) | missing operator | The second line begins with **$+$**: $\dots+3a(a-1)P^U_{k+2}+2(a^2-2a-1)P^U_{k+1}+\dots$. Lean: `correctedTransposeP`. A minus sign is excluded by Lemma 5.15 (§6, S6.laurent.minus_rejected). |
| (3.1.1) | sign | The recurrence is $P_{n+1}=xP_n-P_{n-1}$ (§1.2). |

---

## 4. Main theorem

The statement is unchanged from the previous version. Write
$$Q_+=(x+a-1)(x-2)(x+2a)(x+a-3),\qquad R_+=(a+2)(x+a-2)\bigl(x^2+(2a-3)x-2a\bigr),$$
$$Q_-=(x+2)(x-a+1)(x-a-1),\qquad R_-=(a+2)(x+1)(x-a).$$

**Theorem.**

1. For every $a\ge 2$, `NativeNormalized a false (ordinaryCCorrected a) (printedOrdinaryP a)` holds. In particular, for every $k\ge 0$,
$$D_n=s\cdot C_+^{\rm corr}\cdot\bigl(Q_+P^U_{k+2}-R_+P^U_{k+1}\bigr)^{a+1},\qquad s\ne 0,$$
and $Q_+P^U_{k+2}-R_+P^U_{k+1}=P_+(k)$ is exactly the printed (3.3.9).
2. For every $a\ge 1$, `NativeNormalized a true (transposeCPrinted a) (correctedTransposeP a)` holds, with $D_n=s\,C_-\,(Q_-P^U_{k+2}-R_-P^U_{k+1})^{a+1}$, and the bracket is $P_-(k)$ with the plus sign.

Lean: `ordinary_normalized` and `transpose_normalized` in `ResidualFinal`.

`NativeNormalized a b C P` (module `LiteralNegation`) is the conjunction of the following:

* $C$ is monic;
* $P_{k+2}=xP_{k+1}-P_k$ for all $k\in\mathbb Z$;
* $P_k$ and $P_{k+1}$ are coprime for all $k\in\mathbb Z$;
* for $k\in\mathbb N$, $P_k$ is monic and $\deg P_{k+1}=\deg P_k+1$;
* for $k\in\mathbb N$ there is $s\ne0$ with $D_{a+4+k}=s\,C\,P_k^{a+1}$.

So "consecutive coprimality" ranges over all integer indices. The identity of $QP^U_{k+2}-RP^U_{k+1}$ with the printed coefficient lists also holds for all $k\in\mathbb Z$ (Lemma 5.15). The determinant statement is for $k\ge0$. In the proof, $s=\det M=(a+2)^{\binom m2+k+1}$.

**Remark 4.1 (the underlying matrix facts).** The proof below establishes, and Lean proves, the following.

* **(D)** $\det K=C\,Q^{d}$. The core products are `ordinaryCoreProduct a` for $a\ge2$ and `transposeCoreProduct a` for $a\ge1$ (`ordinary_core_det`, `transpose_core_det`, `ordinary_core_factor_algebra`, `transpose_core_factor_algebra`).
* **(R)** $F^*K^{-1}F=(R/Q)\,I_d$ over $\mathbb C(x)$ for both families at every $a\ge1$ in the written model. Lean's seed-rank declarations `ordinary_boundary` and `transpose_boundary` cover all natural $a$, including $a=0$.

---

## 5. Proof

Throughout, $\varepsilon=1$ for the ordinary hook and $\varepsilon=-1$ for the transposed hook, and $m=a+3$, $d=a+1$.

### 5.1 Reduction to the core

**Lemma 5.1 (Schur step).** Work over $\mathbb C(x)$. If $F^*K^{-1}F=h\,I_d$, then
$$\det(xI+A)=\det K\cdot\bigl(\det \mathcal P_{k+1}(x;\,x-h)\bigr)^{d},$$
where $\mathcal P_{n}(x;y)$ is the $n\times n$ matrix with diagonal $(y,x,\dots,x)$, ones on the first off-diagonals, and zeros elsewhere.

*Proof.* $\det K$ is monic of degree $d\binom m2$ (`coreMatrix_det_monic`), so $K$ is invertible over $\mathbb C(x)$. By Lemma 2.1 and the Schur complement formula, $\det(xI+A)=\det K\cdot\det(\mathcal T-\widehat F^*K^{-1}\widehat F)$. Here $\mathcal T$ is the tail block, and $\widehat F,\widehat F^*$ are $F,F^*$ padded by zero blocks for $\tau_1,\dots,\tau_k$. The matrix $\widehat F^*K^{-1}\widehat F$ vanishes outside the $(\tau_0,\tau_0)$ block, where it equals $hI_d$. So the Schur complement is the tail block with its first diagonal block replaced by $(x-h)I_d$. Reorder the tail indices fibre coordinate first; this is a permutation similarity. The Schur complement then becomes block diagonal, with $d$ equal blocks $\mathcal P_{k+1}(x;x-h)$ (`native_schur_path`, `subtract_marked_block`, `fiberPath_det`). $\square$

**Lemma 5.2 (tail continuant).** Over any commutative ring, $\det\mathcal P_{n}(x;x)=P^U_{n+1}$ and $\det\mathcal P_{n}(x;y)=y\,P^U_{n}-P^U_{n-1}$. In particular
$$\det\mathcal P_{k+1}(x;x-h)=P^U_{k+2}-h\,P^U_{k+1}.$$

*Proof.* Expand along the first row: $\det\mathcal P_n(x;y)=y\det\mathcal P_{n-1}(x;x)-\det\mathcal P_{n-2}(x;x)$, with $\det\mathcal P_0=1$ and $\det\mathcal P_{-1}:=0$. For $y=x$ this is the recurrence $P^U_{n+1}=xP^U_n-P^U_{n-1}$ with the initial values $P^U_1=1$, $P^U_2=x$. It is the **minus** recurrence, which is the sign fixed in §1.2. Substituting gives the second formula, and $y=x-h$ gives the third, since $xP^U_{k+1}-P^U_k=P^U_{k+2}$ (`scalarPath_nat_chebyshev`, `scalarPath_modified_det`). $\square$

**Proposition 5.3 (assembly).** Let $C,Q,R\in\mathbb C[x]$ with $Q\ne0$, and suppose (D) $\det K=C\,Q^d$ and (R) $F^*K^{-1}F=(R/Q)\,I_d$. Then for every $k\ge0$,
$$\det(xI+A)=C\,\bigl(QP^U_{k+2}-RP^U_{k+1}\bigr)^{d},\qquad D_{a+4+k}=(a+2)^{\binom m2+k+1}\,C\,\bigl(QP^U_{k+2}-RP^U_{k+1}\bigr)^{d}.$$

*Proof.* By Lemmas 5.1 and 5.2 with $h=R/Q$,
$$\det(xI+A)=CQ^d\,(P^U_{k+2}-(R/Q)P^U_{k+1})^d=C\,(QP^U_{k+2}-RP^U_{k+1})^d.$$
This is an identity in $\mathbb C(x)$ between polynomials, hence in $\mathbb C[x]$. Multiply by $\det M$ (§2.5). Lean: `native_det_of_core`. $\square$

So it remains to prove (D) and (R) and the normalization properties. We prove (D) and (R) for the **whole** core. §5.12 explains how the Lean endpoint reaches the same conclusion through a line/residual interface.

### 5.2 Site coordinates and incidence matrices

Let $\mathrm{Pt}=\{0,\dots,m-1\}$ be the core sites and $\mathrm{Pr}$ the core cups. Let $\mathrm{OP}=\{(s,z)\in\mathrm{Pt}^2:s\ne z\}$ be the ordered pairs, $\mathrm{Tri}$ the 3-subsets of $\mathrm{Pt}$, and
$$\mathrm{Conf}=\{(p,y):p\in\mathrm{Pr},\ y\in\mathrm{Pt}\setminus p\}$$
the *configurations*. Their sizes are $|\mathrm{Conf}|=\binom m2(m-2)=3|\mathrm{Tri}|$, $|\mathrm{Tri}|=\binom m3$, $|\mathrm{OP}|=m(m-1)$, $|\mathrm{Pr}|=\binom m2$ and $|\mathrm{Pt}|=m$ (`card_sconf`, `card_tri`, `card_opair`, `card_core`).

**Slot sites.** For a core cup $p$ and $i\in\mathsf E$ put $\sigma(p,i)=s_i(p)$ (`slotSite`). By §2.2 the labels $0,\dots,a$ of $p$ sit exactly at the $a+1$ core sites off $p$, in increasing order, and the last active label $a+1$ sits at site $m$. Hence $(p,i)\mapsto(p,\sigma(p,i))$ is a bijection from core indices to $\mathrm{Conf}$ (`toConf_bijective`, `confEquiv`). From now on we index the core by $\mathrm{Conf}$.

**Incidence matrices.** For a cup $c=\{l_c<r_c\}$ and a site $z$, let $N(c,z)=\varepsilon$ if $z=l_c$, $N(c,z)=1$ if $z=r_c$, and $0$ otherwise (`wInc`). For $(p,y)\in\mathrm{Conf}$ let $f(p,y)=-1$ if $\varepsilon=-1$ and $l_p<y<r_p$, and $f(p,y)=1$ otherwise (`fSign`). Define:

| matrix | rows × columns | entry | Lean |
|---|---|---|---|
| $B$ | Conf × OP | $B_{(p,y),(s,z)}=[y=s]\,N(p,z)$ | `incB` |
| $T$ | Conf × Tri | $T_{(p,y),t}=[p\cup\{y\}=t]\,f(p,y)$ | `incT` |
| $\Lambda$ | Conf × Pr | $\Lambda_{(p,y),q}=[p=q]$ | `incL`, `LamCI` |
| $K_2=\Lambda^{\mathsf T}T$ | Pr × Tri | $K_2(q,t)=[q\subset t]\,f(q,t\setminus q)$ | `incK` |
| $H$ | OP × Pt | $H_{(s,z),y}=[s=y]$ | `incH` |
| $D$ | OP × Pr | $D_{(s,z),q}=[(s,z)=(l_q,r_q)]+\varepsilon[(s,z)=(r_q,l_q)]$ | `incD` |
| $N$ | Pr × Pt | $N(q,z)$ as above | `wInc` |
| $J$ | Pt × Pt | all ones | `Chain.J` |

We use two consequences of these definitions. First, $D_{(s,z),\{s,z\}}=N(\{s,z\},z)$. Second, $N(c,z)^2=1$ for $z\in c$.

### 5.3 Two sign lemmas

**Lemma 5.4 (triangle sign).** Let $b,u,v$ be distinct sites, $p=\{b,v\}$ and $q=\{b,u\}$. Then
$$f(p,u)\,f(q,v)=\varepsilon\,N(p,b)\,N(q,b).$$

*Proof.* For $\varepsilon=1$ both sides are $1$. For $\varepsilon=-1$, go through the six orders of $b,u,v$. Note that $f(p,u)=-1$ iff $u$ lies strictly between $b$ and $v$, and $N(p,b)=-1$ iff $b<v$.

| order | $f(p,u)$ | $f(q,v)$ | LHS | $N(p,b)$ | $N(q,b)$ | $-N(p,b)N(q,b)$ |
|---|---|---|---|---|---|---|
| $b<u<v$ | $-1$ | $1$ | $-1$ | $-1$ | $-1$ | $-1$ |
| $b<v<u$ | $1$ | $-1$ | $-1$ | $-1$ | $-1$ | $-1$ |
| $u<b<v$ | $1$ | $1$ | $1$ | $-1$ | $1$ | $1$ |
| $v<b<u$ | $1$ | $1$ | $1$ | $1$ | $-1$ | $1$ |
| $u<v<b$ | $1$ | $-1$ | $-1$ | $1$ | $1$ | $-1$ |
| $v<u<b$ | $-1$ | $1$ | $-1$ | $1$ | $1$ | $-1$ |

Lean: `sign_triangle`. $\square$

**Lemma 5.5 (gauge sign).** Let $c=\{b,v\}$ and $c'=\{b,u\}$ be cups at the seed rank $a+4$ sharing exactly $b$, and let $\pi=\pi_{c\to c'}$. Then
$$\theta(c')\,\operatorname{sgn}(\pi)\,\theta(c)=-\,\operatorname{sgn}(\pi_{\rm end}),$$
where $\pi_{\rm end}\in\mathfrak S_2$ is the identity if $b$ is the same endpoint (left or right) of $c$ and $c'$, and the swap otherwise. Consequently, for the transposed hook,
$$\theta(c')\,\operatorname{sgn}(\pi)\,\theta(c)=\varepsilon\,N(c,b)\,N(c',b).$$
For the ordinary hook the factor $\operatorname{sgn}(\pi)$ does not occur and $\varepsilon N(c,b)N(c',b)=1$.

*Proof.* Let $w_c,w_{c'}$ be the words of §2.6, viewed as bijections from positions $\{0,\dots,a+3\}$ to sites. Consider $\Pi=w_{c'}^{-1}\circ\tau_{uv}\circ w_c$. On the through positions $0,\dots,a+1$ it is $\pi$, by the definition of $\pi$. It maps the two endpoint positions of $c$, which hold $b$ and $v$, to the endpoint positions of $c'$, which hold $b=\tau_{uv}(b)$ and $u=\tau_{uv}(v)$; on these positions it acts as $\pi_{\rm end}$. Hence $\operatorname{sgn}\pi\cdot\operatorname{sgn}\pi_{\rm end}=\operatorname{sgn}\Pi=\theta(c')\cdot(-1)\cdot\theta(c)$, which is the first identity. For $\varepsilon=-1$ we have $N(c,b)N(c',b)=1$ if $b$ has the same position in both cups and $-1$ otherwise, that is, $N(c,b)N(c',b)=\operatorname{sgn}\pi_{\rm end}$. So $-\operatorname{sgn}\pi_{\rm end}=\varepsilon N(c,b)N(c',b)$. Lean: `transport_label_decomposition`, `through_sign_orientation`, `sign_endpointPerm`, `gauge_sign`. $\square$

### 5.4 The bridge

**Proposition 5.6 (bridge).** For core indices $(q,i)$ and $(p,j)$ with $y'=\sigma(q,i)$ and $y=\sigma(p,j)$,
$$g(q)\,A_{(q,i),(p,j)}\,g(p)=\bigl(\varepsilon BB^{\mathsf T}+TT^{\mathsf T}-(1+2\varepsilon)I\bigr)_{(q,y'),(p,y)}.$$
Consequently, in $\mathrm{Conf}$ coordinates,
$$K=G\,\mathcal K\,G,\qquad \mathcal K:=Y I+\varepsilon BB^{\mathsf T}+TT^{\mathsf T},\qquad Y:=x-1-2\varepsilon .$$

*Proof.* From the definitions,
$$(BB^{\mathsf T})_{(q,y'),(p,y)}=[y=y']\,(NN^{\mathsf T})_{qp},\qquad (TT^{\mathsf T})_{(q,y'),(p,y)}=[\,q\cup\{y'\}=p\cup\{y\}\,]\,f(q,y')f(p,y)$$
(`BBt_entry`, `PT_entry`). Two core cups are equal, disjoint, or share exactly one site (`pair_cases`).

*Equal cups, $p=q$.* The native entry is $0$; the loop contributes only to the $x$ on the diagonal. On the right, $(NN^{\mathsf T})_{pp}=\varepsilon^2+1=2$, and $p\cup\{y'\}=p\cup\{y\}$ iff $y=y'$, so the right side is $[y=y'](2\varepsilon+1-(1+2\varepsilon))=0$.

*Disjoint cups.* The native entry is $0$. On the right, $(NN^{\mathsf T})_{qp}=0$, and $q\cup\{y'\}=p\cup\{y\}$ would force $|p\cap q|\ge1$.

*Shared site, $p=\{b,v\}$ and $q=\{b,u\}$.* Let $\pi=\pi_{p\to q}$. Neither $u$ nor $v$ is the site $m$, so $\pi$ fixes the last active label $a+1$ (`shared_core_fixes_last`). Hence
$$\pi\cdot E_j=\operatorname{sgn}(\pi)^{[\varepsilon=-1]}\,(e_{\pi(j)}-e_{a+1}),$$
whose $i$-th coordinate is $\operatorname{sgn}(\pi)^{[\varepsilon=-1]}[\pi(j)=i]$ (`hookAct_delta_fix`). By §2.3, $\pi(j)=i$ iff $y'=\tau_{uv}(y)$ (`transport_slot`). By Lemma 5.5 the gauged native entry is therefore
$$\varepsilon N(p,b)N(q,b)\,[\,y'=\tau_{uv}(y)\,].$$
Since $y\notin p$ and $y'\notin q$, there are two cases. If $y=u$ then $\tau_{uv}(y)=v$; otherwise $\tau_{uv}(y)=y$. And $y=y'=u$ is impossible. So
$$[\,y'=\tau_{uv}(y)\,]=[y=y']+[y=u][y'=v].$$
On the right side we have $(NN^{\mathsf T})_{qp}=N(q,b)N(p,b)$, and $q\cup\{y'\}=p\cup\{y\}$ iff $y=u$ and $y'=v$. So the right side equals
$$\varepsilon N(q,b)N(p,b)[y=y']+[y=u][y'=v]\,f(q,v)f(p,u).$$
The two expressions agree by Lemma 5.4.

The identity matrix term contributes only when $(q,y')=(p,y)$, and is included above. Adding $x I$ on both sides gives $GKG=\mathcal K$, and $G^2=I$. Lean: `bridge_entry`, `core_site_form`, `core_form_CI`. $\square$

Since $\det G=\pm1$, we have $\det K=\det\mathcal K$ (`core_det_form`). Also, $\mathcal K$ is symmetric (`core_symm`).

### 5.5 Incidence identities

**Lemma 5.7.** With $\varepsilon^2=1$ and $\kappa:=m-1-\varepsilon$:
$$\begin{aligned}
&(\mathrm{I1})\ B^{\mathsf T}B=(m-2-\varepsilon)I+\varepsilon HH^{\mathsf T}, &&(\mathrm{I2})\ T^{\mathsf T}T=3I, &&(\mathrm{I3})\ T^{\mathsf T}B=\varepsilon K_2^{\mathsf T}D^{\mathsf T},\\
&(\mathrm{I4})\ K_2K_2^{\mathsf T}=(m-2-2\varepsilon)I+\varepsilon NN^{\mathsf T}, &&(\mathrm{I5})\ H^{\mathsf T}H=(m-1)I, &&(\mathrm{I6})\ D^{\mathsf T}H=\varepsilon N,\\
&(\mathrm{I7})\ D^{\mathsf T}D=2I, &&(\mathrm{I8})\ N^{\mathsf T}N=\kappa I+\varepsilon J .
\end{aligned}$$

*Proof.* Each identity is an entrywise count.

* (I1) $(B^{\mathsf T}B)_{(s,z),(s',z')}=[s=s']\sum_{p\not\ni s}N(p,z)N(p,z')$.
  * If $z=z'$, the sum counts the cups through $z$ that avoid $s$; there are $m-2$.
  * If $s=s'$ and $z\ne z'$, only $p=\{z,z'\}$ contributes, with value $N(p,z)N(p,z')=\varepsilon$.
  * The right side has diagonal $m-2-\varepsilon+\varepsilon$, value $\varepsilon$ when $s=s'$ and $z\ne z'$, and $0$ when $s\ne s'$.
* (I2) Each triple $t$ arises from exactly three configurations, each with $f^2=1$.
* (I3) The entry $(T^{\mathsf T}B)_{t,(s,z)}$ vanishes unless $s,z\in t$. In that case the only configuration is $(p,s)$ with $p=t\setminus\{s\}=\{z,c\}$, where $c$ is the third site, and the entry is $f(p,s)N(p,z)$. On the right side only $q=\{s,z\}$ contributes, giving $\varepsilon f(q,c)D_{(s,z),q}=\varepsilon f(q,c)N(q,z)$. By Lemma 5.4 with shared site $z$, we have $f(p,s)f(q,c)=\varepsilon N(p,z)N(q,z)$, hence $f(p,s)N(p,z)=\varepsilon f(q,c)N(q,z)$, using $N(p,z)^2=1$.
* (I4) The diagonal is $m-2$: there are $m-2$ choices of third site, each with $f^2=1$. For $q=\{b,u\}$ and $q'=\{b,v\}$, the only common triple is $\{b,u,v\}$, which contributes $f(q,v)f(q',u)=\varepsilon N(q,b)N(q',b)$ by Lemma 5.4. Disjoint cups give $0$.
* (I5) Each site is the first entry of $m-1$ ordered pairs.
* (I6) $(D^{\mathsf T}H)_{q,y}$ is $D_{(y,\cdot),q}$ for the unique ordered pair on $q$ starting at $y$. This is $1=\varepsilon N(q,l_q)$ if $y=l_q$ and $\varepsilon=\varepsilon N(q,r_q)$ if $y=r_q$.
* (I7) Each cup has two ordered lifts, with coefficients $1$ and $\varepsilon$, and $1+\varepsilon^2=2$.
* (I8) There are $m-1$ cups through a site, and exactly one cup through two distinct sites $y\ne y'$, contributing $N(p,y)N(p,y')=\varepsilon$.

Lean: `gram_B`, `gram_T`, `incT_B`, `gram_K`, `gram_H`, `incD_H`, `gram_D`, `gram_N`, collected in `site_identities`. $\square$

### 5.6 Determinant reduction

Let $\varepsilon^2=1$ and $m\in F$ for a field $F$ of characteristic $0$; $\kappa=m-1-\varepsilon$ as above. Put
$$\alpha=Y+\varepsilon(m-2)-1,\quad \beta=\frac{\varepsilon(m-2-2\varepsilon)}{Y+3},\quad\gamma=\frac1{Y+3},\quad\delta=\frac{\beta}{\alpha-2\beta},$$
and
$$\begin{aligned}
x_1&=\alpha+m-1+\delta\kappa, & y_1&=\delta\varepsilon, & x_2&=\varepsilon(1+2\delta)\kappa, & y_2&=1+2\delta,\\
x_3&=-\gamma\varepsilon(1+2\delta)\kappa, & y_3&=-\gamma(1+2\delta), & x_4&=\alpha-2\gamma(1+2\delta)\kappa, & y_4&=-2\gamma\varepsilon(1+2\delta),
\end{aligned}$$
$$s_0=x_1x_4-x_2x_3,\qquad s_1=(x_1+my_1)(x_4+my_4)-(x_2+my_2)(x_3+my_3)$$
(`Chain.alpha`, …, `Chain.sOne`).

**Lemma 5.8 (blocks in $\operatorname{span}\{I,J\}$).** Let $|\mathrm{Pt}|=m\ge1$ with $m\ne0$ in $F$. Then
$$\det\begin{pmatrix}x_1I+y_1J&x_2I+y_2J\\x_3I+y_3J&x_4I+y_4J\end{pmatrix}=s_0^{\,m-1}s_1 .$$

*Proof.* Split $F^{\mathrm{Pt}}=F\mathbf 1\oplus V_0$, where $V_0$ is the sum-zero subspace; $J$ acts as $m$ on $\mathbf 1$ and as $0$ on $V_0$. The block matrix preserves $(F\mathbf 1)^2$ and $V_0^2$. On $V_0^2\cong V_0\otimes F^2$ it acts as $\mathrm{id}\otimes\begin{pmatrix}x_1&x_2\\x_3&x_4\end{pmatrix}$, with determinant $s_0^{m-1}$. On $(F\mathbf 1)^2$ it acts as $\begin{pmatrix}x_1+my_1&x_2+my_2\\x_3+my_3&x_4+my_4\end{pmatrix}$, with determinant $s_1$. $\square$

The Lean proof (`det_IJ`, `det_blocks_IJ`) instead uses a Schur complement and assumes $x_1\ne0$, $x_1+my_1\ne0$ and $s_0\ne0$. All three hold in our application (§5.10).

**Proposition 5.9 (determinant reduction; `chain_det`).** Assume (I1)–(I8), $|\mathrm{Pt}|=m$, and $Y\ne0$, $Y+3\ne0$, $\alpha\ne0$, $\alpha-2\beta\ne0$. Then
$$\det\mathcal K\cdot Y^{|\mathrm{Tri}|+|\mathrm{OP}|}\,\alpha^{|\mathrm{Pr}|+2m}=(Y+3)^{|\mathrm{Tri}|}\,Y^{|\mathrm{Conf}|}\,(\alpha-2\beta)^{|\mathrm{Pr}|}\,\alpha^{|\mathrm{OP}|}\,s_0^{m-1}s_1 .$$
The Lean statement also assumes $x_1\ne0$, $x_1+my_1\ne0$ and $s_0\ne0$ (structure `Chain.Generic`).

*Proof.*

1. *Triple level.* Write $\mathcal T=YI+TT^{\mathsf T}$. By Sylvester's identity and (I2),
$$\det\mathcal T\cdot Y^{|\mathrm{Tri}|}=\det(YI+T^{\mathsf T}T)\,Y^{|\mathrm{Conf}|}=(Y+3)^{|\mathrm{Tri}|}Y^{|\mathrm{Conf}|}.$$
Since $(TT^{\mathsf T})^2=3TT^{\mathsf T}$, we have $\mathcal T\cdot Y^{-1}(I-\gamma TT^{\mathsf T})=I$ (`tri_det`, `tri_inv_eq`).
2. *Ordered pairs.* $\mathcal K=\mathcal T+B(\varepsilon B^{\mathsf T})$, so by the matrix determinant lemma $\det\mathcal K=\det\mathcal T\det(I+\varepsilon B^{\mathsf T}\mathcal T^{-1}B)$. Moreover
$$Y(I+\varepsilon B^{\mathsf T}\mathcal T^{-1}B)=YI+\varepsilon B^{\mathsf T}B-\varepsilon\gamma\,B^{\mathsf T}TT^{\mathsf T}B=:Z.$$
By (I1), $\varepsilon B^{\mathsf T}B=\varepsilon(m-2-\varepsilon)I+HH^{\mathsf T}$. By (I3) and (I4),
$$B^{\mathsf T}TT^{\mathsf T}B=DK_2K_2^{\mathsf T}D^{\mathsf T}=(m-2-2\varepsilon)DD^{\mathsf T}+\varepsilon(DN)(DN)^{\mathsf T}.$$
Hence
$$Z=\alpha I+HH^{\mathsf T}-\beta DD^{\mathsf T}-\gamma(DN)(DN)^{\mathsf T},\qquad \det\mathcal K=\det\mathcal T\cdot Y^{-|\mathrm{OP}|}\det Z$$
(`schur_pairs_raw`, `schur_pairs`, `pairs_form`).
3. *Cups.* Write $Z=Z_1+\Phi\Psi$ with $Z_1=\alpha I-\beta DD^{\mathsf T}$, $\Phi=[\,H\mid DN\,]$ (OP × (Pt ⊔ Pt)) and $\Psi=\begin{bmatrix}H^{\mathsf T}\\-\gamma(DN)^{\mathsf T}\end{bmatrix}$. By Sylvester and (I7), $\det Z_1\cdot\alpha^{|\mathrm{Pr}|}=(\alpha-2\beta)^{|\mathrm{Pr}|}\alpha^{|\mathrm{OP}|}$, and $Z_1^{-1}=\alpha^{-1}(I+\delta DD^{\mathsf T})$ because $\alpha\delta-\beta-2\beta\delta=0$. Then $\det Z=\det Z_1\det(I+\Psi Z_1^{-1}\Phi)$ (`zone_det`, `zone_inv_right`, `zform_split`).
4. *Sites.* By (I6), $Z_1^{-1}H=\alpha^{-1}(H+\delta\varepsilon DN)$; by (I7), $Z_1^{-1}DN=\alpha^{-1}(1+2\delta)DN$. Using $H^{\mathsf T}D=\varepsilon N^{\mathsf T}$ (transpose of (I6)), (I5), (I7) and (I8), the four blocks of $\alpha(I+\Psi Z_1^{-1}\Phi)$ are:
   * top left: $\alpha I+(m-1)I+\delta\varepsilon\cdot\varepsilon N^{\mathsf T}N=x_1I+y_1J$;
   * top right: $(1+2\delta)\varepsilon N^{\mathsf T}N=x_2I+y_2J$;
   * bottom left: $-\gamma\bigl(\varepsilon N^{\mathsf T}N+2\delta\varepsilon N^{\mathsf T}N\bigr)=x_3I+y_3J$;
   * bottom right: $\alpha I-2\gamma(1+2\delta)N^{\mathsf T}N=x_4I+y_4J$.

   By Lemma 5.8, $\det(I+\Psi Z_1^{-1}\Phi)=\alpha^{-2m}s_0^{m-1}s_1$ (`block_form`).

Multiplying steps 1–4 gives the claim. $\square$

### 5.7 Compression

**Proposition 5.10 (compression; `chain_compress`).** Work over a field $F$. Assume:

* (I1)–(I8) hold, with $\varepsilon^2=1$;
* $Y+3\ne0$ and $\alpha\ne0$;
* $\mathcal K=YI+\varepsilon BB^{\mathsf T}+TT^{\mathsf T}$ is invertible.

Let $\mathsf E$ be a finite index set. Let $W,\Omega\in F^{\mathrm{OP}\times\mathsf E}$, $U\in F^{\mathrm{Pt}\times\mathsf E}$ and $V\in F^{\mathrm{Pr}\times\mathsf E}$ be rectangular matrices with common column set $\mathsf E$ satisfying
$$\begin{aligned}
&(\mathrm{T1})\ H^{\mathsf T}W=U, &&(\mathrm{T2})\ D^{\mathsf T}W=V, &&(\mathrm{T3})\ N^{\mathsf T}V=\varepsilon U, &&(\mathrm{T4})\ JU=0,\\
&(\mathrm{T5})\ \Omega^{\mathsf T}W=I_{\mathsf E}, &&(\mathrm{T6})\ (H^{\mathsf T}\Omega)^{\mathsf T}U=I_{\mathsf E}, &&(\mathrm{T7})\ (N^{\mathsf T}D^{\mathsf T}\Omega)^{\mathsf T}U=\varepsilon I_{\mathsf E}, &&(\mathrm{T8})\ (D^{\mathsf T}\Omega)^{\mathsf T}V=I_{\mathsf E}.
\end{aligned}$$
Let $d_1,e_2,c_1\in F$ satisfy
$$\begin{aligned}
&(\mathrm{S1})\ (\alpha+m-1)d_1+\varepsilon\kappa e_2+c_1=1,\qquad (\mathrm{S2})\ c_1(\alpha-2\beta)=-\beta,\\
&(\mathrm{S3})\ (\alpha-2\beta-2\gamma\kappa)e_2-(\beta+\gamma\kappa)\varepsilon d_1-2\gamma\varepsilon c_1=-\gamma\varepsilon .
\end{aligned}$$
Then, as $\mathsf E\times\mathsf E$ matrices,
$$(B\Omega)^{\mathsf T}\mathcal K^{-1}(BW)=\varepsilon\Bigl(1-\frac Y\alpha\bigl(1-d_1-\varepsilon e_2-c_1\bigr)\Bigr)\,I_{\mathsf E}.$$
Neither $Y\ne0$ nor $\alpha-2\beta\ne0$ is needed.

*Proof.* Define
$$Z:=YI+\varepsilon B^{\mathsf T}B-\varepsilon\gamma B^{\mathsf T}TT^{\mathsf T}B
   =\alpha I+HH^{\mathsf T}-\beta DD^{\mathsf T}-\gamma(DN)(DN)^{\mathsf T}.$$
The equality follows from (I1), (I3), (I4) and $\varepsilon^2=1$, as in the ordered-pair calculation of Proposition 5.9. The only denominator in this definition is $Y+3$. All test matrices and the resulting solution matrices have columns indexed by $\mathsf E$.

*Step 1: an explicit solution of $Zy=W$.* Put $\mathcal V=d_1HU+e_2DNU+c_1DV$ and $y=\alpha^{-1}(W-\mathcal V)$, both in $F^{\mathrm{OP}\times\mathsf E}$. By (I5)–(I8), (T1)–(T4) and $N^{\mathsf T}NU=\kappa U$ (from (I8) and (T4)),
$$\begin{aligned}
ZW&=\alpha W+HU-\beta DV-\gamma\varepsilon DNU,\\
Z(HU)&=(\alpha+m-1)HU-\varepsilon(\beta+\gamma\kappa)DNU,\\
Z(DNU)&=\varepsilon\kappa HU+(\alpha-2\beta-2\gamma\kappa)DNU,\\
Z(DV)&=HU+(\alpha-2\beta)DV-2\gamma\varepsilon DNU.
\end{aligned}$$
Hence $Z(W-\mathcal V)-\alpha W$ is a linear combination of $HU$, $DV$ and $DNU$ with coefficients equal to the right side minus the left side of (S1), (S2) and (S3), respectively. So $Zy=W$ (`zform_solution`).

*Step 2: back to configurations.* Put $X=By-\gamma\,T(T^{\mathsf T}By)\in F^{\mathrm{Conf}\times\mathsf E}$. Since $(TT^{\mathsf T})^2=3TT^{\mathsf T}$, we get $(YI+TT^{\mathsf T})X=Y\,By$. Hence
$$\mathcal KX=B\bigl(Yy+\varepsilon B^{\mathsf T}By-\varepsilon\gamma B^{\mathsf T}TT^{\mathsf T}By\bigr)=BZy=BW .$$
As $\mathcal K$ is invertible, $\mathcal K^{-1}BW=X$. Similarly $B^{\mathsf T}X=\varepsilon(Zy-Yy)=\varepsilon(W-Yy)$.

*Step 3: the compression.* We have $(B\Omega)^{\mathsf T}\mathcal K^{-1}BW=\Omega^{\mathsf T}B^{\mathsf T}X=\varepsilon(\Omega^{\mathsf T}W-Y\Omega^{\mathsf T}y)$. By (T5), $\Omega^{\mathsf T}W=I_{\mathsf E}$. By (T6)–(T8), $\Omega^{\mathsf T}HU=I_{\mathsf E}$, $\Omega^{\mathsf T}DNU=\varepsilon I_{\mathsf E}$ and $\Omega^{\mathsf T}DV=I_{\mathsf E}$. Hence $\Omega^{\mathsf T}y=\alpha^{-1}(1-d_1-\varepsilon e_2-c_1)I_{\mathsf E}$. $\square$

### 5.8 The boundary blocks in site coordinates

Let $\mathsf E=\{0,\dots,a\}$ index the fibre of $\tau_0$. Define $W,\Omega\in\mathbb Z^{\mathrm{OP}\times\mathsf E}$, $U\in\mathbb Z^{\mathrm{Pt}\times\mathsf E}$, $V,S\in\mathbb Z^{\mathrm{Pr}\times\mathsf E}$ column by column:
$$W e_j=e_{(j,a+2)}-e_{(a+1,a+2)},\quad \Omega e_i=e_{(i,a+2)},\quad Ue_j=e_j-e_{a+1},\quad Ve_j=e_{\{j,a+2\}}-e_{\{a+1,a+2\}},\quad Se_i=e_{\{i,a+2\}}$$
(`wV`, `OmV`, `UV`, `RV`, `SelV`).

**Lemma 5.11 (boundary blocks).** For a marked cup $p=\{t,a+2\}$ and $i,j\in\mathsf E$,
$$F_{(p,i),j}=g(p)\bigl([\sigma(p,i)=j]-[\sigma(p,i)=a+1]\bigr),\qquad F^*_{i,(p,j)}=g(p)\bigl([\sigma(p,j)=i]-[t=i]\bigr),$$
and both blocks vanish on unmarked cups. In $\mathrm{Conf}$ coordinates this reads
$$GF=BW,\qquad F^*G=(B\Omega)^{\mathsf T}-(\Lambda S)^{\mathsf T}.$$
The test data (T1)–(T8) hold with $\varepsilon=\pm1$.

*Proof.* We first compute $F$. The source cup is $\tau_0=\{b,v\}$ with $b=a+2$ and $v=a+3$; the target is $p=\{b,u\}$ with $u=t$. On $\tau_0$ the label of site $s\le a+1$ is $s$. On $p$ the labels $0,\dots,a$ sit at $\{0,\dots,a+1\}\setminus\{t\}$, and label $a+1$ sits at $a+3$. The transposition $\tau_{t,a+3}$ fixes every site in $\{0,\dots,a+1\}\setminus\{t\}$. So $\pi(j)=i$ iff $\sigma(p,i)=j$ (for $j\ne t$; for $j=t$ both sides fail), and $\pi(a+1)=i$ iff $\sigma(p,i)=a+1$. The $i$-th coordinate of $\pi\cdot E_j$ is therefore
$$\operatorname{sgn}(\pi)^{[\varepsilon=-1]}\bigl([\sigma(p,i)=j]-[\sigma(p,i)=a+1]\bigr)$$
(`bIn_marked`). For the transposed hook, Lemma 5.5 with $\theta(\tau_0)=1$, $N(\tau_0,a+2)=\varepsilon$ and $N(p,a+2)=1$ gives $\operatorname{sgn}\pi=\theta(p)$ (`marked_orientation_sign`, `transposed_marked_input_action`).

For $F^*$ the source is $p$ and the target is $\tau_0$, with $u=a+3$ and $v=t$. Then $\pi(j)=\sigma(p,j)$ for $j\le a$ and $\pi(a+1)=t$, which gives the formula (`marked_to_first_tail`, `bOut_marked`, `transposed_marked_output_action`). Unmarked cups are disjoint from $\tau_0$.

Next, $(BW)_{(p,y),j}=N(p,a+2)([y=j]-[y=a+1])$ and $N(p,a+2)=[p\text{ marked}]$. With $y=\sigma(p,i)$ and $g(p)^2=1$ this is $GF=BW$. Similarly $(B\Omega)_{(p,y),i}=[p\text{ marked}][y=i]$ and $(\Lambda S)_{(p,y),i}=[p=\{i,a+2\}]$, and $p=\{t,a+2\}=\{i,a+2\}$ iff $t=i$ (`gauge_in`, `gauge_out`).

Finally the test data. (T1)–(T4) and (T5) are immediate, since $j,a+1<a+2$ and $i\le a$. For (T6), $((H^{\mathsf T}\Omega)^{\mathsf T}U)_{ij}=U_{ij}=[i=j]$. For (T7), $(N^{\mathsf T}D^{\mathsf T}\Omega)_{z,i}=N(\{i,a+2\},z)=\varepsilon[z=i]+[z=a+2]$, and $U_{a+2,j}=0$. For (T8), $V_{\{i,a+2\},j}=[i=j]$. Lean: `test_data`. $\square$

### 5.9 The constant line and the signed line response

Define the **line operator** on cups,
$$\mathcal D=(x-2\varepsilon)I+\varepsilon NN^{\mathsf T},$$
and the **line input**
$$\mathrm{lineInput}:=\tfrac1d\,\Lambda^{\mathsf T}BW\ \in\ \mathbb Q^{\mathrm{Pr}\times\mathsf E}.$$
In Lean, `lineInput a` is $\frac1{a+1}\sum_i F^{\rm ord}_{(p,i),j}$. It equals $\frac1d\Lambda^{\mathsf T}GF$ for both hooks (`boundary_in_line`), hence equals $\frac1d\Lambda^{\mathsf T}BW$ by Lemma 5.11. Put
$$E_0:=S-s_*\mathbf 1^{\mathsf T},\qquad s_*:=e_{\{a+1,a+2\}},\qquad \lambda:=x-2\varepsilon+\varepsilon\kappa,\qquad \rho:=\frac1{x-2\varepsilon}\Bigl(1-\frac{\varepsilon}{\lambda}\Bigr).$$

**Lemma 5.12 (line).**

1. $\mathcal K\Lambda=\Lambda\mathcal D$, and $\mathcal D$ is symmetric and invertible over $\mathbb Q(x)$.
2. $\Lambda^{\mathsf T}BW=-E_0$, so $\mathrm{lineInput}=-E_0/d$.
3. $S^{\mathsf T}\mathcal D^{-1}E_0=\rho\,I_{\mathsf E}$.

For the ordinary hook $\lambda=x+a-1$ and $\rho=\dfrac{x+a-2}{(x-2)(x+a-1)}$. For the transposed hook $\lambda=x-a-1$ and $\rho=\dfrac{x-a}{(x+2)(x-a-1)}$.

*Proof.* (1) We have $(\mathcal K\Lambda)_{(q,y'),p}=\sum_{y\notin p}\mathcal K_{(q,y'),(p,y)}$. Using the two formulas of the proof of Proposition 5.6:

* If $p=q$, the sum is $Y+2\varepsilon+1=x=\mathcal D_{pp}$.
* If $p$ and $q$ are disjoint, the sum is $0$.
* If $q=\{b,u\}$ and $p=\{b,v\}$, the sum is $\varepsilon[y'\ne v]N(q,b)N(p,b)+[y'=v]f(q,v)f(p,u)$. By Lemma 5.4 this is $\varepsilon N(q,b)N(p,b)=\mathcal D_{qp}$.

$\mathcal D$ is symmetric, and $\det\mathcal D$ is monic in $x$. The inherited `coreMatrix_line_frac` gives the intertwining relation in native coordinates, where $\Lambda$ becomes $G\Lambda$ (`lineJ_eq`). The symmetry declarations `core_symm` and `line_symm` are in `Compress1`. In Lean, $\mathcal D$ is `linePolynomial`: `lineChar` $=xI+$`lineAdj` for $\varepsilon=1$ and `transLineChar` for $\varepsilon=-1$. Its determinant is computed in `ordinary_line_charpoly` and `transposed_line_charpoly`.

(2) For $q=\{t,a+2\}$ we get $\sum_{y\notin q}([y=j]-[y=a+1])=[t\ne j]-[t\ne a+1]=[t=a+1]-[t=j]$. Unmarked cups give $0$.

(3) For each $j$, $N^{\mathsf T}E_0e_j=N(\{j,a+2\},\cdot)-N(\{a+1,a+2\},\cdot)=\varepsilon Ue_j$. Then
$$\mathcal D E_0e_j=(x-2\varepsilon)E_0e_j+NUe_j,\qquad \mathcal D NUe_j=(x-2\varepsilon)NUe_j+\varepsilon N(\kappa I+\varepsilon J)Ue_j=\lambda\,NUe_j,$$
using (I8) and (T4). Hence $\mathcal D^{-1}E_0e_j=\frac1{x-2\varepsilon}\bigl(E_0e_j-\frac1\lambda NUe_j\bigr)$. Finally $S^{\mathsf T}E_0e_j=e_j$ and $(S^{\mathsf T}NUe_j)_i=N(\{i,a+2\},j)-N(\{i,a+2\},a+1)=\varepsilon[i=j]$. $\square$

**Proposition 5.13 (compression split, with signs).** Over $\mathbb Q(x)$,
$$F^*K^{-1}F=\underbrace{(B\Omega)^{\mathsf T}\mathcal K^{-1}(BW)}_{\text{incidence term }=\ \iota I}\;-\;\underbrace{S^{\mathsf T}\bigl(d\,\mathcal D^{-1}\,\mathrm{lineInput}\bigr)}_{\text{line response }r_{\rm line}},\qquad r_{\rm line}=-\rho\,I_{\mathsf E},$$
so that
$$F^*K^{-1}F=(\iota+\rho)\,I_{\mathsf E}.$$
Here $\iota=\varepsilon\bigl(1-\frac Y\alpha(1-d_1-\varepsilon e_2-c_1)\bigr)$ by Proposition 5.10. The line response equals $-\rho I_{\mathsf E}$ and enters the split with a subtraction, so its contribution is $+\rho I_{\mathsf E}$.

*Proof.* By Proposition 5.6, $K^{-1}=G\mathcal K^{-1}G$. Lemma 5.11 then gives
$$F^*K^{-1}F=(F^*G)\mathcal K^{-1}(GF)=(B\Omega)^{\mathsf T}\mathcal K^{-1}BW-S^{\mathsf T}\Lambda^{\mathsf T}\mathcal K^{-1}BW .$$
From $\mathcal K\Lambda=\Lambda\mathcal D$ we get $\Lambda\mathcal D^{-1}=\mathcal K^{-1}\Lambda$. Transposing, with $\mathcal K$ and $\mathcal D$ symmetric, gives $\Lambda^{\mathsf T}\mathcal K^{-1}=\mathcal D^{-1}\Lambda^{\mathsf T}$. Hence
$$S^{\mathsf T}\Lambda^{\mathsf T}\mathcal K^{-1}BW=S^{\mathsf T}\mathcal D^{-1}\Lambda^{\mathsf T}BW=S^{\mathsf T}\bigl(d\,\mathcal D^{-1}\mathrm{lineInput}\bigr)=-S^{\mathsf T}\mathcal D^{-1}E_0=-\rho I_{\mathsf E}$$
by Lemma 5.12. Lean: `compression_split` (the subtraction), and `Ord.line_term` and `Tr.line_term` (the value $-\rho I$, via `lineResponse_inverse`/`markedSolution_value` and `transResponse_inverse`/`transSolution_value`). $\square$

*Numerical illustration (ordinary, $a=2$, $x=10$; §6 check S4.referee_example).* Here $\iota=745/2772$ and $\rho=5/44$, so the response matrix is $r_{\rm line}=-(5/44)I_{\mathsf E}$. Subtracting it gives the scalar $\iota+\rho=265/693=R_+/Q_+$. The opposite sign would give $\iota-\rho=215/1386$.

### 5.10 Evaluation for the two families

Specialize $F=\mathbb Q(x)$, $m=a+3$ and $\kappa=m-1-\varepsilon$. The tables below give the rational identities used in the two cases (§6, S1–S4). In both families $Y$, $Y+3$ and $\alpha$ are monic linear polynomials. The displayed expressions for $\alpha-2\beta$ and the additional Lean hypotheses $x_1$, $x_1+my_1$ and $s_0$ are nonzero because their numerators and denominators are monic in $x$ (`Ord.generic`, `Tr.generic`). The core determinant is monic by Proposition 5.6 and Lemma 5.1, which gives invertibility of $\mathcal K$ in $\mathbb Q(x)$.

**Ordinary hook** ($\varepsilon=1$; `OrdScalars`, `OrdDet`, `OrdBdry`).

| quantity | value |
|---|---|
| $Y,\ Y+3,\ \alpha$ | $x-3,\ x,\ x+a-3$ |
| $\beta,\ \gamma,\ \kappa$ | $\frac{a-1}{x},\ \frac1x,\ a+1$ |
| $\alpha-2\beta,\ \delta$ | $\frac{(x-2)(x+a-1)}x,\ \frac{a-1}{(x-2)(x+a-1)}$ |
| $x_1$ | $\frac{x^3+(3a-4)x^2+(2a^2-9a+5)x-3(a-1)^2}{(x-2)(x+a-1)}$ |
| $x_1+my_1$ | $\frac{(x+a-3)(x^2+(2a-1)x-2a+2)}{(x-2)(x+a-1)}$ |
| $s_0$ | $\frac{(x-3)(x+2a)(x+a-3)}{x-2}$ |
| $s_1$ | $\frac{(x-3)(x+a-3)^2(x+2a+2)}{(x-2)(x+a-1)}$ |

*Determinant (D).* Write $t=\binom m3$, $b=m(m-1)$ and $u=\binom m2$, so $|\mathrm{Conf}|=3t$. Proposition 5.9 gives
$$\det K=(Y+3)^{t}\,Y^{2t-b}\,(\alpha-2\beta)^{u}\,\alpha^{\,b-u-2m}\,s_0^{m-1}s_1 .$$
Substituting the table and collecting the linear factors of $x$:

| factor | exponent in $\det K$ | closed form | minus $d$ per factor of $Q_+$ | exponent in $C_+^{\rm corr}$ |
|---|---|---|---|---|
| $x-3$ | $2t-b+m$ | $\frac{(a+3)(a+1)(a-1)}3$ | — | $\frac{(a-1)(a+1)(a+3)}3$ |
| $x-2$ | $u-m$ | $\frac{(a+3)a}2$ | $-(a+1)$ | $\frac{(a-1)(a+2)}2$ |
| $x$ | $t-u$ | $\frac{(a+3)(a+2)(a-2)}6$ | — | $\frac{(a+3)(a+2)(a-2)}6$ |
| $x+a-3$ | $u-m+1$ | $\frac{(a+2)(a+1)}2$ | $-(a+1)$ | $\frac{a(a+1)}2$ |
| $x+a-1$ | $u-1$ | $\frac{(a+1)(a+4)}2$ | $-(a+1)$ | $\frac{(a+1)(a+2)}2$ |
| $x+2a$ | $m-1$ | $a+2$ | $-(a+1)$ | $1$ |
| $x+2a+2$ | $1$ | $1$ | — | $1$ |

So $\det K=$ `ordinaryCoreProduct a` $=C_+^{\rm corr}Q_+^{\,d}$ for $a\ge2$. When two factors coincide (at $a=3$, $x+a-3=x$) their exponents add (`ordinary_core_det`, `ordinary_core_factor_algebra`, `ordinary_two_overlap`, `ordinary_three_overlap`). The exponent of $x$, $t-u=\binom m3-\binom m2$, is the corrected one.

*Boundary (R).* The scalars
$$d_1=\frac{x^2+(a-3)x-2a}{(x-3)(x+2a)(x+a-1)},\qquad e_2=-\frac{x^2-3x+2a}{(x-3)(x-2)(x+2a)(x+a-1)},\qquad c_1=-\frac{a-1}{(x-2)(x+a-1)}$$
satisfy (S1)–(S3) (`Ord.solve`). Hence
$$\iota_+=1-\frac{x-3}{x+a-3}(1-d_1-e_2-c_1)=\frac{(x+a-2)\bigl((a+1)x^2+(2a^2-2a-3)x-2a(2a-1)\bigr)}{Q_+},$$
and by Proposition 5.13
$$F^*K^{-1}F=\Bigl(\iota_++\frac{x+a-2}{(x-2)(x+a-1)}\Bigr)I=\frac{R_+}{Q_+}\,I$$
(`Ord.chain_term`, `Ord.line_term`, `Ord.scalar_identity`, `ordinary_boundary`; this holds for every $a\ge1$ in the written model).

**Transposed hook** ($\varepsilon=-1$; `TrScalars`, `TrDet`, `TrBdry`).

| quantity | value |
|---|---|
| $Y,\ Y+3,\ \alpha$ | $x+1,\ x+4,\ x-a-1$ |
| $\beta,\ \gamma,\ \kappa$ | $-\frac{a+3}{x+4},\ \frac1{x+4},\ a+3$ |
| $\alpha-2\beta,\ \delta$ | $\frac{(x+2)(x-a+1)}{x+4},\ -\frac{a+3}{(x+2)(x-a+1)}$ |
| $x_1$ | $\frac{x^3+(4-a)x^2+(5-3a)x-(a^2+8a+7)}{(x+2)(x-a+1)}$ |
| $x_1+my_1$ | $x+1$ |
| $s_0$ | $\frac{(x+1)(x+4)(x-a-1)^2}{(x+2)(x-a+1)}$ |
| $s_1$ | $(x+1)(x-a-1)$ |

| factor | exponent in $\det K$ | closed form | minus $d$ per factor of $Q_-$ | exponent in $C_-$ |
|---|---|---|---|---|
| $x+4$ | $t-u+m-1$ | $\frac{a(a+1)(a+2)}6$ | — | $\frac{a(a+1)(a+2)}6$ |
| $x+2$ | $u-m+1$ | $\frac{(a+2)(a+1)}2$ | $-(a+1)$ | $\frac{a(a+1)}2$ |
| $x+1$ | $2t-b+m$ | $\frac{(a+3)(a+1)(a-1)}3$ | — | $\frac{(a-1)(a+1)(a+3)}3$ |
| $x-a+1$ | $u-m+1$ | $\frac{(a+2)(a+1)}2$ | $-(a+1)$ | $\frac{a(a+1)}2$ |
| $x-a-1$ | $u-1$ | $\frac{(a+1)(a+4)}2$ | $-(a+1)$ | $\frac{(a+1)(a+2)}2$ |

So $\det K=$ `transposeCoreProduct a` $=C_-Q_-^{\,d}$ for $a\ge1$, and $C_-$ is exactly (3.3.8) (`transpose_core_det`, `transpose_core_factor_algebra`). With
$$d_1=\frac1{x+1},\qquad e_2=\frac1{(x+2)(x-a+1)},\qquad c_1=\frac{a+3}{(x+2)(x-a+1)}$$
(`Tr.solve`) we get
$$\iota_-=-\Bigl(1-\frac{x+1}{x-a-1}(1-d_1+e_2-c_1)\Bigr)=\frac{(x-a)\bigl((a+1)x+2a+1\bigr)}{Q_-},$$
and
$$F^*K^{-1}F=\Bigl(\iota_-+\frac{x-a}{(x+2)(x-a-1)}\Bigr)I=\frac{R_-}{Q_-}\,I$$
The written evaluation holds for every $a\ge1$ (`Tr.chain_term`, `Tr.line_term`, `Tr.scalar_identity`, `transpose_boundary`).

### 5.11 Normalization and the printed coefficient lists

Let $P_k:=QP^U_{k+2}-RP^U_{k+1}$ for $k\in\mathbb Z$ (Lean `seedP Q R k`).

**Lemma 5.14 (recurrence, coprimality, degrees).**

1. $P_{k+2}=xP_{k+1}-P_k$ for all $k\in\mathbb Z$, and $P_{-1}=Q$, $P_{-2}=R$.
2. For the ordinary hook with $a\ge2$ and the transposed hook with $a\ge1$, $\gcd(P_k,P_{k+1})=1$ for all $k\in\mathbb Z$.
3. For $k\ge0$, $P_k$ is monic of degree $\deg Q+k+1$.

*Proof.* (1) follows from the recurrence for $P^U$ and from $P^U_0=0$, $P^U_{\pm1}=\pm1$ (`seedP_step`).

(2) Every root of $Q$ is a non-root of $R$. For the ordinary hook,
$$R_+(1-a)=(a+2)(a^2-a+2),\quad R_+(2)=2a(a+2)(a-1),\quad R_+(-2a)=-4a(a+2)^2,\quad R_+(3-a)=-a(a+2)(a-1),$$
all nonzero for $a\ge2$. (At $a=1$, $R_+(2)=0$.) For the transposed hook,
$$R_-(-2)=(a+2)^2,\quad R_-(a-1)=-a(a+2),\quad R_-(a+1)=(a+2)^2,$$
all nonzero for $a\ge1$. So $\gcd(P_{-2},P_{-1})=\gcd(R,Q)=1$. The map $(P_k,P_{k+1})\mapsto(P_{k+1},xP_{k+1}-P_k)$ is unimodular, so coprimality propagates in both directions (`ordinary_seeds_coprime`, `transpose_seeds_coprime`, `seedP_coprime`, `ordinaryP_coprime`, `transposeP_coprime`).

(3) For $j\ge1$, $P^U_j$ is monic of degree $j-1$. Moreover $Q$ is monic and $\deg R<\deg Q$ (`nativeU_degree`, `seedP_degree`, `ordinaryP_monic_degree`, `transposeP_monic_degree`). $\square$

**Lemma 5.15 (Chebyshev expansion).** Let $H(z)=z^2Q(z+z^{-1})-zR(z+z^{-1})=\sum_jc_jz^j$. Then for all $k\in\mathbb Z$,
$$P_k=\sum_jc_j\,P^U_{k+j}.$$
For $(Q_+,R_+)$ the coefficients $c_6,\dots,c_{-2}$ are the coefficients of (3.3.9) as printed. For $(Q_-,R_-)$ the coefficients $c_5,\dots,c_{-1}$ are
$$1,\ -2(a-1),\ a(a-5),\ 3a(a-1),\ +2(a^2-2a-1),\ a(a-1),\ -(a+1),$$
which is (3.3.10) with the plus sign.

*Proof.* Substitute $x=z+z^{-1}$, which embeds $\mathbb C[x]$ into $\mathbb C[z^{\pm1}]$, and use $P^U_j=(z^j-z^{-j})/(z-z^{-1})$ for all $j\in\mathbb Z$. Since $Q(z+z^{-1})$ and $R(z+z^{-1})$ are invariant under $z\mapsto z^{-1}$,
$$(z-z^{-1})P_k=z^kH(z)-z^{-k}H(z^{-1})=\sum_jc_j(z^{k+j}-z^{-k-j})=(z-z^{-1})\sum_jc_jP^U_{k+j}.$$
The coefficient lists are obtained by expanding $H$; §6 (S6) does this symbolically in $a$. For example, the transposed $z^1$ coefficient is $3+(a^2-4a-1)-(a+2)(2-a)=2(a^2-2a-1)$. This gives a plus before the displayed term $2(a^2-2a-1)P^U_{k+1}$. Since $(a-1)^2\ne2$ for integer $a$, a minus would change the polynomial. Lean proves the same identities by recurrence manipulation for all $k\in\mathbb Z$ (`ordinaryP_seed_identity`, `transposeP_seed_identity`). $\square$

**Remark 5.16 (uniqueness).** Because $P_k$ and $P_{k+1}$ are coprime, the monic greatest common divisor of $D_{a+4+k}$ and $D_{a+5+k}$ is exactly $C$. Then $P_k^d$ is $D_{a+4+k}/(sC)$, and monicity fixes $P_k$. So the normalized pair $(C,P)$ of Theorem 3.19 is determined by the determinants, and the corrected (3.3.7) and plus-sign (3.3.10) are forced.

**Proof of the Theorem.**

* Ordinary hook, $a\ge2$. §5.10 gives (D) with $C=C_+^{\rm corr}$, $Q=Q_+$, and (R) with $R=R_+$. Proposition 5.3 gives $D_{a+4+k}=(a+2)^{\binom m2+k+1}C_+^{\rm corr}P_k^{\,d}$ for every $k\ge0$. Lemma 5.14 gives the recurrence, coprimality, monicity and degree clauses. $C_+^{\rm corr}$ is monic. Lemma 5.15 identifies $P_k$ with (3.3.9) for all $k\in\mathbb Z$.
* Transposed hook, $a\ge1$. The same argument applies with $(C_-,Q_-,R_-)$ and (3.3.10) with the plus sign. $\square$

### 5.12 How the Lean endpoints package this proof

The Lean development proves (D) and (R) for the full core: `ordinary_core_det`, `transpose_core_det`, `ordinary_boundary`, `transpose_boundary`. It reaches `ordinary_normalized`/`transpose_normalized` through an interface inherited from the earlier lane, which splits the core into the constant line in each fibre and its complement:

* `residualCore a b` $=K(I-\mathcal J\mathcal L)+\mathcal J\mathcal L$, where $\mathcal J\mathcal L$ is the projection onto the gauged constant line $\Lambda$ (`lineJ`, `lineL`). Then $\det K=\det\mathcal D\cdot\det(\texttt{residualCore})$ (`native_core_split_det`).
* `residualCompression a b` $=F^*K^{-1}(I-\mathcal J\mathcal L)F$. Then $F^*K^{-1}F=\texttt{residualCompression}+\texttt{firstResolvent}\cdot I$, where
$$\texttt{firstResolvent}=\tfrac{a+2}{a+1}\cdot\tfrac{x+a-2}{(x-2)(x+a-1)}\ \text{(ordinary)},\qquad \tfrac{a+2}{a+1}\cdot\tfrac{x-a}{(x+2)(x-a-1)}\ \text{(transposed)}$$
(`native_boundary_split`, `first_summand_evaluation`). This is a different split of the same matrix from Proposition 5.13: here $F^*$ is not decomposed.

`ResidualFinal` divides the full core determinant by $\det\mathcal D\ne0$ and subtracts `firstResolvent` from the full boundary scalar. This yields the four residual statements:

* `residual_det_ordinary` (`ordinaryResidualProduct`, $a\ge2$);
* `residual_det_transpose` (`transposeResidualProduct`, $a\ge1$);
* `residual_boundary_ordinary` and `residual_boundary_transpose`, with `missingBoundary` $=R/Q-$`firstResolvent`, for all natural $a$ in Lean.

The inherited `ordinary_normalized_of_residual` and `transpose_normalized_of_residual` then multiply the line factor back in and add `firstResolvent` back. They call `ordinary_normalized_of_seed` and `transpose_normalized_of_seed`, whose hypotheses are exactly (D) and (R).

The residual detour is therefore an exact round trip: it removes the line part and restores it, and nothing in the final statements depends on it. The written proof above applies (D) and (R) directly, which is the content of `ordinary_normalized_of_seed`. The four residual statements are kept because they are the targets the earlier lane left open. They follow from the full statements, and §6 checks them numerically (N4 residual compression, N6 residual determinants). The direct composition `ordinary_normalized_of_seed a ha (ordinary_core_det a ha) (ordinary_boundary a)` has matching hypotheses. It was **not** compiled as a separate declaration, and no claim here depends on it.

---

## 6. Independent verification

`scripts/verify_brauer_hook.py` (Python 3, standard library only) rebuilds everything from the source's definitions (§2.1–2.5): eligible cups (3.2.1), through orders, the gluing permutations of (3.13), the permutation-module realization of the two hook Specht modules, and the Gram matrix $\Gamma$. It shares no code with the Lean development or with the referee's script.

All arithmetic is exact:

* Python integers and `Fraction`;
* bivariate polynomials and rational functions in $(x,a)$ with rational coefficients, with identities checked by cross-multiplication;
* characteristic polynomials of integer matrices, computed modulo enough 61-bit primes that the product exceeds twice a Hadamard bound for every coefficient. Equality over $\mathbb Z$ is therefore *proved*, not sampled.

The run was pinned with `taskset -c 28-31` under `timeout 1800` and `prlimit --as=8 GiB` (`scripts/run_checks.sh`). The receipt and outputs are in `checks/` (`verify-output.txt`, `results.json`, `run-receipt.json`, `time-v.txt`). Result: **all 947 checks in 68 groups pass** (wall time 185 s; receipt `checks/run-receipt.json`, script SHA-256 `e038008f…40926`). A copy of the source PDF used for §1 is in `source/`.

| ID | what is checked | range |
|---|---|---|
| N1 | Gram from the source pairing; $M^{-1}\Gamma'=A$; $\Gamma'$ symmetric; $\det(I+J_d)=d+1$; $\det(xI+A)=C\,P_k^{d}$ exactly over $\mathbb Z$; $P_k=QP^U_{k+2}-RP^U_{k+1}$ | ordinary $a=2..5$ and transposed $a=1..5$ with $k=0..4$; both families $a=6,7$ with $k=0..2$ (largest matrix $384\times384$) |
| N2 | (D): $\det K=$ core product $=C\,Q^{d}$, exact over $\mathbb Z$ | ordinary $a=2..8$, transposed $a=1..8$ (up to $495\times495$) |
| N3 | cardinalities; slot bijection; gauge closed form $\theta=(-1)^{l+r+1}$; triangle sign (Lemma 5.4); gauge sign (Lemma 5.5); **bridge** (Prop. 5.6) entrywise; **eight incidence identities** (Lemma 5.7); boundary entries of $F,F^*$ (Lemma 5.11); $F^*\ne F^{\mathsf T}$; $GF=BW$; $F^*G=(B\Omega)^{\mathsf T}-(\Lambda S)^{\mathsf T}$; test data (T1)–(T8); $\mathcal K\Lambda=\Lambda\mathcal D$; $\Lambda^{\mathsf T}BW=-E_0$; $N^{\mathsf T}E_0=\varepsilon U$ | $a=1..6$, both families (30 checks each) |
| N7 | Prop. 5.9 at exact rational points: step 1 ($\det\mathcal T$); step 2 ($Y(I+\varepsilon B^{\mathsf T}\mathcal T^{-1}B)=Z$ and the determinant relation); step 3 ($\det Z_1$, $Z_1^{-1}$, $Z=Z_1+\Phi\Psi$); step 4 (**the $2\times2$ block form** and $\det=s_0^{m-1}s_1$); the assembled identity | $a\le5$ (and ordinary $a=1$), $x\in\{10,-7/3\}$ |
| N4 | Prop. 5.10 and 5.13 at exact points: native $F^*K^{-1}F=(R/Q)I$; incidence term $=\iota I$; $Zy=W$; $X$ explicit; $B^{\mathsf T}X=\varepsilon(W-Yy)$; $S^{\mathsf T}\mathcal D^{-1}E_0=\rho I$; **line response $=-\rho I$**; $\iota I-r_{\rm line}=(R/Q)I$; $\iota I+r_{\rm line}\ne (R/Q)I$; `compression_split`; residual compression $=R/Q-$`firstResolvent` | ordinary $a=2..5$, transposed $a=1..5$, $x\in\{10,-7/3,29/5\}$ ($a\le4$) |
| N5 | (R) as an identity of rational functions: $Q\,F^*\operatorname{adj}(K)F=R\det K\cdot I$ has degree $\le N+3$ and is verified at $N+4$ points with $\det K\ne0$ | ordinary $a=2,3,4$; transposed $a=1..4$ |
| N6 | residual interface: $\det(\texttt{residualCore})=$ residual product; $\det K=\det\mathcal D\cdot\det(\texttt{residualCore})$; line $\times$ residual $=$ core product | ordinary $a=2..4$, transposed $a=1..4$, $x\in\{10,-11\}$ |
| S1 | parameter values of §5.10 ($Y,\alpha,\beta,\alpha-2\beta,\delta,\kappa,x_1,x_1+my_1,s_0,s_1$) | symbolic in $(x,a)$ |
| S2 | **compression scalars** $d_1,e_2,c_1$ satisfy (S1)–(S3) | symbolic |
| S3–S5 | $\lambda,\rho$ closed forms; $\iota$ closed forms; $\iota+\rho=R/Q$ and $\iota-\rho\ne R/Q$ (**sign**); referee example $745/2772,\ 5/44,\ 265/693,\ 215/1386$; `missingBoundary` | symbolic |
| S6–S7 | Laurent coefficients of $z^2Q-zR$ equal (3.3.9) and plus-(3.3.10); the minus reading fails; $QP^U_{k+2}-RP^U_{k+1}$ equals the printed lists, $P_{-1}=Q$, $P_{-2}=R$ | symbolic in $a$; integer $a\le12$, $k=-8..8$ |
| S8–S9 | residues $R(z)$ at roots of $Q$; nonvanishing for ordinary $2\le a<200$ and transposed $1\le a<200$, failure at ordinary $a=1$; monic degrees; Euclid $\gcd(P_k,P_{k+1})=1$ | as stated |
| S10–S11 | exponents of Prop. 5.9 $=$ core product $=C\,Q^{d}$ (merged factors); same as polynomials in $a$; printed vs corrected $x$-exponent agree only at $a\in\{-3,-1,4\}$; corrected $C$ at $a=3$ equals the source's $C^{(4,1)}$ | $a\le60$; symbolic |
| S12 | literal refutation: printed degrees $136$ and $5$, total $166$, versus $174$ | $a=5$ |
| S13 | tail continuant $\det\mathcal P_n(x;y)=yP^U_n-P^U_{n-1}$ (symbolic, $n\le11$; brute force $n\le6$); the plus recurrence would give $x^2+1$ | |

These checks are evidence for the written proof and an independent recomputation of the model at small parameters. They are not a substitute for the general proof, which is §5 together with the Lean development. The referee's separate script (21 matrices, ordinary $a=2,3,4$ and transposed $a=1..4$, $k=0..2$) agrees with the same formulas.

---

## 7. Relation to earlier work and attribution

* **Source.** The one-cup basis and gluing rules (3.9)–(3.13), the tail recursion (3.2.4)–(3.2.9) and Theorem 3.19 (via Lemma 3.20) are Morris and Martin's. Lemma 5.1–Proposition 5.3 are a matrix form of their path mechanism. **Remark 3.33 already displays the backward seeds** $P_{l+3}=Q_\pm$ and $P_{l+2}=R_\pm$ for both hook families, as observations for the cases they computed (Proposition 3.32 lists $1\le l\le7$ for the hooks). Through the recurrence, those seeds determine the coefficient lists. (3.31) displays $C^{(4,1)}$, which our corrected formula reproduces at $a=3$. What this paper adds is a proof, for all heights, that these seeds and the corrected $C$ are the actual normalized factors, together with the explicit identification of the three print defects.
* **Earlier proof route.** Within this campaign, an earlier producer proof (`brauer-hook-372351-native-determinants-formal-sol62-20261118-r1/inputs/PRODUCER/PROOF.md`) and its independent review (`…/inputs/REVIEW/REPORT.md`) obtained the same $C$, $Q$, $R$ by a different, spectral argument. They write the core as $T_m-(1+c(\nu))$ on induced modules, get multiplicities from the two-strip branching rule via the Young seminormal form (Vershik–Okounkov, arXiv:math/0503040, Thm. 5.8, Prop. 6.2), and get the boundary resolvent from explicit projector weights $w_{\nu,\mu}$. The earlier lane (`brauer-hook-372351-native-determinants-formal-sol62-20261118-r1`) formalized the native model, the tail reduction, the line part and the conditional endpoints; that is the inherited Lean code. The incidence factorization of §5.2–5.10 (Propositions 5.6, 5.9, 5.10, 5.13) is the part new to this proof. This factorization supplies the evaluation used in the Mathlib formalization and avoids the need for Specht-module branching theory in that development.
* **Kadár–Martin–Yu** (arXiv:1401.1774, Prop. 4.22, Cor. 4.23, Prop. 5.3) construct the cell-module basis from Specht modules and half diagrams, which the source uses in (3.12), and the restriction filtration. They give no Gram compression coefficients.
* **Kadár–Martin** (arXiv:2002.05478, §5) compute a height-zero tridiagonal Gram extension with one-dimensional fibres, including the Laurent parametrization used in Lemma 5.15.
* **Alraddadi–Parker** (arXiv:2407.07028, Lemma 5.2, Thm. 5.3) give the "$M+\delta I$ with $M$ real symmetric" non-degeneracy mechanism. It underlies the monicity used in the degree count of Proposition 3.1; the source cites it as [1].
* **Rui–Si** (arXiv:math/0607267v3, Prop. 4.2, Thm. 4.11) factor Gram determinants of full Brauer cell modules through up-down tableaux. The core block $K$ is the metric-normalized operator for the direct sum of ordinary Brauer one-cup cell forms on $m$ sites obtained by restricting the fibre to the permutations of its $m-2$ core through sites. Thus (D) could in principle be transferred from their results. The earlier review found no evaluation there of the marked boundary compression (R) for the restricted Kadar–Yu module.

**Limits of the literature review.** This revision did no new literature search. It re-read only the source (v1, same SHA-256 as recorded by the earlier lane) at the cited passages. The statements above about the other works rest on the earlier review's reading of the cited passages. That review could not access the body of a selected Enyang–Goodman work (robots-blocked). It did not read De Visscher–Martin (the source's [7], King polynomials, cited in Remark 3.33), other arXiv versions of the source, or a publisher version, and it did not survey the wider literature on Brauer and Kadár–Yu Gram determinants. We therefore make no priority claim beyond the following: in the material reviewed, we found no earlier proof of the corrected statements for all heights.

---

## 8. Scope and limits

* The results are stated for the native model of §2. Its identification with the source's definitions is the earlier lane's crosswalk and inherited Lean modules; it is not re-derived here. §6 recomputes it independently for small parameters. Normalization is up to the nonzero constant $\det M$, as Theorem 3.19 allows.
* The ranges are as follows. The normalized theorem holds for ordinary $a\ge2$, transposed $a\ge1$, tail $k\ge0$; the recurrence and coprimality hold for all integer $k$. (D) holds in the same ranges. The written calculation of (R) covers $a\ge1$ in both families, and the Lean boundary declarations include $a=0$. The ordinary formulas fail at $a=1$: the $x$-exponent from Proposition 5.9 is negative there, and $\gcd(Q_+,R_+)\ne1$.
* No spectral theory of the symmetric group is used in §5. Eigenvalues and multiplicities appear only through the explicit factorizations.
* The Lean code is unchanged from the previous version and is reproduced byte-for-byte in `LEAN-SOURCE-APPENDIX.md`. The axiom and replay claims rest on that lane's `REPORT.md`; this revision did not re-run Lean.

---

## 9. Map from proof steps to Lean declarations

| Step | Statement | Lean declaration (module) |
|---|---|---|
| §2.1–2.5 | cups, through order, gluing, fibre, Gram $=M(xI+A)$ | `Eligible`, `eligible_core_or_tail`, `throughOrder`, `trace_shared`, `transport_fixes_inactive` (CupDiagram); `activeTransport`, `nativeMove`, `interaction`, `nativeGram`, `gram_eq_metric_char`, `nativeDet_eq`, `metric_det_ne` (NativeGram); `standardCoords`, `hookAct` (HookFiber); `transposeCoords` (TransposedFiber); `invariant_hook_pairing` (PairingBridge) |
| §2.6 | gauge | `cupOrientation`, `orientation_first_tail` (CupOrientation); `coreOrientation` (TransposedLine); `gauge` (LineSplitting) |
| §2.7 | blocks, stability | `native_normal_blocks`, `coreMatrix_det_monic` (NativeBlocks); `coreMatrix_stable`, `boundaryCompression_stable` (CoreStability) |
| §3.1 | literal refutation | `native_height_five_degree` (NativeGram); `printedC_five_degree`, `printedP_five_polynomial`, `height_five_printed_negation`, `printed_ordinary_clauses_negation` (LiteralNegation) |
| §3.2 | printed and corrected formulas | `ordinaryCPrinted`, `ordinaryCCorrected`, `transposeCPrinted`, `printedOrdinaryP`, `correctedTransposeP`, `nativeU` (PrintedHook) |
| Lemma 5.1, 5.2, Prop 5.3 | Schur step, continuant, assembly | `native_schur_path`, `subtract_marked_block`, `native_det_of_core` (NativeSchur); `scalarPath_modified_det`, `fiberPath_det` (Continuant) |
| §5.2 | slot sites, configurations, cardinalities, incidence matrices | `slotSite`, `toConf_bijective`, `confEquiv` (SiteSlots); `card_sconf`, `card_opair`, `card_tri` (SiteChain); `card_core` (CoreIncidence); `wInc`, `fSign`, `incB`, `incT`, `incL`, `incK`, `incH`, `incD` (SiteMatrices) |
| Lemma 5.4 | triangle sign | `sign_triangle`, `pair_cases` (SiteTriples) |
| Lemma 5.5 | gauge sign | `transport_label_decomposition`, `through_sign_orientation` (CupOrientation); `sign_endpointPerm` (TransposedLine); `gauge_sign` (SiteBridge) |
| Prop 5.6 | bridge | `transport_slot`, `hookAct_delta_fix` (SiteSlots); `BBt_entry` (SiteBridge); `PT_entry` (SiteTriples); `bridge_entry` (SiteBridgeEntry); `core_site_form`, `core_det_form` (CoreSiteForm); `core_form_CI`, `core_symm` (Compress1) |
| Lemma 5.7 | incidence identities | `gram_B`, `gram_H`, `gram_D`, `incD_H`, `gram_N` (SiteMatrices); `gram_T`, `incT_B`, `gram_K` (SiteTriples); `site_identities` (SiteChain) |
| Lemma 5.8 | $I$/$J$ blocks | `sylvester_shift`, `det_IJ`, `det_blocks_IJ`, `IJ_mul_of_J` (ChainIJ) |
| Prop 5.9 | determinant reduction | `tri_det`, `tri_inv_eq`, `schur_pairs_raw`, `schur_pairs`, `zone_det`, `zone_inv_right` (ChainDet); `zform_split`, `block_form` (ChainBlock); `chain_det`, `Chain.Identities`, `Chain.Generic` (ChainFinal) |
| Prop 5.10 | compression | `Chain.TestData`, `Chain.SolveScalars`, `zform_solution`, `chain_compress` (ChainSolve) |
| Lemma 5.11 | boundary blocks, test data | `bIn_marked`, `bOut_marked` (Compress2); `wV`, `OmV`, `UV`, `RV`, `SelV`, `LamCI` (Compress3); `test_data` (Compress4); `gauge_in`, `gauge_out` (Compress5); `marked_orientation_sign` (TransposedLine); `transposed_marked_input_action`, `transposed_marked_output_action` (TransposedBoundary) |
| Lemma 5.12 | line | `lineInput`, `lineResponse_inverse`, `markedSolution_value` (OrdinaryLineResolvent); `transResponse_inverse`, `transSolution_value` (TransposedLineResolvent); `coreMatrix_line_frac`, `linePolynomial` (LineSplitting); `lineJ_eq`, `lineJ_transpose` (Compress5); `line_symm` (Compress1); `boundary_in_line` (BoundarySplitting) |
| Prop 5.13 | signed compression split | `compression_split` (Compress6); `Ord.line_term` (OrdBdry); `Tr.line_term` (TrBdry) |
| §5.10 | ordinary evaluation | `Ord.generic`, `Ord.sZero`, `Ord.sOne`, `Ord.bx1`, `Ord.bx1m` (OrdScalars); `ord_cards`, `ordinary_core_det` (OrdDet); `Ord.solve`, `Ord.chain_term`, `Ord.scalar_identity`, `ordinary_boundary` (OrdBdry); `ordinary_core_factor_algebra` (FactorArithmetic) |
| §5.10 | transposed evaluation | `Tr.generic` (TrScalars); `tr_cards`, `transpose_core_det` (TrDet); `Tr.solve`, `Tr.chain_term`, `Tr.scalar_identity`, `transpose_boundary` (TrBdry); `transpose_core_factor_algebra` (FactorArithmetic) |
| Lemma 5.14 | recurrence, coprimality, degrees | `seedP`, `seedP_step`, `seedP_coprime`, `seedP_degree`, `nativeU_degree`, `ordinary_seeds_coprime`, `transpose_seeds_coprime`, `ordinaryP_coprime`, `transposeP_coprime`, `ordinaryP_monic_degree`, `transposeP_monic_degree` (SeedAlgebra) |
| Lemma 5.15 | coefficient lists | `ordinaryP_seed_identity`, `transposeP_seed_identity` (PrintedHook) |
| Theorem | normalized endpoints | `ordinary_normalized_of_seed`, `transpose_normalized_of_seed` (FactorArithmetic); `ordinary_normalized`, `transpose_normalized`, `native_core_dets` (ResidualFinal); `NativeNormalized` (LiteralNegation) |
| §5.12 | residual interface | `residualCore`, `native_core_split_det` (LineSplitting); `residualCompression`, `firstResolvent`, `native_boundary_split` (BoundarySplitting); `ordinaryResidualProduct`, `transposeResidualProduct`, `missingBoundary`, `ordinary_core_product_split`, `transpose_core_product_split`, `ordinary_normalized_of_residual`, `transpose_normalized_of_residual` (ResidualTargets); `residual_from_full`, `residual_det_ordinary`, `residual_det_transpose`, `residual_boundary_ordinary`, `residual_boundary_transpose` (ResidualFinal) |

## Appendix: notation

| symbol | meaning |
|---|---|
| $x$ | loop parameter (source $\alpha$) |
| $a,\ m=a+3,\ d=a+1,\ n=a+4+k$ | height, core sites, fibre dimension, rank |
| $\varepsilon$ | $+1$ ordinary, $-1$ transposed |
| $\mathsf E=\{0,\dots,a\}$ | fibre coordinates; column set of all test matrices |
| $\sigma(p,i)$ | site of the $i$-th through strand of $p$ |
| $\theta,\ g,\ G$ | orientation sign, gauge, diagonal gauge matrix |
| $K=xI+A_{\rm core}$, $F$, $F^*$ | core block, boundary column block, reverse boundary block |
| $\mathcal K=YI+\varepsilon BB^{\mathsf T}+TT^{\mathsf T}$, $Y=x-1-2\varepsilon$ | gauged core in site coordinates |
| $\mathcal D=(x-2\varepsilon)I+\varepsilon NN^{\mathsf T}$ | line operator on cups |
| $\iota$, $\rho$, $r_{\rm line}=-\rho I$ | incidence scalar, line scalar, signed line response |
| $\kappa=m-1-\varepsilon$ | Lean `gee` |
| $Q,R,P_k=QP^U_{k+2}-RP^U_{k+1}$ | seeds and normalized Chebyshev factor |
