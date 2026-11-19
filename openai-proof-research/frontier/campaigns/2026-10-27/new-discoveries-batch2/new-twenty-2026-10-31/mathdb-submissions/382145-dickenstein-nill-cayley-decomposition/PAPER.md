# Lattice polytopes of large Q-codegree are Cayley sums: a direct proof of the Dickenstein–Nill Cayley decomposition conjecture

*Standalone manuscript for MathDB 382145. The direct proof and its exact Lean appendix passed independent replay and final manuscript review. Current registry qualification and literature priority remain open.*

## Abstract

Let $P\subseteq\mathbb R^n$ be an $n$-dimensional lattice polytope with Q-codegree $\mu(P)$. Dickenstein and Nill, as reformulated by Di Rocco, Haase, Nill and Paffenholz (DRHNP, Conjecture 3; restated by Garzón Mora and Haase as Conjecture 1.1), conjectured the following. If $\mu(P)>\frac{n+1}{2}$, then $P$ is a Cayley sum of lattice polytopes of dimension at most $\lfloor 2(n+1-\mu(P))\rfloor$.

We prove this. The proof is direct and does not use DRHNP Theorem 3.4:

1. Take an optimal dual certificate $y$ of minimal support for the linear program that defines $1/\mu(P)$.
2. Keep the facets with heavy weight $y_i>\frac{1}{2\mu(P)}$, or all but one support facet when every support weight is heavy.
3. On the vertices of $P$, the corresponding integral slack map takes values in the vertex set of a unimodular simplex and hits every vertex.
4. This lattice projection splits over $\mathbb Z$, and its fibres give the Cayley factors.

The whole argument is formalized in Lean 4 with Mathlib, against literal definitions of facets, primitive normals, the adjoint sets $P^{(s)}$, $\mu$ and Cayley polytopes.

## 1. Definitions and statement

Throughout, $n\ge 0$ and $V\subset\mathbb Z^n$ is finite. $P=\operatorname{conv}V$ is assumed full-dimensional, i.e. $\operatorname{aff}P=\mathbb R^n$.

**Facets and primitive normals** (DRHNP Definition 1.1, Remark 1.2). A vector $a\in\mathbb Z^n$ is *primitive* if the only common divisors of its entries are $\pm1$, i.e. $\gcd(a)=1$. A primitive $a$ is the *inward facet normal* of $P$ if all of the following hold:

- $b_a:=\min_{x\in P}\langle a,x\rangle$;
- $F_a:=\{x\in P:\langle a,x\rangle=b_a\}$ is nonempty;
- $\dim\operatorname{aff}F_a=n-1$.

Write $\mathcal N(P)$ for the set of these normals; it is the set of rows of the unique minimal primitive inequality description used by DRHNP.

**Adjoint sets and Q-codegree** (DRHNP Definition 1.5). For $s>0$ let
$$P^{(s)}=\{x\in\mathbb R^n:\ \langle a,x\rangle\ge b_a+s\ \text{ for all } a\in\mathcal N(P)\}.$$
Let $\sigma(P)=\sup\{s>0: P^{(s)}\neq\emptyset\}$ and $\mu(P)=\sigma(P)^{-1}$.

**Cayley sums** (DRHNP Definition 3.1, GMH Definition 4.1). For lattice polytopes $P_0,\dots,P_t\subseteq\mathbb R^k$,
$$P_0*\cdots*P_t=\operatorname{conv}\big((P_0\times\{0\})\cup(P_1\times\{e_1\})\cup\cdots\cup(P_t\times\{e_t\})\big)\subseteq\mathbb R^k\times\mathbb R^t.$$
$P$ is a *Cayley polytope of length $t+1$* if an affine lattice isomorphism $\mathbb Z^n\cong\mathbb Z^k\times\mathbb Z^t$ identifies $P$ with such a sum. The structure is nontrivial when $t\ge1$.

**Theorem 1** (DRHNP Conjecture 3 = GMH Conjecture 1.1 = MathDB 382145). Let $P$ be an $n$-dimensional lattice polytope with $\mu(P)>\frac{n+1}{2}$. Then $P$ is a Cayley polytope $P_0*\cdots*P_t$ with $t\ge1$, all $P_i$ nonempty lattice polytopes in $\mathbb R^k$, and
$$k\le\lfloor 2(n+1-\mu(P))\rfloor .$$
In particular $\dim P_i\le\lfloor 2(n+1-\mu(P))\rfloor$ for every $i$, and $n=k+t$.

The bound is on the ambient lattice $\mathbb R^k$ of the factors. This is the reading of DRHNP Theorem 3.4 ("Cayley sum of lattice polytopes in $\mathbb R^m$ with $m\le d(P)$"), and it implies the per-factor reading.

### 1.1 Remarks on the definitions

1. **Only actual facets enter.** $\mathcal N(P)$ consists of the primitive normals of the $(n-1)$-dimensional faces, and nothing else (DRHNP Remark 1.2 shows why lower-dimensional supporting inequalities must be excluded). The proof uses only four properties of this family:
   - (i) it is finite;
   - (ii) each $a\in\mathcal N(P)$ is a nonzero integral vector;
   - (iii) $b_a=\min_{v\in V}\langle a,v\rangle\in\mathbb Z$ is valid on $P$;
   - (iv) $P$ is full-dimensional.

   The H-representation $P=\bigcap_a\{\langle a,\cdot\rangle\ge b_a\}$ (Minkowski–Weyl) is **not** a premise of the proof. It is needed only for facts the proof never uses, such as $P^{(0)}=P$. The formal definition still agrees with the native facet presentation, because the two families of rows are literally the same:
   - Each formal normal $a$ cuts out an $(n-1)$-dimensional face, i.e. a facet. A facet spans a unique hyperplane, so its primitive inward normal is unique (this is the Lean lemma `facetNormal_eq_of_touch`), and $a$ is the native row of that facet with the same offset $b_a$.
   - Conversely, every native facet row satisfies the four defining conditions.
2. **Conventions.** For $n\ge1$ the shift set $\{s>0:P^{(s)}\ne\emptyset\}$ is nonempty. The barycentre $\bar v=\frac1{|V|}\sum_{v\in V}v$ lies in $P^{(1/|V|)}$: for every $a\in\mathcal N(P)$ the integers $\langle a,v\rangle-b_a$ are $\ge0$ and not all $0$, by full dimension and $a\ne0$. This was kernel-checked by the reviewer as `ReviewR2.adjoint_barycentre`. For native polytopes with $n\ge1$ the shift set is also bounded, and DRHNP Proposition 1.6 shows that $\mu(P)$ is a positive rational. If it were unbounded, the convention $1/\infty=0$ would give $\mu=0$, and the hypothesis would fail. The Lean value has the same behaviour: `sSup` of an unbounded set is $0$, so `qCodegree` is $0$ (`ReviewR2.qCodegree_eq_zero_of_unbounded`). The formal hypothesis therefore holds exactly when the native one does.
3. **Small dimensions.** For $n=0$ there are no primitive vectors and no facets. The shift set is $(0,\infty)$, so $\mu=0$ and the statement is vacuous. For $n=1$ the hypothesis $\mu>1$ is satisfied only by the unit segment ($\mu([0,m])=2/m$). The unit segment is the Cayley sum of two points in $\mathbb R^0$, and the Lean sanity module proves this case through the main theorem.
4. **Strictness is sharp.** $2\Delta_n$ has $\mu=\frac{n+1}{2}$ and lattice width $2$. A nontrivial Cayley polytope has lattice width $1$, so $2\Delta_n$ is not a Cayley polytope and the strict inequality cannot be weakened.

## 2. Notation for the proof

Fix $P=\operatorname{conv}V$ with $\mu=\mu(P)>\frac{n+1}{2}$. Then $\sigma=1/\mu\in(0,\frac2{n+1})$, and in particular $n\ge1$.

Index the finite facet family as $a_i$, $i\in I$, with offsets $b_i\in\mathbb Z$. Define the slack functions $\ell_i(x)=\langle a_i,x\rangle-b_i$. For $v\in V$, $\ell_i(v)\in\mathbb Z_{\ge0}$, and $\ell_i$ is not identically zero on $V$, since $a_i\ne0$ and $P$ is full-dimensional.

**Lemma 0 (finiteness).** $\mathcal N(P)$ is finite. *Proof.* Suppose $a,a'\in\mathcal N(P)$ have the same set of generators $v\in V$ with $\ell(v)=0$. Then $F_a$ lies in the hyperplane $\{\langle a',\cdot\rangle=b_{a'}\}$, because points of $F_a$ are convex combinations of those generators. Since $\dim F_a=n-1$, $\ker\langle a,\cdot\rangle\subseteq\ker\langle a',\cdot\rangle$, so $a'=\lambda a$. Validity on the full-dimensional $P$ forces $\lambda>0$, and primitivity with Bézout forces $\lambda=1$. Hence $a\mapsto\{v\in V:\ell_a(v)=0\}$ is injective into $2^V$. $\square$

## 3. The optimal certificate

**Lemma 1 (certificate).** There is $y\in\mathbb R^I_{\ge0}$ with
$$\sum_i y_i=1,\qquad \sum_i y_i a_i=0,\qquad \sum_i y_i b_i=-\sigma .$$
Consequently $\sum_i y_i\ell_i(x)=\sigma$ for **every** $x\in\mathbb R^n$.

*Proof.* Consider the finite linear program $\max\{s:\ \langle a_i,x\rangle-s\ge b_i\ \forall i\}$ in the variables $(x,s)$. Its feasible values of $s$ form a down-closed interval. By hypothesis this interval contains positive values and has supremum $\sigma<\infty$, so the program is feasible and bounded with optimum $\sigma$. Its LP dual is
$$\min\Big\{-\textstyle\sum_i y_ib_i:\ y\ge0,\ \sum_iy_ia_i=0,\ \sum_iy_i=1\Big\}.$$
Strong duality (e.g. Schrijver, *Theory of Linear and Integer Programming*, Cor. 7.1g) gives a dual optimum $y$ of value $\sigma$.

The Lean proof instead separates the compact convex image of the standard simplex under $y\mapsto(\sum y_ia_i,-\sum y_ib_i)$ from the ray $\{0\}\times(-\infty,\sigma]$ (`exists_dual`). Both separation outcomes contradict $\sigma=\sup$.

The last identity follows from $\sum_iy_i\ell_i(x)=\langle\sum_iy_ia_i,x\rangle-\sum_iy_ib_i$. $\square$

*Weak duality* ($s\le-\sum y_ib_i$ for every feasible dual $y$ and every $s$ in the shift set) shows that the optimal value is $\sigma$ exactly (`weak_duality`).

**Lemma 2 (minimal support).** Choose $y$ as in Lemma 1 with support $S=\{i:y_i>0\}$ of minimum size. Then:

- (a) the augmented rows $(a_i,1)\in\mathbb R^{n+1}$, $i\in S$, are linearly independent, so $s:=|S|\le n+1$;
- (b) for every nonempty $T\subsetneq S$, $\sum_{j\in T}a_j\neq0$.

*Proof.* (a) Suppose $0\ne z$ is supported in $S$ with $\sum z_ia_i=0$ and $\sum z_i=0$. For small $|\varepsilon|$, $y+\varepsilon z$ is dual feasible. Optimality of $y$ forces $\sum z_ib_i=0$, so every such $y+\varepsilon z$ is optimal. Since $\sum z_i=0$, $z$ has a negative entry. Increasing $\varepsilon$ until the first coordinate in $S$ vanishes gives an optimal certificate of smaller support, a contradiction (`shrink`, `exists_min_cert`, `card_support_le`).

(b) Suppose $\sum_{T}a_j=0$ and pick $k\in S\setminus T$. Put $z=\mathbf 1_T-|T|\,y$. Then $z$ is supported in $S$, $\sum z_ia_i=0$ and $\sum z_i=|T|-|T|=0$, so by (a) $z=0$. That means $y=\mathbf 1_T/|T|$, which contradicts $y_k>0$ (`sum_ne_zero_of_proper`). $\square$

**Lemma 3 (caps).** $y_i\le\sigma$ for every $i$. *Proof.* Pick $v\in V$ with $\ell_i(v)\ge1$. By Lemma 1, $\sigma=\sum_j y_j\ell_j(v)\ge y_i\ell_i(v)\ge y_i$. $\square$

## 4. The heavy rows and the two projection cases

Let $J=\{i\in S: y_i>\sigma/2\}$.

**Lemma 4 (0/1 slacks).** For every $v\in V$, the vector $(\ell_j(v))_{j\in J}$ is either $0$ or a unit vector $e_j$. *Proof.* All terms of $\sum_{j\in J}y_j\ell_j(v)\le\sigma$ are nonnegative. If two indices of $J$ had slack $\ge1$, or one had slack $\ge2$, the sum would exceed $2\cdot\frac\sigma2=\sigma$. $\square$

**Lemma 5 (size).** $|J|+s\ge 2\mu$; hence $|J|\ge2\mu-(n+1)>0$. *Proof.* By Lemma 3 and the definition of $J$,
$$1=\sum_{i\in S}y_i\le |J|\sigma+(s-|J|)\tfrac\sigma2=\tfrac\sigma2(s+|J|).\qquad\square$$

**Choice of $T$.**

- *Case A: $J\ne S$.* Put $T=J$ and $t=|T|$. By Lemma 5, $n-t\le n-2\mu+s\le 2n+1-2\mu$.
- *Case B: $J=S$.* Lemma 5 gives $2s\ge2\mu>n+1\ge2$, so $s\ge2$ and $s\ge\mu$. Fix $k_0\in S$ and put $T=S\setminus\{k_0\}$, $t=s-1\ge1$. Then $n-t=n+1-s\le 2(n+1-\mu)$, because $2\mu\le2s\le s+n+1$.

In both cases $\emptyset\ne T\subsetneq S$, and Lemma 4 still holds for $T\subseteq J$. Moreover
$$k:=n-t\le 2(n+1-\mu).$$

**Lemma 6 (all simplex vertices are hit).**

- There is $v_0\in V$ with $\ell_j(v_0)=0$ for all $j\in T$.
- For each $j\in T$ there is $v_j\in V$ with $(\ell_i(v_j))_{i\in T}=e_j$.

*Proof.* By Lemma 2(b), $c=\sum_{T}a_j\ne0$, so $\langle c,\cdot\rangle$ is not constant on $V$. By Lemma 4, $\sum_{j\in T}\ell_j(v)=\langle c,v\rangle-\sum_Tb_j\in\{0,1\}$ on $V$. A nonconstant function with these values takes the value $0$, which gives $v_0$. For $j\in T$, $\ell_j$ is not constant on $V$ and takes values in $\{0,1\}$, so it takes the value $1$ at some $v_j$. By Lemma 4 the other slacks in $T$ vanish there. $\square$

These lemmas are packaged in Lean as `projection_core`.

## 5. Lattice splitting and the Cayley structure

Let $A:\mathbb Z^n\to\mathbb Z^T$, $A(x)=(\langle a_j,x\rangle)_{j\in T}$, and $c=(b_j)_{j\in T}$. By Lemmas 4 and 6, $A(v)-c\in\{0\}\cup\{e_j:j\in T\}$ for all $v\in V$, and every one of these $t+1$ vertices is attained.

**Section and free kernel.** $A(v_j-v_0)=e_j$, so $\varsigma(e_j)=v_j-v_0$ defines a section $\varsigma:\mathbb Z^T\to\mathbb Z^n$, and $A$ is surjective. Every $x$ decomposes as $x=(x-\varsigma Ax)+\varsigma Ax$, so $\mathbb Z^n=K\oplus\varsigma(\mathbb Z^T)$ with $K=\ker A$. As a subgroup of $\mathbb Z^n$, $K$ is free (PID), and rank additivity gives $\operatorname{rk}K=n-t=k$. Choose $\beta:K\xrightarrow{\ \sim\ }\mathbb Z^k$. Then
$$g:\mathbb Z^n\to\mathbb Z^k\times\mathbb Z^t,\qquad g(x)=(\beta(x-\varsigma Ax),\,Ax)$$
is a $\mathbb Z$-isomorphism with inverse $(u,w)\mapsto\beta^{-1}u+\varsigma w$. Its real extension $g_{\mathbb R}$ is an integral matrix whose inverse is the integral matrix of $g^{-1}$. The reviewer kernel-checked this as `ReviewR2.realExt_mul_symm` / `realExt_symm_mul`, together with $n=k+t$ (`rank_split`).

**Fibres.** Let $\Phi(x)=g_{\mathbb R}(x-v_0)$, an affine lattice isomorphism with integral translation. For $v\in V$,
$$\Phi(v)=\big(p_v,\ A v-A v_0\big)=\big(p_v,\ A(v)-c\big)\in\mathbb Z^k\times\{0,e_j\},$$
because $A(v_0)=c$. For $i\in\{0\}\cup T$ put $Q_i=\{p_v: A(v)-c=e_i\}$ (with $e_0:=0$). Each $Q_i$ is nonempty by Lemma 6. Let $P_i=\operatorname{conv}Q_i\subseteq\mathbb R^k$. Affine maps commute with convex hulls, and $\operatorname{conv}(Q_i\times\{e_i\})=P_i\times\{e_i\}$, so
$$\Phi(P)=\operatorname{conv}\Phi(V)=\operatorname{conv}\bigcup_i(Q_i\times\{e_i\})=\operatorname{conv}\bigcup_i(P_i\times\{e_i\})=P_0*P_{1}*\cdots*P_t .$$
In Lean this is `cayley_of_projection`.

**Conclusion.** $P$ is a Cayley polytope of length $t+1\ge2$ of nonempty lattice polytopes in $\mathbb R^k$. Since $k$ is an integer and $k\le2(n+1-\mu)$, we get $k\le\lfloor2(n+1-\mu)\rfloor$ (`Int.le_floor`). This proves Theorem 1. $\blacksquare$

No use is made of DRHNP Theorem 3.4, of the degree $d(P)$, or of any Cayley-decomposition theorem from the literature.

## 6. Ordinary remarks (not formalized, not part of the formal scope, no credit claimed)

These were rederived by the reviewer by hand; no Lean proof exists for them.

1. **Stronger bound away from $\Delta_n$.** In Case A, $k\le2n+1-2\mu$. In Case B with $s\le n$, $k=n+1-s\le 2n+1-2\mu$, because $2\mu\le2s\le n+s$.

   In Case B with $s=n+1$, take any $v\in V$. By Lemma 4 applied to $J=S$ and $\sum_S y_i\ell_i(v)=\sigma>0$, exactly one slack equals $1$, so $y_i=\sigma$ for the corresponding $i$. Every $i\in S$ occurs (Lemma 3), so all $y_i=\sigma$ and $\mu=n+1$. The map $(\ell_i)_{i\in S\setminus\{k_0\}}$ then sends $V$ onto the vertices of the unimodular simplex in $\mathbb Z^n$, and it is a surjective endomorphism of $\mathbb Z^n$, hence an isomorphism, so $P\cong\Delta_n$.

   Hence, for $P\not\cong\Delta_n$ with $\mu>\frac{n+1}2$: $P$ is a Cayley sum of lattice polytopes in $\mathbb R^k$ with $k\le\lfloor2(n+1-\mu)\rfloor-1$, and length $t+1\ge 2\mu-n$. For $\Delta_n$ the bound is $k=0$.
2. **Width inequality.** $\mu(P)\cdot w(P)\le n+1$, where $w$ is the lattice width. Some $i\in S$ has $y_i\ge1/s\ge1/(n+1)$. Choose $v\in V$ maximizing $\ell_i$; then $\ell_i(v)$ is the width of $P$ in the primitive direction $a_i$, which is $\ge w(P)$. By Lemma 1, $\sigma\ge y_i\ell_i(v)\ge w/(n+1)$. Consequently $\mu>\frac{n+1}2$ forces lattice width one. This is the producer's original first step; their route then finished with DRHNP Theorem 3.4.
3. The Fine variant (GMH $\mu^F$) and the narrower DRHNP Corollary 3.7 variants are **separate**. No formal or priority claim is made for them here.

## 7. Relation to the literature; limits

- DRHNP (arXiv:1105.2415v3 and the *Algebra & Number Theory* final) prove the claimed dimension bound whenever $n>d(P)$ in Theorem 3.4. At $\mu>(n+1)/2$, this covers all odd $n$ and all $\mu\ge(n+2)/2$. In the remaining range, $n$ is even and $(n+1)/2<\mu<(n+2)/2$, so $\lfloor2(n+1-\mu)\rfloor=n$. There the conjecture reduces to a nontrivial Cayley decomposition, equivalent to lattice width one. This is the even-dimensional width-one case posed in DRHNP §3.3 and follows from the width inequality in §6. The direct proof in §§2–5 treats the full range using the heavy-slack projection.
- Garzón Mora–Haase restate the strict Q-codegree conjecture in arXiv:2302.04074v1, Conjecture 1.1. Higashitani's arXiv:1605.00273v2 addresses the different integer-codegree conjecture.
- **Unresolved prior-art boundaries (preserved):**
  - The FU Berlin dissertation of S. Garzón Mora (Refubium) was not read. The exact robots-disallow hold stands, with no retry or alternate recovery.
  - The current public proof registries are still held for qualification.
  - The final reviewer inspected Higashitani arXiv:1605.00273v2. The 2019 journal final remains unread.
  - Whether the minimal-support argument is a routine lattice-normal analogue of LP/Helly inradius–width bounds is not settled.

  Accordingly, no novelty or priority claim is made.
- The final manuscript review confirmed the ordinary proof, native scope and exact Lean appendix.

**References.**

- [DRHNP] S. Di Rocco, C. Haase, B. Nill, A. Paffenholz, *Polyhedral adjunction theory*, Algebra & Number Theory 7 (2013), no. 10; arXiv:1105.2415v3.
- [GMH] S. Garzón Mora, C. Haase, *Fine polyhedral adjunction theory*, arXiv:2302.04074v1.
- [DN] A. Dickenstein, B. Nill, *A simple combinatorial criterion for projective toric manifolds with dual defect*, Math. Res. Lett. 17(3) (2010) 435–448.
- [Hig] A. Higashitani, *Lattice simplices of maximal dimension with a given degree*, Michigan Math. J. 68(1) (2019) 193–210 (preprint arXiv:1605.00273v2 inspected).
- [Sch] A. Schrijver, *Theory of Linear and Integer Programming*, Wiley 1986.
- MathDB 382145 (normalized snapshot record sha256 `13a642594de4b6f0…`).

## 8. Formalization

- **Toolchain:** Lean 4.34.1 (pinned binary sha256 `e8baaa71…`), Mathlib `d13f23b7…` (prebuilt upstream oleans trusted, metadata hashes verified).
- **Endpoints:** `Cayley382145.dickensteinNill_cayley` and `Cayley382145.dickensteinNillCayleyConjecture_holds : DickensteinNillCayleyConjecture`.
- **Axioms:** exactly `propext`, `Classical.choice`, `Quot.sound` for all nine printed roots.
- **Independent replay:** strict extraction from the frozen appendix into empty directories, then a fresh compile and a separate `leanchecker` run per module in dependency order. All nine oleans are bit-identical to the author's.
- **Reviewer audit module:** the separately labeled module `Cayley382145ReviewR2` (not part of Appendix A) adds the barycentre bridge, the unbounded-convention lemma, the real inverse of $g$, $n=k+t$, and an expanded endpoint `dickensteinNill_cayley_expanded`.

### 8.1 Declaration crosswalk

| Paper step | Lean declarations (module:line, Appendix A) |
|---|---|
| §1 primitive, facet normal, $b_a$, $F_a$ | `IsPrimitive` (Defs:32), `facetOffset` (Defs:35), `facetFace` (Defs:39), `IsFacetNormal` (Defs:44) |
| §1 $P^{(s)}$, $\mu$ | `adjointSet` (Defs:49), `qCodegree` (Defs:53) |
| §1 Cayley sum, affine lattice iso, real extension | `cayleyVertex` (Defs:57), `cayleyEmbed` (Defs:62), `realExt` (Defs:66), `IsCayleySumIn` (Defs:73) |
| Theorem 1 (literal statement) | `DickensteinNillCayleyConjecture` (Defs:83), `dickensteinNill_cayley` (Main:15), `dickensteinNillCayleyConjecture_holds` (Main:129) |
| §2 integer offsets; full-dimension nonconstancy | `facetOffset_latticeHull` (Basic:88), `exists_ne_of_full` (Basic:46), `exists_zDot_ne_of_full` (Basic:70), `nonempty_of_full` (Basic:76) |
| Lemma 0 finiteness | `face_sub_of_touch` (Finite:32), `ker_le_of_face` (Finite:72), `prop_of_ker_le` (Finite:110), `eq_of_prop` (Finite:126), `facetNormal_eq_of_touch` (Finite:171), `touchSet` (Finite:216), `facetNormals_finite` (Finite:225) |
| Lemma 1 certificate / weak duality | `shiftSet` (Cert:24), `weak_duality` (Cert:27), `dualMap` (Cert:40), `simplexSet` (Cert:58), `exists_dual` (Cert:92), `IsOptCert` (Cert:210), `exists_opt` (Cert:213) |
| Lemma 2 minimal support (a),(b) | `shrink` (Cert:222), `exists_min_cert` (Cert:287), `card_support_le` (Cert:317), `sum_ne_zero_of_proper` (Cert:362) |
| Lemmas 3–6, Cases A/B | `projection_core` (Projection:28) |
| §5 section, free kernel, fibres, Cayley hull | `zVertex` (Lattice:20), `realExt_mulVec_castPt` (Lattice:40), `cayleyAff` (Lattice:48), `cayley_of_projection` (Lattice:58) |
| §1.1 Remark 3 non-vacuity (unit segment) | `segV` (Sanity:14), `seg_facet_iff` (Sanity:121), `seg_qCodegree` (Sanity:130), `seg_hypothesis` (Sanity:148), `seg_cayley` (Sanity:152) |
| §1.1 Remark 2, §5 (reviewer module, separate) | `ReviewR2.adjoint_barycentre` (ReviewR2:31), `ReviewR2.shiftSet_nonempty` (ReviewR2:63), `ReviewR2.qCodegree_eq_zero_of_unbounded` (ReviewR2:69), `ReviewR2.realExt_mul_symm` (ReviewR2:86), `ReviewR2.realExt_symm_mul` (ReviewR2:91), `ReviewR2.rank_split` (ReviewR2:96), `ReviewR2.dickensteinNill_cayley_expanded` (ReviewR2:101) |

Line numbers refer to the canonical sources in Appendix A. The complete per-declaration index is in [REPLAY-DECLARATIONS-INDEX.json](REPLAY-DECLARATIONS-INDEX.json).

## Appendix A. Exact Lean sources (nine canonical modules, byte-exact, checked dependency order)

Each fenced block below is byte-identical to the frozen author source. Module hashes are recorded in the [replay report](REPLAY-REPORT.md).

### Cayley382145Defs.lean

```lean
import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# MathDB 382145: native definitions and literal statement

Dickenstein–Nill Cayley decomposition conjecture (DRHNP arXiv:1105.2415v3 Conjecture 3 =
Garzón Mora–Haase arXiv:2302.04074v1 Conjecture 1.1). All notions are defined from the
polytope itself: facets are the `(n-1)`-dimensional faces cut out by primitive inward integral
normals, the Q-codegree is the reciprocal of the supremal uniform inward facet shift, and a
Cayley sum is an image under an integral affine lattice isomorphism (with its real extension).
-/

namespace Cayley382145

open scoped Matrix

/-- Pairing of an integral covector with a real point. -/
def intDot {n : ℕ} (a : Fin n → ℤ) (x : Fin n → ℝ) : ℝ := ∑ i, (a i : ℝ) * x i

/-- Coordinatewise cast of a lattice point. -/
def castPt {ι : Type*} (v : ι → ℤ) : ι → ℝ := fun i => (v i : ℝ)

/-- Convex hull of finitely many lattice points (a lattice polytope). -/
def latticeHull {k : ℕ} (V : Finset (Fin k → ℤ)) : Set (Fin k → ℝ) :=
  convexHull ℝ (castPt '' (V : Set (Fin k → ℤ)))

/-- A primitive integral vector: its entries have no common non-unit divisor. -/
def IsPrimitive {n : ℕ} (a : Fin n → ℤ) : Prop := ∀ d : ℤ, (∀ i, d ∣ a i) → IsUnit d

/-- `min_P ⟨a, ·⟩`. -/
noncomputable def facetOffset {n : ℕ} (P : Set (Fin n → ℝ)) (a : Fin n → ℤ) : ℝ :=
  sInf (intDot a '' P)

/-- The face of `P` on which `⟨a, ·⟩` is minimal. -/
def facetFace {n : ℕ} (P : Set (Fin n → ℝ)) (a : Fin n → ℤ) : Set (Fin n → ℝ) :=
  {x | x ∈ P ∧ intDot a x = facetOffset P a}

/-- `a` is the primitive inward normal of an actual facet (a nonempty face of dimension
`n - 1`) of `P`. -/
def IsFacetNormal {n : ℕ} (P : Set (Fin n → ℝ)) (a : Fin n → ℤ) : Prop :=
  IsPrimitive a ∧ (∀ x ∈ P, facetOffset P a ≤ intDot a x) ∧ (facetFace P a).Nonempty ∧
    Module.finrank ℝ (affineSpan ℝ (facetFace P a)).direction = n - 1

/-- The adjoint polytope `P^(s) = {x : ⟨a_F, x⟩ ≥ b_F + s for every facet F}`. -/
def adjointSet {n : ℕ} (P : Set (Fin n → ℝ)) (s : ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ a, IsFacetNormal P a → facetOffset P a + s ≤ intDot a x}

/-- The Q-codegree `μ(P) = (sup {s > 0 : P^(s) ≠ ∅})⁻¹`. -/
noncomputable def qCodegree {n : ℕ} (P : Set (Fin n → ℝ)) : ℝ :=
  (sSup {s : ℝ | 0 < s ∧ (adjointSet P s).Nonempty})⁻¹

/-- Vertices `0, e_1, …, e_t` of the standard simplex in `ℝ^t`. -/
def cayleyVertex {t : ℕ} : Option (Fin t) → Fin t → ℝ
  | none => 0
  | some j => Pi.single j 1

/-- `p ↦ (p, e_i) ∈ ℝ^k × ℝ^t`. -/
def cayleyEmbed {k t : ℕ} (i : Option (Fin t)) (p : Fin k → ℝ) : Fin k ⊕ Fin t → ℝ :=
  Sum.elim p (cayleyVertex i)

/-- Real extension (matrix over `ℝ`) of an integral linear map. -/
noncomputable def realExt {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (g : (ι → ℤ) →ₗ[ℤ] (κ → ℤ)) : Matrix κ ι ℝ :=
  (LinearMap.toMatrix' g).map (Int.cast : ℤ → ℝ)

/-- `P` is a nontrivial Cayley sum `P_0 * ⋯ * P_t` (`t ≥ 1`) of lattice polytopes
`P_i ⊆ ℝ^k`: an affine lattice isomorphism `ℤ^n ≅ ℤ^k × ℤ^t` maps `P` onto
`conv (⋃ i, P_i × {e_i})`. -/
def IsCayleySumIn {n : ℕ} (P : Set (Fin n → ℝ)) (k t : ℕ) : Prop :=
  1 ≤ t ∧ ∃ (g : (Fin n → ℤ) ≃ₗ[ℤ] (Fin k ⊕ Fin t → ℤ)) (z : Fin n → ℤ)
    (Q : Option (Fin t) → Finset (Fin k → ℤ)),
    (∀ i, (Q i).Nonempty) ∧
    (fun x => realExt (g : (Fin n → ℤ) →ₗ[ℤ] (Fin k ⊕ Fin t → ℤ)) *ᵥ (x - castPt z)) '' P =
      convexHull ℝ (⋃ i, cayleyEmbed i '' latticeHull (Q i))

/-- MathDB 382145 (literal): every `n`-dimensional lattice polytope with
`μ(P) > (n+1)/2` is a Cayley sum of lattice polytopes of dimension at most
`⌊2(n+1-μ(P))⌋`. -/
def DickensteinNillCayleyConjecture : Prop :=
  ∀ (n : ℕ) (P : Set (Fin n → ℝ)) (V : Finset (Fin n → ℤ)), P = latticeHull V →
    affineSpan ℝ P = ⊤ → ((n : ℝ) + 1) / 2 < qCodegree P →
    ∃ k t : ℕ, (k : ℤ) ≤ ⌊2 * ((n : ℝ) + 1 - qCodegree P)⌋ ∧ IsCayleySumIn P k t

end Cayley382145
```

### Cayley382145Basic.lean

```lean
import Cayley382145Defs
import Mathlib.Analysis.Convex.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # MathDB 382145: basic facts on integral pairings and lattice hulls -/

namespace Cayley382145

open Finset

variable {n : ℕ}

/-- Integer pairing. -/
def zDot (a v : Fin n → ℤ) : ℤ := ∑ i, a i * v i

/-- Real dot product. -/
def rdot {m : ℕ} (u x : Fin m → ℝ) : ℝ := ∑ k, u k * x k

theorem intDot_eq_rdot (a : Fin n → ℤ) (x : Fin n → ℝ) : intDot a x = rdot (castPt a) x := rfl

theorem intDot_castPt (a v : Fin n → ℤ) : intDot a (castPt v) = (zDot a v : ℝ) := by
  simp [intDot, castPt, zDot]

theorem rdot_sum {ι : Type*} [Fintype ι] (y : ι → ℝ) (α : ι → Fin n → ℝ) (x : Fin n → ℝ) :
    rdot (∑ i, y i • α i) x = ∑ i, y i * rdot (α i) x := by
  simp only [rdot, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm.trans
    (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring)

theorem rdot_zero_left (x : Fin n → ℝ) : rdot 0 x = 0 := by simp [rdot]

/-- `intDot a` as a real linear functional. -/
noncomputable def intDotL (a : Fin n → ℤ) : (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun := intDot a
  map_add' x y := by
    simp only [intDot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [intDot, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

theorem intDotL_apply (a : Fin n → ℤ) (x : Fin n → ℝ) : intDotL a x = intDot a x := rfl

/-- Full dimensionality: no nonzero integral functional is constant on the generators. -/
theorem exists_ne_of_full {V : Finset (Fin n → ℤ)} (hfull : affineSpan ℝ (latticeHull V) = ⊤)
    {c : Fin n → ℤ} (hc : c ≠ 0) (d : ℝ) : ∃ v ∈ V, intDot c (castPt v) ≠ d := by
  by_contra h
  push Not at h
  have hsub : latticeHull V ⊆ {x | intDotL c x = d} := by
    apply convexHull_min _ (convex_hyperplane (intDotL c).isLinear d)
    rintro _ ⟨v, hv, rfl⟩
    exact h v hv
  have hvs : vectorSpan ℝ (latticeHull V) = ⊤ := by
    rw [← direction_affineSpan, hfull, AffineSubspace.direction_top]
  have hle : vectorSpan ℝ (latticeHull V) ≤ LinearMap.ker (intDotL c) := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    have h1 : intDotL c x = d := hsub hx
    have h2 : intDotL c y = d := hsub hy
    simp only [SetLike.mem_coe, LinearMap.mem_ker, vsub_eq_sub, map_sub, h1, h2, sub_self]
  rw [hvs] at hle
  apply hc
  funext i
  have hi := hle (Submodule.mem_top (x := (Pi.single i 1 : Fin n → ℝ)))
  rw [LinearMap.mem_ker, intDotL_apply] at hi
  simp [intDot, Pi.single_apply] at hi
  simpa using hi

theorem exists_zDot_ne_of_full {V : Finset (Fin n → ℤ)} (hfull : affineSpan ℝ (latticeHull V) = ⊤)
    {c : Fin n → ℤ} (hc : c ≠ 0) (d : ℤ) : ∃ v ∈ V, zDot c v ≠ d := by
  obtain ⟨v, hv, hne⟩ := exists_ne_of_full hfull hc (d : ℝ)
  refine ⟨v, hv, fun h => hne ?_⟩
  rw [intDot_castPt, h]

theorem nonempty_of_full {V : Finset (Fin n → ℤ)} (hfull : affineSpan ℝ (latticeHull V) = ⊤) :
    V.Nonempty := by
  rcases V.eq_empty_or_nonempty with h | h
  · subst h
    exfalso
    have hb : affineSpan ℝ (latticeHull (∅ : Finset (Fin n → ℤ))) = ⊥ := by
      simp [latticeHull]
    rw [hb] at hfull
    exact absurd hfull (AffineSubspace.bot_ne_top ℝ (Fin n → ℝ) (Fin n → ℝ))
  · exact h

/-- The facet offset of a lattice hull is the integral minimum over the generators. -/
theorem facetOffset_latticeHull {V : Finset (Fin n → ℤ)} (hV : V.Nonempty) (a : Fin n → ℤ) :
    ∃ v₀ ∈ V, facetOffset (latticeHull V) a = (zDot a v₀ : ℝ) ∧ (∀ v ∈ V, zDot a v₀ ≤ zDot a v) ∧
      ∀ x ∈ latticeHull V, (zDot a v₀ : ℝ) ≤ intDot a x := by
  obtain ⟨v₀, hv₀, hmin⟩ := V.exists_min_image (zDot a) hV
  have hlow : latticeHull V ⊆ {x | (zDot a v₀ : ℝ) ≤ intDotL a x} := by
    apply convexHull_min _ (convex_halfSpace_ge (intDotL a).isLinear _)
    rintro _ ⟨v, hv, rfl⟩
    show (zDot a v₀ : ℝ) ≤ intDot a (castPt v)
    rw [intDot_castPt]
    exact_mod_cast hmin v hv
  have hmem : castPt v₀ ∈ latticeHull V := subset_convexHull ℝ _ ⟨v₀, hv₀, rfl⟩
  refine ⟨v₀, hv₀, ?_, hmin, fun x hx => hlow hx⟩
  apply IsLeast.csInf_eq
  refine ⟨⟨castPt v₀, hmem, intDot_castPt a v₀⟩, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact hlow hx

theorem IsPrimitive.ne_zero {a : Fin n → ℤ} (ha : IsPrimitive a) : a ≠ 0 := by
  rintro rfl
  have h2 := ha 2 (fun _ => dvd_zero 2)
  rw [Int.isUnit_iff] at h2
  omega

theorem IsPrimitive.exists_bezout {a : Fin n → ℤ} (ha : IsPrimitive a) :
    ∃ c : Fin n → ℤ, ∑ i, c i * a i = 1 := by
  have hdvd : ∀ i, Submodule.IsPrincipal.generator (Ideal.span (Set.range a)) ∣ a i := by
    intro i
    rw [← Ideal.mem_span_singleton, Ideal.span_singleton_generator]
    exact Ideal.subset_span ⟨i, rfl⟩
  have htop : Ideal.span (Set.range a) = ⊤ := by
    rw [← Ideal.span_singleton_generator (Ideal.span (Set.range a)), Ideal.span_singleton_eq_top]
    exact ha _ hdvd
  have h1 : (1 : ℤ) ∈ Submodule.span ℤ (Set.range a) := by
    rw [Ideal.submodule_span_eq, htop]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp h1
  exact ⟨c, by simpa [smul_eq_mul] using hc⟩

end Cayley382145
```

### Cayley382145Finite.lean

```lean
import Cayley382145Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # MathDB 382145: the actual facet normals of a full-dimensional lattice hull are finite

Facets are the native `(n-1)`-dimensional faces. Two facet normals touching the same generators
cut out the same face; the dimension condition forces equal kernels, positivity of the ratio
follows from full dimensionality, and primitivity (via Bézout) forces equality. -/

namespace Cayley382145

open Finset

variable {n : ℕ}

theorem facetOffset_le {V : Finset (Fin n → ℤ)} (hV : V.Nonempty) (c : Fin n → ℤ)
    {x : Fin n → ℝ} (hx : x ∈ latticeHull V) : facetOffset (latticeHull V) c ≤ intDot c x := by
  obtain ⟨v₀, -, h1, -, h3⟩ := facetOffset_latticeHull hV c
  rw [h1]
  exact h3 x hx

theorem castPt_mem_latticeHull {V : Finset (Fin n → ℤ)} {v : Fin n → ℤ} (hv : v ∈ V) :
    castPt v ∈ latticeHull V :=
  subset_convexHull ℝ _ ⟨v, hv, rfl⟩

theorem intDot_single (c : Fin n → ℤ) (j : Fin n) : intDot c (Pi.single j 1) = (c j : ℝ) := by
  simp [intDot, Pi.single_apply]

/-- If two normals touch the same generators, the face of the first lies in the facet
hyperplane of the second. -/
theorem face_sub_of_touch {V : Finset (Fin n → ℤ)} (hV : V.Nonempty) {a a' : Fin n → ℤ}
    (htouch : ∀ v ∈ V, (intDot a (castPt v) = facetOffset (latticeHull V) a ↔
      intDot a' (castPt v) = facetOffset (latticeHull V) a'))
    {x : Fin n → ℝ} (hx : x ∈ facetFace (latticeHull V) a) :
    intDot a' x = facetOffset (latticeHull V) a' := by
  obtain ⟨hxP, hxb⟩ := hx
  have hxP' : x ∈ convexHull ℝ ((V.image castPt : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
    rw [Finset.coe_image]
    exact hxP
  obtain ⟨w, hw0, hw1, hwx⟩ := Finset.mem_convexHull'.mp hxP'
  have hlin : ∀ c : Fin n → ℤ, intDot c x = ∑ y ∈ V.image castPt, w y * intDot c y := by
    intro c
    rw [← hwx, ← intDotL_apply, map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [map_smul, smul_eq_mul, intDotL_apply]
  have hlow : ∀ c : Fin n → ℤ, ∀ y ∈ V.image castPt, facetOffset (latticeHull V) c ≤ intDot c y := by
    intro c y hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    exact facetOffset_le hV c (castPt_mem_latticeHull hv)
  have hexp : ∀ c : Fin n → ℤ, intDot c x - facetOffset (latticeHull V) c =
      ∑ y ∈ V.image castPt, w y * (intDot c y - facetOffset (latticeHull V) c) := by
    intro c
    rw [Finset.sum_congr rfl (fun y _ => mul_sub (w y) _ _), Finset.sum_sub_distrib, ← hlin c,
      ← Finset.sum_mul, hw1, one_mul]
  have hsum0 : ∑ y ∈ V.image castPt, w y * (intDot a y - facetOffset (latticeHull V) a) = 0 := by
    rw [← hexp a, hxb, sub_self]
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun y hy =>
    mul_nonneg (hw0 y hy) (sub_nonneg.mpr (hlow a y hy)))).mp hsum0
  have hsum1 : ∑ y ∈ V.image castPt, w y * (intDot a' y - facetOffset (latticeHull V) a') = 0 := by
    apply Finset.sum_eq_zero
    intro y hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    rcases mul_eq_zero.mp (hterm _ hy) with h | h
    · rw [h, zero_mul]
    · rw [(htouch v hv).mp (sub_eq_zero.mp h), sub_self, mul_zero]
  have := hexp a'
  rw [hsum1] at this
  linarith

/-- The dimension condition on a facet forces kernel inclusion. -/
theorem ker_le_of_face {P : Set (Fin n → ℝ)} {a a' : Fin n → ℤ} (ha : a ≠ 0)
    (hdim : Module.finrank ℝ (affineSpan ℝ (facetFace P a)).direction = n - 1)
    (hsub : ∀ x ∈ facetFace P a, intDot a' x = facetOffset P a') :
    LinearMap.ker (intDotL a) ≤ LinearMap.ker (intDotL a') := by
  set E := (affineSpan ℝ (facetFace P a)).direction with hE
  have hEle : E ≤ LinearMap.ker (intDotL a) ⊓ LinearMap.ker (intDotL a') := by
    rw [hE, direction_affineSpan, vectorSpan_def, Submodule.span_le]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    have hx' := hsub x hx
    have hy' := hsub y hy
    have hxa := hx.2
    have hya := hy.2
    simp only [SetLike.mem_coe, Submodule.mem_inf, LinearMap.mem_ker, vsub_eq_sub, map_sub,
      intDotL_apply]
    constructor <;> linarith
  have hrange : Module.finrank ℝ (LinearMap.range (intDotL a)) = 1 := by
    apply le_antisymm
    · calc Module.finrank ℝ (LinearMap.range (intDotL a)) ≤ Module.finrank ℝ ℝ :=
            Submodule.finrank_le _
        _ = 1 := Module.finrank_self ℝ
    · rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero, LinearMap.range_eq_bot]
      intro h0
      obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
      have := LinearMap.congr_fun h0 (Pi.single i 1)
      rw [intDotL_apply, intDot_single, LinearMap.zero_apply] at this
      exact hi (by exact_mod_cast this)
  have hker : Module.finrank ℝ (LinearMap.ker (intDotL a)) = n - 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker (intDotL a)
    rw [hrange, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    omega
  by_contra hnot
  have hlt : LinearMap.ker (intDotL a) ⊓ LinearMap.ker (intDotL a') < LinearMap.ker (intDotL a) :=
    lt_of_le_of_ne inf_le_left (fun h => hnot (inf_eq_left.mp h))
  have h1 := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 := Submodule.finrank_mono hEle
  omega

/-- Kernel inclusion gives proportional integer vectors. -/
theorem prop_of_ker_le {a a' : Fin n → ℤ}
    (hker : LinearMap.ker (intDotL a) ≤ LinearMap.ker (intDotL a')) (i₀ j : Fin n) :
    a i₀ * a' j = a' i₀ * a j := by
  have hx : ((a i₀ : ℝ) • (Pi.single j 1 : Fin n → ℝ) - (a j : ℝ) • Pi.single i₀ 1) ∈
      LinearMap.ker (intDotL a) := by
    rw [LinearMap.mem_ker, map_sub, map_smul, map_smul, intDotL_apply, intDotL_apply,
      intDot_single, intDot_single, smul_eq_mul, smul_eq_mul, mul_comm, sub_self]
  have h := hker hx
  rw [LinearMap.mem_ker, map_sub, map_smul, map_smul, intDotL_apply, intDotL_apply,
    intDot_single, intDot_single, smul_eq_mul, smul_eq_mul, sub_eq_zero] at h
  have h' : ((a i₀ * a' j : ℤ) : ℝ) = ((a' i₀ * a j : ℤ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast h'

/-- Primitive, positively proportional integer vectors are equal. -/
theorem eq_of_prop {a a' : Fin n → ℤ} (ha : IsPrimitive a) (ha' : IsPrimitive a') (i₀ : Fin n)
    (hprop : ∀ j, a i₀ * a' j = a' i₀ * a j) (hpos : 0 < a i₀ * a' i₀) : a = a' := by
  obtain ⟨c, hc⟩ := ha.exists_bezout
  obtain ⟨c', hc'⟩ := ha'.exists_bezout
  set p := a i₀ with hp
  set q := a' i₀ with hq
  have hu : p * (∑ j, c j * a' j) = q := by
    calc p * (∑ j, c j * a' j) = ∑ j, c j * (p * a' j) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ j, c j * (q * a j) := Finset.sum_congr rfl fun j _ => by rw [hprop j]
      _ = q * ∑ j, c j * a j := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ = q := by rw [hc, mul_one]
  have hu' : q * (∑ j, c' j * a j) = p := by
    calc q * (∑ j, c' j * a j) = ∑ j, c' j * (q * a j) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ j, c' j * (p * a' j) := Finset.sum_congr rfl fun j _ => by rw [hprop j]
      _ = p * ∑ j, c' j * a' j := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ = p := by rw [hc', mul_one]
  have hp0 : p ≠ 0 := by
    rintro h0
    rw [h0, zero_mul] at hpos
    exact lt_irrefl 0 hpos
  have huu : (∑ j, c j * a' j) * (∑ j, c' j * a j) = 1 := by
    apply mul_left_cancel₀ hp0
    rw [← mul_assoc, hu, hu', mul_one]
  have hqp : q = p := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one huu with h | h
    · rw [← hu, h, mul_one]
    · exfalso
      rw [h] at hu
      have : p * q = -(p * p) := by rw [← hu]; ring
      nlinarith [mul_self_nonneg p]
  funext j
  have := hprop j
  rw [hqp] at this
  exact (mul_left_cancel₀ hp0 this).symm

theorem zDot_prop {a a' : Fin n → ℤ} (i₀ : Fin n) (hprop : ∀ j, a i₀ * a' j = a' i₀ * a j)
    (v : Fin n → ℤ) : a i₀ * zDot a' v = a' i₀ * zDot a v := by
  simp only [zDot, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [← mul_assoc, hprop j, mul_assoc]

/-- Two facet normals touching the same generators coincide. -/
theorem facetNormal_eq_of_touch {V : Finset (Fin n → ℤ)} (hfull : affineSpan ℝ (latticeHull V) = ⊤)
    {a a' : Fin n → ℤ} (ha : IsFacetNormal (latticeHull V) a) (ha' : IsFacetNormal (latticeHull V) a')
    (htouch : ∀ v ∈ V, (intDot a (castPt v) = facetOffset (latticeHull V) a ↔
      intDot a' (castPt v) = facetOffset (latticeHull V) a')) : a = a' := by
  have hV := nonempty_of_full hfull
  have hane := ha.1.ne_zero
  have hker := ker_le_of_face hane ha.2.2.2 (fun x hx => face_sub_of_touch hV htouch hx)
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hane
  have hprop := prop_of_ker_le hker i₀
  obtain ⟨v₀, hv₀, hoff, hmin, -⟩ := facetOffset_latticeHull hV a
  have htv₀ : intDot a' (castPt v₀) = facetOffset (latticeHull V) a' :=
    (htouch v₀ hv₀).mp (by rw [intDot_castPt, hoff])
  obtain ⟨v₁, hv₁, hne⟩ := exists_zDot_ne_of_full hfull hane (zDot a v₀)
  have hD : 0 < zDot a v₁ - zDot a v₀ := by
    have := hmin v₁ hv₁
    omega
  have hD' : 0 ≤ zDot a' v₁ - zDot a' v₀ := by
    have h1 := facetOffset_le hV a' (castPt_mem_latticeHull hv₁)
    rw [← htv₀, intDot_castPt, intDot_castPt] at h1
    have h2 : zDot a' v₀ ≤ zDot a' v₁ := by exact_mod_cast h1
    omega
  have hrel : a i₀ * (zDot a' v₁ - zDot a' v₀) = a' i₀ * (zDot a v₁ - zDot a v₀) := by
    rw [mul_sub, mul_sub, zDot_prop i₀ hprop, zDot_prop i₀ hprop]
  have hq0 : a' i₀ ≠ 0 := by
    intro hq
    apply ha'.1.ne_zero
    funext j
    have := hprop j
    rw [hq, zero_mul] at this
    exact (mul_eq_zero.mp this).resolve_left hi₀
  have hpq : 0 ≤ a i₀ * a' i₀ := by
    rcases lt_or_ge (a i₀ * a' i₀) 0 with h | h
    · exfalso
      have h1 : a i₀ * a' i₀ * (zDot a v₁ - zDot a v₀) =
          a i₀ * a i₀ * (zDot a' v₁ - zDot a' v₀) := by
        linear_combination (-(a i₀)) * hrel
      have h2 := mul_neg_of_neg_of_pos h hD
      have h3 := mul_nonneg (mul_self_nonneg (a i₀)) hD'
      linarith
    · exact h
  have hpos : 0 < a i₀ * a' i₀ := lt_of_le_of_ne hpq (Ne.symm (mul_ne_zero hi₀ hq0))
  exact eq_of_prop ha.1 ha'.1 i₀ hprop hpos

open Classical in
/-- Generators touched by the facet hyperplane of `a`. -/
noncomputable def touchSet (V : Finset (Fin n → ℤ)) (a : Fin n → ℤ) : Finset (Fin n → ℤ) :=
  V.filter (fun v => intDot a (castPt v) = facetOffset (latticeHull V) a)

theorem mem_touchSet {V : Finset (Fin n → ℤ)} {a v : Fin n → ℤ} :
    v ∈ touchSet V a ↔ v ∈ V ∧ intDot a (castPt v) = facetOffset (latticeHull V) a := by
  unfold touchSet
  exact Finset.mem_filter

/-- The set of actual primitive facet normals of a full-dimensional lattice hull is finite. -/
theorem facetNormals_finite {V : Finset (Fin n → ℤ)} (hfull : affineSpan ℝ (latticeHull V) = ⊤) :
    {a | IsFacetNormal (latticeHull V) a}.Finite := by
  apply Set.Finite.of_finite_image (f := touchSet V)
  · apply V.powerset.finite_toSet.subset
    rintro _ ⟨a, -, rfl⟩
    rw [Finset.mem_coe, Finset.mem_powerset]
    intro v hv
    exact (mem_touchSet.mp hv).1
  · intro a ha a' ha' hφ
    apply facetNormal_eq_of_touch hfull ha ha'
    intro v hv
    have h := Finset.ext_iff.mp hφ v
    rw [mem_touchSet, mem_touchSet] at h
    exact ⟨fun h1 => (h.mp ⟨hv, h1⟩).2, fun h1 => (h.mpr ⟨hv, h1⟩).2⟩

end Cayley382145
```

### Cayley382145Cert.lean

```lean
import Cayley382145Basic
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # MathDB 382145: optimal uniform-shift certificate from a separation argument

For finitely many affine rows `x ↦ ⟨α i, x⟩ - β i` whose uniform-shift set is nonempty and
bounded above with supremum `σ`, we construct `y ≥ 0`, `∑ y = 1`, `∑ y α = 0`,
`∑ y β = -σ` by strictly separating the compact convex image of the standard simplex from
the closed ray `{0} × (-∞, σ]` (geometric Hahn–Banach); weak duality gives equality.
A minimal-support optimal certificate has independent augmented rows. No LP duality
theorem is imported. -/

namespace Cayley382145

open Finset

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- Uniform shifts `s > 0` admitting a point with all row slacks at least `s`. -/
def shiftSet (α : ι → Fin n → ℝ) (β : ι → ℝ) : Set ℝ :=
  {s | 0 < s ∧ ∃ x, ∀ i, β i + s ≤ rdot (α i) x}

theorem weak_duality (α : ι → Fin n → ℝ) (β : ι → ℝ) {y : ι → ℝ} (hy0 : ∀ i, 0 ≤ y i)
    (hy1 : ∑ i, y i = 1) (hya : ∑ i, y i • α i = 0) {s : ℝ} (hs : s ∈ shiftSet α β) :
    s ≤ -∑ i, y i * β i := by
  obtain ⟨-, x, hx⟩ := hs
  have h1 : ∑ i, y i * (β i + s) ≤ ∑ i, y i * rdot (α i) x :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hx i) (hy0 i)
  rw [← rdot_sum, hya, rdot_zero_left] at h1
  have h2 : ∑ i, y i * (β i + s) = ∑ i, y i * β i + s := by
    rw [Finset.sum_congr rfl (fun i _ => mul_add (y i) (β i) s), Finset.sum_add_distrib,
      ← Finset.sum_mul, hy1, one_mul]
  linarith

/-- `y ↦ (∑ y α, -∑ y β)`. -/
noncomputable def dualMap (α : ι → Fin n → ℝ) (β : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] (Fin n → ℝ) × ℝ where
  toFun y := (∑ i, y i • α i, -∑ i, y i * β i)
  map_add' y z := by
    refine Prod.ext ?_ ?_
    · simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, Prod.fst_add]
    · simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, Prod.snd_add, neg_add]
  map_smul' c y := by
    refine Prod.ext ?_ ?_
    · simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Prod.smul_fst, Finset.smul_sum,
        mul_smul]
    · simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Prod.smul_snd, Finset.mul_sum,
        mul_neg, mul_assoc]

theorem rdot_smul_right (c : ℝ) (u x : Fin n → ℝ) : rdot u (c • x) = c * rdot u x := by
  simp only [rdot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The standard simplex in `ℝ^ι` (local definition). -/
def simplexSet (ι : Type*) [Fintype ι] : Set (ι → ℝ) := {y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1}

theorem isCompact_simplexSet : IsCompact (simplexSet ι) := by
  have hdef : simplexSet ι = {y : ι → ℝ | ∀ i, 0 ≤ y i} ∩ {y | ∑ i, y i = 1} := rfl
  apply IsCompact.of_isClosed_subset (isCompact_Icc (a := (0 : ι → ℝ)) (b := 1))
  · rw [hdef]
    apply IsClosed.inter
    · have hI : {y : ι → ℝ | ∀ i, 0 ≤ y i} = ⋂ i, {y : ι → ℝ | 0 ≤ y i} := by
        ext y
        simp
      rw [hI]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    · exact isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
  · rintro y ⟨h0, h1⟩
    refine ⟨fun i => h0 i, fun i => ?_⟩
    show y i ≤ 1
    rw [← h1]
    exact Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)

theorem convex_simplexSet : Convex ℝ (simplexSet ι) := by
  intro y hy z hz a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hy.1 i)) (mul_nonneg hb (hz.1 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum, hy.2, hz.2, mul_one, mul_one, hab]

theorem single_mem_simplexSet [DecidableEq ι] (i : ι) : (Pi.single i 1 : ι → ℝ) ∈ simplexSet ι := by
  refine ⟨fun j => ?_, by simp⟩
  by_cases h : j = i
  · subst h; simp
  · simp [h]

/-- Strong duality inequality via strict separation. -/
theorem exists_dual (α : ι → Fin n → ℝ) (β : ι → ℝ) (hne : (shiftSet α β).Nonempty)
    (hbdd : BddAbove (shiftSet α β)) :
    ∃ y : ι → ℝ, (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1 ∧ ∑ i, y i • α i = 0 ∧
      -∑ i, y i * β i ≤ sSup (shiftSet α β) := by
  classical
  set σ := sSup (shiftSet α β) with hσ
  have hle : ∀ s ∈ shiftSet α β, s ≤ σ := fun s hs => le_csSup hbdd hs
  have hσpos : 0 < σ := by
    obtain ⟨s, hs⟩ := hne
    exact lt_of_lt_of_le hs.1 (hle s hs)
  by_contra hno
  push Not at hno
  have hDc : IsCompact (dualMap α β '' simplexSet ι) :=
    isCompact_simplexSet.image (dualMap α β).continuous_of_finiteDimensional
  have hDv : Convex ℝ (dualMap α β '' simplexSet ι) :=
    convex_simplexSet.linear_image (dualMap α β)
  have hRv : Convex ℝ {p : (Fin n → ℝ) × ℝ | p.1 = 0 ∧ p.2 ≤ σ} := by
    intro p hp q hq a b ha hb hab
    refine ⟨?_, ?_⟩
    · simp [hp.1, hq.1]
    · have h1 := mul_le_mul_of_nonneg_left hp.2 ha
      have h2 := mul_le_mul_of_nonneg_left hq.2 hb
      have h3 : a * σ + b * σ = σ := by rw [← add_mul, hab, one_mul]
      simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      linarith
  have hRc : IsClosed {p : (Fin n → ℝ) × ℝ | p.1 = 0 ∧ p.2 ≤ σ} :=
    (isClosed_eq continuous_fst continuous_const).inter
      (isClosed_le continuous_snd continuous_const)
  have hdisj : Disjoint (dualMap α β '' simplexSet ι) {p : (Fin n → ℝ) × ℝ | p.1 = 0 ∧ p.2 ≤ σ} := by
    rw [Set.disjoint_left]
    rintro _ ⟨y, hy, rfl⟩ ⟨h1, h2⟩
    have h1' : ∑ i, y i • α i = 0 := h1
    have h2' : -∑ i, y i * β i ≤ σ := h2
    exact absurd h2' (not_le.mpr (hno y hy.1 hy.2 h1'))
  obtain ⟨f, u, v, hfD, huv, hfR⟩ := geometric_hahn_banach_compact_closed hDv hDc hRv hRc hdisj
  set lam := f ((0 : Fin n → ℝ), (1 : ℝ)) with hlamdef
  have hf0r : ∀ r : ℝ, f ((0 : Fin n → ℝ), r) = r * lam := by
    intro r
    have : ((0 : Fin n → ℝ), r) = r • ((0 : Fin n → ℝ), (1 : ℝ)) := by simp
    rw [this, map_smul, smul_eq_mul]
  have hR' : ∀ r ≤ σ, v < r * lam := fun r hr => by
    rw [← hf0r]
    exact hfR _ ⟨rfl, hr⟩
  have hlam : lam ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have hr : -(|v| + 1) / lam < 0 := div_neg_of_neg_of_pos (by linarith [abs_nonneg v]) hpos
    have := hR' (-(|v| + 1) / lam) (by linarith)
    rw [div_mul_cancel₀ _ hpos.ne'] at this
    linarith [neg_abs_le v]
  let g : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    (f : (Fin n → ℝ) × ℝ →ₗ[ℝ] ℝ) ∘ₗ LinearMap.inl ℝ (Fin n → ℝ) ℝ
  have hg : ∀ x, g x = f (x, 0) := fun x => rfl
  let w : Fin n → ℝ := fun k => g (fun j => if k = j then 1 else 0)
  have hgw : ∀ x, g x = rdot x w := by
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ g x]
    simp only [rdot, smul_eq_mul, w]
  have hrd : ∀ (c : ℝ) (u' : Fin n → ℝ), rdot u' (c • w) = c * g u' := by
    intro c u'
    rw [rdot_smul_right, hgw]
  have hvert : ∀ i, dualMap α β (Pi.single i 1) = (α i, -β i) := by
    intro i
    refine Prod.ext ?_ ?_
    · show ∑ j, (Pi.single i 1 : ι → ℝ) j • α j = α i
      simp [Pi.single_apply]
    · show -∑ j, (Pi.single i 1 : ι → ℝ) j * β j = -β i
      simp [Pi.single_apply]
  have hfi : ∀ i, g (α i) - β i * lam < u := by
    intro i
    have h := hfD _ ⟨Pi.single i 1, single_mem_simplexSet i, rfl⟩
    rw [hvert] at h
    have hsplit : ((α i, -β i) : (Fin n → ℝ) × ℝ) = (α i, 0) + (0, -β i) := by simp
    rw [hsplit, map_add, hf0r, ← hg] at h
    linarith
  rcases hlam.lt_or_eq with hneg | hzero
  · have hu : u < σ * lam := lt_trans huv (hR' σ le_rfl)
    have hu0 : u < 0 := lt_trans hu (mul_neg_of_pos_of_neg hσpos hneg)
    have hmem : u / lam ∈ shiftSet α β := by
      refine ⟨div_pos_of_neg_of_neg hu0 hneg, lam⁻¹ • w, fun i => ?_⟩
      rw [hrd, ← mul_le_mul_right_of_neg hneg]
      have e1 : lam⁻¹ * g (α i) * lam = g (α i) := by
        rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ hneg.ne, one_mul]
      have e2 : (β i + u / lam) * lam = β i * lam + u := by
        rw [add_mul, div_mul_cancel₀ u hneg.ne]
      rw [e1, e2]
      linarith [hfi i]
    have h1 := hle _ hmem
    have h2 : σ < u / lam := by
      rw [← mul_lt_mul_right_of_neg hneg, div_mul_cancel₀ u hneg.ne]
      exact hu
    linarith
  · have hv0 : v < 0 := by
      have := hR' σ le_rfl
      rw [hzero, mul_zero] at this
      exact this
    have hu0 : u < 0 := lt_trans huv hv0
    have hgi : ∀ i, g (α i) < u := fun i => by
      have := hfi i
      rw [hzero, mul_zero, sub_zero] at this
      exact this
    set B := ∑ i, |β i| with hB
    have hβB : ∀ i, β i ≤ B := fun i =>
      le_trans (le_abs_self _) (Finset.single_le_sum (fun j _ => abs_nonneg (β j)) (Finset.mem_univ i))
    have hB0 : 0 ≤ B := Finset.sum_nonneg fun j _ => abs_nonneg _
    set K := (σ + 1 + B) / (-u) with hK
    have hK0 : 0 ≤ K := div_nonneg (by linarith) (by linarith)
    have hKu : K * (-u) = σ + 1 + B := div_mul_cancel₀ _ (neg_pos.mpr hu0).ne'
    have hmem : σ + 1 ∈ shiftSet α β := by
      refine ⟨by linarith, (-K) • w, fun i => ?_⟩
      rw [hrd]
      have h1 : K * (-u) ≤ K * (-g (α i)) := mul_le_mul_of_nonneg_left (by linarith [hgi i]) hK0
      have h2 := hβB i
      linarith
    have := hle _ hmem
    linarith

/-- Optimal certificates. -/
def IsOptCert (α : ι → Fin n → ℝ) (β : ι → ℝ) (σ : ℝ) (y : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1 ∧ ∑ i, y i • α i = 0 ∧ ∑ i, y i * β i = -σ

theorem exists_opt (α : ι → Fin n → ℝ) (β : ι → ℝ) (hne : (shiftSet α β).Nonempty)
    (hbdd : BddAbove (shiftSet α β)) : ∃ y, IsOptCert α β (sSup (shiftSet α β)) y := by
  obtain ⟨y, h0, h1, h2, h3⟩ := exists_dual α β hne hbdd
  refine ⟨y, h0, h1, h2, ?_⟩
  have h4 : sSup (shiftSet α β) ≤ -∑ i, y i * β i :=
    csSup_le hne fun s hs => weak_duality α β h0 h1 h2 hs
  linarith

/-- Ratio-test support reduction. -/
theorem shrink (α : ι → Fin n → ℝ) (β : ι → ℝ) (hne : (shiftSet α β).Nonempty)
    {y : ι → ℝ} (hy : IsOptCert α β (sSup (shiftSet α β)) y) {z : ι → ℝ}
    (hzs : ∀ i, y i = 0 → z i = 0) (hza : ∑ i, z i • α i = 0) (hz1 : ∑ i, z i = 0) (hz0 : z ≠ 0)
    (hzb : ∑ i, z i * β i ≤ 0) :
    ∃ y', IsOptCert α β (sSup (shiftSet α β)) y' ∧
      (univ.filter (fun i => y' i ≠ 0)).card < (univ.filter (fun i => y i ≠ 0)).card := by
  obtain ⟨hy0, hy1, hya, hyb⟩ := hy
  have hpos : ∃ i, 0 < z i := by
    by_contra h
    push Not at h
    apply hz0
    funext i
    exact (Finset.sum_eq_zero_iff_of_nonpos (fun j _ => h j)).mp hz1 i (Finset.mem_univ i)
  have hPz : (univ.filter (fun i => 0 < z i)).Nonempty := by
    obtain ⟨i, hi⟩ := hpos
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨i₀, hi₀, hmin⟩ := (univ.filter (fun i => 0 < z i)).exists_min_image
    (fun i => y i / z i) hPz
  have hzi₀ : 0 < z i₀ := (Finset.mem_filter.mp hi₀).2
  set ε := y i₀ / z i₀ with hεdef
  have hε : 0 ≤ ε := div_nonneg (hy0 i₀) hzi₀.le
  set y' : ι → ℝ := fun i => y i - ε * z i with hy'def
  have hy'0 : ∀ i, 0 ≤ y' i := by
    intro i
    rcases lt_or_ge 0 (z i) with hz | hz
    · have h1 := hmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hz⟩)
      have h2 : ε * z i ≤ y i := (le_div_iff₀ hz).mp h1
      show 0 ≤ y i - ε * z i
      linarith
    · have h2 : ε * z i ≤ 0 := by nlinarith
      show 0 ≤ y i - ε * z i
      linarith [hy0 i]
  have hy'1 : ∑ i, y' i = 1 := by
    show ∑ i, (y i - ε * z i) = 1
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hz1, mul_zero, sub_zero, hy1]
  have hy'a : ∑ i, y' i • α i = 0 := by
    show ∑ i, (y i - ε * z i) • α i = 0
    simp only [sub_smul, Finset.sum_sub_distrib, mul_smul]
    rw [← Finset.smul_sum, hza, smul_zero, sub_zero, hya]
  have hy'b : ∑ i, y' i * β i = ∑ i, y i * β i - ε * ∑ i, z i * β i := by
    show ∑ i, (y i - ε * z i) * β i = _
    simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc]
    rw [← Finset.mul_sum]
  have hwd : sSup (shiftSet α β) ≤ -∑ i, y' i * β i :=
    csSup_le hne fun s hs => weak_duality α β hy'0 hy'1 hy'a hs
  have hεzb : ε * ∑ i, z i * β i ≤ 0 := by nlinarith
  refine ⟨y', ⟨hy'0, hy'1, hy'a, by linarith⟩, ?_⟩
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨i₀, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, fun h => ?_⟩
      have := hzs i₀ h
      linarith
    · rw [Finset.mem_filter, not_and, not_not]
      intro _
      show y i₀ - y i₀ / z i₀ * z i₀ = 0
      rw [div_mul_cancel₀ _ hzi₀.ne', sub_self]
  · intro i hi
    rw [Finset.mem_filter] at hi ⊢
    refine ⟨Finset.mem_univ _, fun h => hi.2 ?_⟩
    show y i - ε * z i = 0
    rw [h, hzs i h, mul_zero, sub_zero]

/-- A minimal-support optimal certificate with independent augmented rows. -/
theorem exists_min_cert (α : ι → Fin n → ℝ) (β : ι → ℝ) (hne : (shiftSet α β).Nonempty)
    (hbdd : BddAbove (shiftSet α β)) :
    ∃ y, IsOptCert α β (sSup (shiftSet α β)) y ∧
      ∀ z : ι → ℝ, (∀ i, y i = 0 → z i = 0) → ∑ i, z i • α i = 0 → ∑ i, z i = 0 → z = 0 := by
  classical
  have hex : ∃ m, ∃ y, IsOptCert α β (sSup (shiftSet α β)) y ∧
      (univ.filter (fun i => y i ≠ 0)).card = m := by
    obtain ⟨y, hy⟩ := exists_opt α β hne hbdd
    exact ⟨_, y, hy, rfl⟩
  obtain ⟨y, hy, hcard⟩ := Nat.find_spec hex
  refine ⟨y, hy, fun z hzs hza hz1 => ?_⟩
  by_contra hz0
  have key : ∀ z' : ι → ℝ, (∀ i, y i = 0 → z' i = 0) → ∑ i, z' i • α i = 0 → ∑ i, z' i = 0 →
      z' ≠ 0 → ∑ i, z' i * β i ≤ 0 → False := by
    intro z' h1 h2 h3 h4 h5
    obtain ⟨y', hy', hlt⟩ := shrink α β hne hy h1 h2 h3 h4 h5
    have := Nat.find_min' hex ⟨y', hy', rfl⟩
    omega
  rcases le_total (∑ i, z i * β i) 0 with hb | hb
  · exact key z hzs hza hz1 hz0 hb
  · apply key (-z)
    · intro i hi
      simp [hzs i hi]
    · simp [neg_smul, Finset.sum_neg_distrib, hza]
    · simp [Finset.sum_neg_distrib, hz1]
    · exact neg_ne_zero.mpr hz0
    · simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
      linarith

/-- Independent augmented rows: the support has at most `n + 1` elements. -/
theorem card_support_le {y : ι → ℝ} {α : ι → Fin n → ℝ}
    (hind : ∀ z : ι → ℝ, (∀ i, y i = 0 → z i = 0) → ∑ i, z i • α i = 0 → ∑ i, z i = 0 → z = 0) :
    (univ.filter (fun i => y i ≠ 0)).card ≤ n + 1 := by
  classical
  set S := univ.filter (fun i => y i ≠ 0) with hS
  let u : S → (Fin n → ℝ) × ℝ := fun x => (α x, 1)
  have hli : LinearIndependent ℝ u := by
    rw [Fintype.linearIndependent_iff]
    intro g hg x
    let z : ι → ℝ := fun i => if h : i ∈ S then g ⟨i, h⟩ else 0
    have hz : ∀ F : ι → (Fin n → ℝ) × ℝ, ∑ i, z i • F i = ∑ x : S, g x • F x := by
      intro F
      rw [← Finset.sum_subset (Finset.subset_univ S)
        (fun i _ hi => by simp [z, hi]), ← Finset.sum_coe_sort S]
      exact Finset.sum_congr rfl fun x _ => by simp [z, x.2]
    have h0 : ∑ i, z i • ((α i, 1) : (Fin n → ℝ) × ℝ) = 0 := by
      rw [hz]
      exact hg
    have h1 : ∑ i, z i • α i = 0 := by
      have := congrArg Prod.fst h0
      simpa [Prod.fst_sum] using this
    have h2 : ∑ i, z i = 0 := by
      have := congrArg Prod.snd h0
      simpa [Prod.snd_sum] using this
    have hzs : ∀ i, y i = 0 → z i = 0 := by
      intro i hi
      have hiS : i ∉ S := by
        rw [hS, Finset.mem_filter]
        exact fun h => h.2 hi
      simp [z, hiS]
    have hzero := congrFun (hind z hzs h1 h2) x
    simpa [z, x.2] using hzero
  have := hli.fintype_card_le_finrank
  rw [Fintype.card_coe, Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
    Module.finrank_self] at this
  exact this

theorem sum_ite_mem_univ {M : Type*} [AddCommMonoid M] (J : Finset ι) (f : ι → M)
    [DecidablePred (· ∈ J)] : ∑ i, (if i ∈ J then f i else 0) = ∑ i ∈ J, f i := by
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

/-- A nonempty proper subset of the support has a nonzero row sum. -/
theorem sum_ne_zero_of_proper {y : ι → ℝ} {α : ι → Fin n → ℝ}
    (hind : ∀ z : ι → ℝ, (∀ i, y i = 0 → z i = 0) → ∑ i, z i • α i = 0 → ∑ i, z i = 0 → z = 0)
    (hy1 : ∑ i, y i = 1) (hya : ∑ i, y i • α i = 0)
    {J : Finset ι} (hJ : ∀ j ∈ J, y j ≠ 0) (hJne : J.Nonempty) {k : ι} (hk : y k ≠ 0)
    (hkJ : k ∉ J) : ∑ j ∈ J, α j ≠ 0 := by
  classical
  intro h
  let z : ι → ℝ := fun i => (if i ∈ J then 1 else 0) - (J.card : ℝ) * y i
  have hzs : ∀ i, y i = 0 → z i = 0 := by
    intro i hi
    have : i ∉ J := fun hiJ => hJ i hiJ hi
    simp [z, this, hi]
  have hza : ∑ i, z i • α i = 0 := by
    simp only [z, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul, mul_smul]
    rw [← Finset.smul_sum, hya, smul_zero, sub_zero, sum_ite_mem_univ, h]
  have hz1 : ∑ i, z i = 0 := by
    simp only [z, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, hy1, mul_one, sum_ite_mem_univ, Finset.sum_const, nsmul_eq_mul, mul_one,
      sub_self]
  have hk0 := congrFun (hind z hzs hza hz1) k
  have hzk : z k = -((J.card : ℝ) * y k) := by simp [z, hkJ]
  rw [hzk, Pi.zero_apply, neg_eq_zero] at hk0
  rcases mul_eq_zero.mp hk0 with h1 | h1
  · exact hJne.ne_empty (Finset.card_eq_zero.mp (by exact_mod_cast h1))
  · exact hk h1

end Cayley382145
```

### Cayley382145Projection.lean

```lean
import Cayley382145Cert

/-! # MathDB 382145: heavy-row selection and the standard-simplex projection data

From an optimal minimal-support certificate (`∑ y_i ℓ_i ≡ σ` on the generators) we select a
nonempty proper subset `J` of the support consisting of heavy rows (`y_j > σ/2`). Integer slacks
of these rows on every generator are `0` or `1` with at most one `1`; every row of `J` attains
`1` and some generator has all `J`-slacks `0`. The count gives `n - |J| ≤ 2(n+1-μ)`. -/

namespace Cayley382145

open Finset

variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem zDot_sum (J : Finset ι) (a : ι → Fin n → ℤ) (v : Fin n → ℤ) :
    zDot (∑ j ∈ J, a j) v = ∑ j ∈ J, zDot (a j) v := by
  simp only [zDot, Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

omit [Fintype ι] [DecidableEq ι] in
theorem castPt_sum (J : Finset ι) (a : ι → Fin n → ℤ) :
    castPt (∑ j ∈ J, a j) = ∑ j ∈ J, castPt (a j) := by
  funext k
  simp [castPt, Finset.sum_apply]

theorem projection_core (a : ι → Fin n → ℤ) (β : ι → ℤ) (V : Finset (Fin n → ℤ)) (y : ι → ℝ)
    (σ : ℝ) (hσ : 0 < σ) (hy0 : ∀ i, 0 ≤ y i) (hy1 : ∑ i, y i = 1)
    (hya : ∑ i, y i • castPt (a i) = 0)
    (hind : ∀ z : ι → ℝ, (∀ i, y i = 0 → z i = 0) → ∑ i, z i • castPt (a i) = 0 →
      ∑ i, z i = 0 → z = 0)
    (hnn : ∀ i, ∀ v ∈ V, β i ≤ zDot (a i) v)
    (hsum : ∀ v ∈ V, ∑ i, y i * ((zDot (a i) v - β i : ℤ) : ℝ) = σ)
    (hfull : ∀ c : Fin n → ℤ, c ≠ 0 → ∀ d : ℤ, ∃ v ∈ V, zDot c v ≠ d)
    (hprim : ∀ i, a i ≠ 0) (hμ : ((n : ℝ) + 1) / 2 < σ⁻¹) :
    ∃ J : Finset ι, J.Nonempty ∧ ((n : ℝ) - J.card ≤ 2 * ((n : ℝ) + 1 - σ⁻¹)) ∧
      (∀ v ∈ V, ∀ j ∈ J, zDot (a j) v - β j = 0 ∨ zDot (a j) v - β j = 1) ∧
      (∀ v ∈ V, ∀ j ∈ J, ∀ j' ∈ J, zDot (a j) v - β j = 1 → zDot (a j') v - β j' = 1 → j = j') ∧
      (∃ v ∈ V, ∀ j ∈ J, zDot (a j) v - β j = 0) ∧
      (∀ j ∈ J, ∃ v ∈ V, zDot (a j) v - β j = 1) := by
  have hLnn : ∀ i, ∀ v ∈ V, (0 : ℝ) ≤ ((zDot (a i) v - β i : ℤ) : ℝ) := fun i v hv => by
    have := hnn i v hv
    exact_mod_cast (show (0 : ℤ) ≤ zDot (a i) v - β i by omega)
  have hpart : ∀ v ∈ V, ∀ T : Finset ι, ∑ i ∈ T, y i * ((zDot (a i) v - β i : ℤ) : ℝ) ≤ σ := by
    intro v hv T
    rw [← hsum v hv]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
      (fun i _ _ => mul_nonneg (hy0 i) (hLnn i v hv))
  have hcap : ∀ i, y i ≤ σ := by
    intro i
    obtain ⟨v, hv, hne⟩ := hfull (a i) (hprim i) (β i)
    have h1 : (1 : ℝ) ≤ ((zDot (a i) v - β i : ℤ) : ℝ) := by
      have := hnn i v hv
      exact_mod_cast (show (1 : ℤ) ≤ zDot (a i) v - β i by omega)
    have h2 := hpart v hv {i}
    rw [Finset.sum_singleton] at h2
    have h3 := mul_le_mul_of_nonneg_left h1 (hy0 i)
    linarith
  have hσn : σ * (((n : ℝ) + 1) / 2) < 1 := by
    have := mul_lt_mul_of_pos_left hμ hσ
    rwa [mul_inv_cancel₀ hσ.ne'] at this
  set S := univ.filter (fun i => y i ≠ 0) with hS
  set H := univ.filter (fun i => σ / 2 < y i) with hH
  have hmemS : ∀ i, i ∈ S ↔ y i ≠ 0 := fun i => by simp [hS]
  have hmemH : ∀ i, i ∈ H ↔ σ / 2 < y i := fun i => by simp [hH]
  have hsle : (S.card : ℝ) ≤ n + 1 := by exact_mod_cast card_support_le hind
  have hHS : H ⊆ S := fun i hi => (hmemS i).mpr (by
    have := (hmemH i).mp hi
    intro h
    rw [h] at this
    linarith)
  have hySum : ∑ i ∈ S, y i = 1 := by
    rw [hS, Finset.sum_filter_ne_zero]
    exact hy1
  have hsumH : ∑ i ∈ H, y i ≤ σ * H.card := by
    calc ∑ i ∈ H, y i ≤ ∑ _i ∈ H, σ := Finset.sum_le_sum fun i _ => hcap i
      _ = σ * H.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hsumSH : ∑ i ∈ S \ H, y i ≤ σ / 2 * (S \ H).card := by
    calc ∑ i ∈ S \ H, y i ≤ ∑ _i ∈ S \ H, σ / 2 := Finset.sum_le_sum fun i hi => by
          have h := (Finset.mem_sdiff.mp hi).2
          rw [hmemH] at h
          exact le_of_not_gt h
      _ = σ / 2 * (S \ H).card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hcardSH : ((S \ H).card : ℝ) + H.card = S.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hHS
  have hbound : 2 ≤ σ * (S.card + H.card) := by
    have h := Finset.sum_sdiff hHS (f := y)
    rw [hySum] at h
    have e : ((S \ H).card : ℝ) = S.card - H.card := by linarith
    rw [e] at hsumSH
    nlinarith
  have hSne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, Finset.sum_empty] at hySum
    exact zero_ne_one hySum
  obtain ⟨J, hJH, hJne, k, hkS, hkJ, hJbound⟩ : ∃ J : Finset ι, J ⊆ H ∧ J.Nonempty ∧
      ∃ k, k ∈ S ∧ k ∉ J ∧ ((n : ℝ) - J.card ≤ 2 * ((n : ℝ) + 1 - σ⁻¹)) := by
    by_cases hEq : H = S
    · obtain ⟨k, hk⟩ := hSne
      refine ⟨S.erase k, ?_, ?_, k, hk, fun h => (Finset.mem_erase.mp h).1 rfl, ?_⟩
      · rw [hEq]
        exact Finset.erase_subset k S
      · by_contra hne
        rw [Finset.not_nonempty_iff_eq_empty] at hne
        have hsingle : ∀ i, i ≠ k → y i = 0 := by
          intro i hik
          by_contra hy
          have hmem : i ∈ S.erase k := Finset.mem_erase.mpr ⟨hik, (hmemS i).mpr hy⟩
          rw [hne] at hmem
          simp at hmem
        have h1 : ∑ i, y i = y k := Fintype.sum_eq_single k hsingle
        have h2 : ∑ i, y i • castPt (a i) = y k • castPt (a k) :=
          Fintype.sum_eq_single k (fun i hik => by rw [hsingle i hik, zero_smul])
        rw [hy1] at h1
        rw [hya, ← h1, one_smul] at h2
        apply hprim k
        funext j
        have hj := congrFun h2 j
        simp only [Pi.zero_apply, castPt] at hj
        show a k j = 0
        exact_mod_cast hj.symm
      · have hcardS : ((S.erase k).card : ℝ) + 1 = S.card := by
          exact_mod_cast Finset.card_erase_add_one hk
        have hμs : σ⁻¹ ≤ S.card := by
          have h1 : 1 ≤ σ * S.card := by
            calc (1 : ℝ) = ∑ i ∈ S, y i := hySum.symm
              _ ≤ ∑ _i ∈ S, σ := Finset.sum_le_sum fun i _ => hcap i
              _ = σ * S.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
          calc σ⁻¹ = σ⁻¹ * 1 := (mul_one _).symm
            _ ≤ σ⁻¹ * (σ * S.card) := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hσ.le)
            _ = S.card := by rw [← mul_assoc, inv_mul_cancel₀ hσ.ne', one_mul]
        linarith
    · have hHne : H.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h
        rw [h, Finset.card_empty, Nat.cast_zero, add_zero] at hbound
        have : σ * S.card ≤ σ * (n + 1) := mul_le_mul_of_nonneg_left hsle hσ.le
        nlinarith
      obtain ⟨k, hkS, hkH⟩ : ∃ k, k ∈ S ∧ k ∉ H := by
        by_contra hno
        push Not at hno
        exact hEq (Finset.Subset.antisymm hHS (fun i hi => hno i hi))
      refine ⟨H, subset_refl _, hHne, k, hkS, hkH, ?_⟩
      have h2 : 2 * σ⁻¹ ≤ S.card + H.card := by
        calc 2 * σ⁻¹ = σ⁻¹ * 2 := mul_comm _ _
          _ ≤ σ⁻¹ * (σ * (S.card + H.card)) :=
              mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hσ.le)
          _ = S.card + H.card := by rw [← mul_assoc, inv_mul_cancel₀ hσ.ne', one_mul]
      linarith
  have hJheavy : ∀ j ∈ J, σ / 2 < y j := fun j hj => (hmemH j).mp (hJH hj)
  have hJS : ∀ j ∈ J, y j ≠ 0 := fun j hj => (hmemS j).mp (hHS (hJH hj))
  have hle1 : ∀ v ∈ V, ∀ j ∈ J, zDot (a j) v - β j ≤ 1 := by
    intro v hv j hj
    by_contra h
    push Not at h
    have h2 : (2 : ℝ) ≤ ((zDot (a j) v - β j : ℤ) : ℝ) := by
      exact_mod_cast (show (2 : ℤ) ≤ zDot (a j) v - β j by omega)
    have h3 := hpart v hv {j}
    rw [Finset.sum_singleton] at h3
    have h4 := mul_le_mul_of_nonneg_left h2 (hy0 j)
    have h5 := hJheavy j hj
    linarith
  have h01 : ∀ v ∈ V, ∀ j ∈ J, zDot (a j) v - β j = 0 ∨ zDot (a j) v - β j = 1 := by
    intro v hv j hj
    have h1 := hle1 v hv j hj
    have h2 := hnn j v hv
    omega
  have hone : ∀ v ∈ V, ∀ j ∈ J, ∀ j' ∈ J, zDot (a j) v - β j = 1 → zDot (a j') v - β j' = 1 →
      j = j' := by
    intro v hv j hj j' hj' h1 h1'
    by_contra hne
    have h3 := hpart v hv {j, j'}
    rw [Finset.sum_pair hne, h1, h1', Int.cast_one, mul_one, mul_one] at h3
    have h4 := hJheavy j hj
    have h5 := hJheavy j' hj'
    linarith
  have hhit : ∀ j ∈ J, ∃ v ∈ V, zDot (a j) v - β j = 1 := by
    intro j hj
    obtain ⟨v, hv, hne⟩ := hfull (a j) (hprim j) (β j)
    refine ⟨v, hv, ?_⟩
    rcases h01 v hv j hj with h | h
    · exact absurd (by omega) hne
    · exact h
  have hzero : ∃ v ∈ V, ∀ j ∈ J, zDot (a j) v - β j = 0 := by
    have hc : ∑ j ∈ J, a j ≠ 0 := by
      intro h
      apply sum_ne_zero_of_proper hind hy1 hya hJS hJne ((hmemS k).mp hkS) hkJ
      rw [← castPt_sum, h]
      funext x
      simp [castPt]
    obtain ⟨v, hv, hne⟩ := hfull _ hc (∑ j ∈ J, β j + 1)
    refine ⟨v, hv, fun j hj => ?_⟩
    by_contra hj0
    have hj1 : zDot (a j) v - β j = 1 := (h01 v hv j hj).resolve_left hj0
    have hsumJ : ∑ i ∈ J, (zDot (a i) v - β i) = 1 := by
      rw [Finset.sum_eq_single_of_mem j hj]
      · exact hj1
      · intro i hi hij
        rcases h01 v hv i hi with h | h
        · exact h
        · exact absurd (hone v hv i hi j hj h hj1) hij
    apply hne
    rw [zDot_sum]
    rw [Finset.sum_sub_distrib] at hsumJ
    omega
  exact ⟨J, hJne, hJbound, h01, hone, hzero, hhit⟩

end Cayley382145
```

### Cayley382145Lattice.lean

```lean
import Cayley382145Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod

/-! # MathDB 382145: integral splitting and the Cayley identification

If an integral affine map `L = A(·) - c : ℤ^n → ℤ^t` sends every generator to a vertex of the
standard simplex and hits every vertex, then `A(v_j - v_0) = e_j` gives a section, the kernel
has a `ℤ`-basis (PID), `ℤ^n ≅ ℤ^r × ℤ^t` with `r + t = n`, and the real extension maps the
lattice hull onto `conv ⋃ (P_i × {e_i})`, `P_i` the hull of the projected fibre generators. -/

namespace Cayley382145

open Finset
open scoped Matrix

/-- Integral standard-simplex vertices. -/
def zVertex {t : ℕ} : Option (Fin t) → Fin t → ℤ
  | none => 0
  | some j => Pi.single j 1

theorem castPt_zVertex {t : ℕ} (i : Option (Fin t)) : castPt (zVertex i) = cayleyVertex i := by
  cases i with
  | none =>
    funext j
    simp [zVertex, cayleyVertex, castPt]
  | some j =>
    funext j'
    by_cases h : j' = j
    · subst h
      simp [zVertex, cayleyVertex, castPt]
    · simp [zVertex, cayleyVertex, castPt, h]

theorem castPt_sub {ι : Type*} (v w : ι → ℤ) : castPt (v - w) = castPt v - castPt w := by
  funext i
  simp [castPt]

theorem realExt_mulVec_castPt {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (g : (ι → ℤ) →ₗ[ℤ] (κ → ℤ)) (p : ι → ℤ) : realExt g *ᵥ castPt p = castPt (g p) := by
  funext k
  have h := RingHom.map_mulVec (Int.castRingHom ℝ) (LinearMap.toMatrix' g) p k
  rw [LinearMap.toMatrix'_mulVec] at h
  exact h.symm

/-- `p ↦ (p, e_i)` as a real affine map. -/
noncomputable def cayleyAff {k t : ℕ} (i : Option (Fin t)) : (Fin k → ℝ) →ᵃ[ℝ] (Fin k ⊕ Fin t → ℝ) where
  toFun := cayleyEmbed i
  linear := LinearMap.pi (Sum.elim (fun m : Fin k => (LinearMap.proj m : (Fin k → ℝ) →ₗ[ℝ] ℝ))
    (fun _ : Fin t => (0 : (Fin k → ℝ) →ₗ[ℝ] ℝ)))
  map_vadd' p w := by
    funext s
    cases s with
    | inl m => simp [cayleyEmbed, vadd_eq_add, LinearMap.pi_apply]
    | inr j => simp [cayleyEmbed, vadd_eq_add, LinearMap.pi_apply]

theorem cayley_of_projection {n t : ℕ} (V : Finset (Fin n → ℤ)) (A : (Fin n → ℤ) →ₗ[ℤ] (Fin t → ℤ))
    (c : Fin t → ℤ) (ht : 1 ≤ t)
    (himg : ∀ v ∈ V, ∃ i : Option (Fin t), A v - c = zVertex i)
    (hhit : ∀ i : Option (Fin t), ∃ v ∈ V, A v - c = zVertex i) :
    ∃ k, k + t = n ∧ IsCayleySumIn (latticeHull V) k t := by
  classical
  obtain ⟨v₀, hv₀, h₀⟩ := hhit none
  have hAv₀ : A v₀ = c := by
    have h := h₀
    simp only [zVertex] at h
    exact sub_eq_zero.mp h
  choose vj hvj hvjA using fun j : Fin t => hhit (some j)
  have hAdiff : ∀ j, A (vj j - v₀) = Pi.single j 1 := by
    intro j
    have h1 := hvjA j
    simp only [zVertex] at h1
    rw [map_sub, hAv₀, h1]
  let sec : (Fin t → ℤ) →ₗ[ℤ] (Fin n → ℤ) :=
    { toFun := fun γ => ∑ j, γ j • (vj j - v₀)
      map_add' := fun γ δ => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r γ => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply] }
  have hAsec : ∀ γ, A (sec γ) = γ := by
    intro γ
    show A (∑ j, γ j • (vj j - v₀)) = γ
    rw [map_sum]
    have hterm : ∀ j, A (γ j • (vj j - v₀)) = γ j • Pi.single j 1 := fun j => by
      rw [← hAdiff j]
      exact A.map_smul (γ j) (vj j - v₀)
    simp only [hterm]
    funext m
    rw [Finset.sum_apply, Finset.sum_eq_single m]
    · simp
    · intro j _ hjm
      simp [Ne.symm hjm]
    · intro h
      exact absurd (Finset.mem_univ m) h
  let e₁ : (Fin n → ℤ) ≃ₗ[ℤ] LinearMap.ker A × (Fin t → ℤ) :=
    { toFun := fun x => (⟨x - sec (A x), by rw [LinearMap.mem_ker, map_sub, hAsec, sub_self]⟩, A x)
      map_add' := fun x y => by
        refine Prod.ext (Subtype.ext ?_) ?_
        · simp only [map_add, Prod.fst_add, Submodule.coe_add]
          abel
        · simp only [map_add, Prod.snd_add]
      map_smul' := fun r x => by
        refine Prod.ext (Subtype.ext ?_) ?_
        · simp only [map_smul, Prod.smul_fst, SetLike.val_smul, RingHom.id_apply, smul_sub]
        · simp only [map_smul, Prod.smul_snd, RingHom.id_apply]
      invFun := fun p => (p.1 : Fin n → ℤ) + sec p.2
      left_inv := fun x => by simp only [sub_add_cancel]
      right_inv := fun p => by
        obtain ⟨⟨k, hk⟩, γ⟩ := p
        have hk' : A k = 0 := hk
        refine Prod.ext (Subtype.ext ?_) ?_
        · simp only [map_add, hk', zero_add, hAsec, add_sub_cancel_right]
        · simp only [map_add, hk', zero_add, hAsec] }
  obtain ⟨r, ⟨bK⟩⟩ := Submodule.nonempty_basis_of_pid (Pi.basisFun ℤ (Fin n)) (LinearMap.ker A)
  let g : (Fin n → ℤ) ≃ₗ[ℤ] (Fin r ⊕ Fin t → ℤ) :=
    e₁.trans ((bK.equivFun.prodCongr (LinearEquiv.refl ℤ (Fin t → ℤ))).trans
      (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin t) ℤ ℤ).symm)
  have hg_inr : ∀ x j, g x (Sum.inr j) = A x j := by
    intro x j
    simp only [g, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
      LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr, LinearEquiv.refl_apply]
    rfl
  have hrank : r + t = n := by
    have h := LinearEquiv.finrank_eq g
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin, Fintype.card_fin] at h
    omega
  let α : (Fin n → ℤ) → Fin r → ℤ := fun v m => g (v - v₀) (Sum.inl m)
  have hgv : ∀ v (i : Option (Fin t)), A v - c = zVertex i →
      castPt (g (v - v₀)) = cayleyEmbed i (castPt (α v)) := by
    intro v i hvi
    funext s
    cases s with
    | inl m => rfl
    | inr j =>
      have e1 : A (v - v₀) = zVertex i := by rw [map_sub, hAv₀, hvi]
      show ((g (v - v₀) (Sum.inr j) : ℤ) : ℝ) = cayleyVertex i j
      rw [hg_inr, e1, ← castPt_zVertex]
      rfl
  let Q : Option (Fin t) → Finset (Fin r → ℤ) := fun i =>
    (V.filter (fun v => A v - c = zVertex i)).image α
  have hQne : ∀ i, (Q i).Nonempty := by
    intro i
    obtain ⟨v, hv, hvi⟩ := hhit i
    exact ⟨α v, Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, hvi⟩, rfl⟩⟩
  let M := realExt (g : (Fin n → ℤ) →ₗ[ℤ] (Fin r ⊕ Fin t → ℤ))
  let φA : (Fin n → ℝ) →ᵃ[ℝ] (Fin r ⊕ Fin t → ℝ) :=
    { toFun := fun x => M *ᵥ (x - castPt v₀)
      linear := Matrix.toLin' M
      map_vadd' := fun p w => by
        show M *ᵥ (w + p - castPt v₀) = Matrix.toLin' M w + M *ᵥ (p - castPt v₀)
        rw [add_sub_assoc, Matrix.mulVec_add, Matrix.toLin'_apply] }
  have hφv : ∀ v, φA (castPt v) = castPt (g (v - v₀)) := by
    intro v
    show realExt (g : (Fin n → ℤ) →ₗ[ℤ] (Fin r ⊕ Fin t → ℤ)) *ᵥ (castPt v - castPt v₀) = _
    rw [← castPt_sub]
    exact realExt_mulVec_castPt (g : (Fin n → ℤ) →ₗ[ℤ] (Fin r ⊕ Fin t → ℤ)) (v - v₀)
  refine ⟨r, hrank, ht, g, v₀, Q, hQne, ?_⟩
  show φA '' latticeHull V = _
  rw [latticeHull, AffineMap.image_convexHull]
  apply Set.Subset.antisymm
  · apply convexHull_mono
    rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    obtain ⟨i, hvi⟩ := himg v hv
    refine Set.mem_iUnion.mpr ⟨i, castPt (α v), subset_convexHull ℝ _ ⟨α v, ?_, rfl⟩, ?_⟩
    · exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, hvi⟩, rfl⟩)
    · rw [hφv, hgv v i hvi]
  · apply convexHull_min _ (convex_convexHull ℝ _)
    refine Set.iUnion_subset fun i => ?_
    have hc : cayleyEmbed i '' latticeHull (Q i) = cayleyAff i '' latticeHull (Q i) := rfl
    rw [hc, latticeHull, AffineMap.image_convexHull]
    apply convexHull_mono
    rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    obtain ⟨v, hvf, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hv, hvi⟩ := Finset.mem_filter.mp hvf
    refine ⟨castPt v, ⟨v, hv, rfl⟩, ?_⟩
    rw [hφv, hgv v i hvi]
    rfl

end Cayley382145
```

### Cayley382145Main.lean

```lean
import Cayley382145Finite
import Cayley382145Projection
import Cayley382145Lattice

/-! # MathDB 382145: the Dickenstein–Nill Cayley decomposition conjecture (literal endpoint)

`dickensteinNill_cayley`: for every `n` and every full-dimensional lattice polytope
`P = conv V ⊆ ℝ^n` with native Q-codegree `μ(P) > (n+1)/2`, `P` is a nontrivial Cayley sum of
lattice polytopes in `ℝ^k` with `k ≤ ⌊2(n+1-μ(P))⌋`. No external Cayley theorem is assumed. -/

namespace Cayley382145

open Finset

theorem dickensteinNill_cayley (n : ℕ) (P : Set (Fin n → ℝ)) (V : Finset (Fin n → ℤ))
    (hP : P = latticeHull V) (hfull : affineSpan ℝ P = ⊤)
    (hμ : ((n : ℝ) + 1) / 2 < qCodegree P) :
    ∃ k t : ℕ, (k : ℤ) ≤ ⌊2 * ((n : ℝ) + 1 - qCodegree P)⌋ ∧ IsCayleySumIn P k t := by
  subst hP
  classical
  have hV := nonempty_of_full hfull
  have hfin := facetNormals_finite hfull
  set N := hfin.toFinset with hN
  have hmemN : ∀ a, a ∈ N ↔ IsFacetNormal (latticeHull V) a := fun a => by simp [hN]
  let α : N → Fin n → ℝ := fun i => castPt (i : Fin n → ℤ)
  let βr : N → ℝ := fun i => facetOffset (latticeHull V) (i : Fin n → ℤ)
  have hT : {s : ℝ | 0 < s ∧ (adjointSet (latticeHull V) s).Nonempty} = shiftSet α βr := by
    ext s
    constructor
    · rintro ⟨hs, x, hx⟩
      exact ⟨hs, x, fun i => hx i ((hmemN i).mp i.2)⟩
    · rintro ⟨hs, x, hx⟩
      exact ⟨hs, x, fun a ha => hx ⟨a, (hmemN a).mpr ha⟩⟩
  have hq : qCodegree (latticeHull V) = (sSup (shiftSet α βr))⁻¹ := by
    rw [qCodegree, hT]
  set σ := sSup (shiftSet α βr) with hσdef
  rw [hq] at hμ ⊢
  have hσpos : 0 < σ := by
    have h1 : 0 < σ⁻¹ := lt_of_le_of_lt (by positivity) hμ
    exact inv_pos.mp h1
  have hne : (shiftSet α βr).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [hσdef, h, Real.sSup_empty] at hσpos
    exact lt_irrefl 0 hσpos
  have hbdd : BddAbove (shiftSet α βr) := by
    by_contra h
    rw [hσdef, Real.sSup_of_not_bddAbove h] at hσpos
    exact lt_irrefl 0 hσpos
  obtain ⟨y, ⟨hy0, hy1, hya, hyb⟩, hind⟩ := exists_min_cert α βr hne hbdd
  rw [← hσdef] at hyb
  have hoff : ∀ i : N, ∃ b : ℤ, facetOffset (latticeHull V) (i : Fin n → ℤ) = b ∧
      ∀ v ∈ V, b ≤ zDot (i : Fin n → ℤ) v := by
    intro i
    obtain ⟨v₀, -, h1, h2, -⟩ := facetOffset_latticeHull hV (i : Fin n → ℤ)
    exact ⟨zDot (i : Fin n → ℤ) v₀, h1, h2⟩
  choose βz hβz hβnn using hoff
  have hsum : ∀ v ∈ V, ∑ i, y i * ((zDot (i : Fin n → ℤ) v - βz i : ℤ) : ℝ) = σ := by
    intro v _
    have e : ∀ i : N, ((zDot (i : Fin n → ℤ) v - βz i : ℤ) : ℝ) = rdot (α i) (castPt v) - βr i := by
      intro i
      show ((zDot (i : Fin n → ℤ) v - βz i : ℤ) : ℝ) =
        intDot (i : Fin n → ℤ) (castPt v) - facetOffset (latticeHull V) (i : Fin n → ℤ)
      rw [Int.cast_sub, intDot_castPt, hβz i]
    simp only [e, mul_sub, Finset.sum_sub_distrib]
    rw [← rdot_sum, hya, rdot_zero_left, hyb]
    ring
  have hprim : ∀ i : N, (i : Fin n → ℤ) ≠ 0 := fun i => ((hmemN i).mp i.2).1.ne_zero
  obtain ⟨J, hJne, hJbound, h01, hone, hzero, hhitJ⟩ :=
    projection_core (fun i : N => (i : Fin n → ℤ)) βz V y σ hσpos hy0 hy1 hya hind hβnn hsum
      (fun c hc d => exists_zDot_ne_of_full hfull hc d) hprim hμ
  set t := J.card with ht
  let e : Fin t ≃ J := J.equivFin.symm
  let A : (Fin n → ℤ) →ₗ[ℤ] (Fin t → ℤ) :=
    { toFun := fun x j => zDot (((e j : N) : Fin n → ℤ)) x
      map_add' := fun x y => by
        funext j
        simp only [zDot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        funext j
        simp only [zDot, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring }
  let cvec : Fin t → ℤ := fun j => βz (e j)
  have hAv : ∀ v (j : Fin t), (A v - cvec) j = zDot (((e j : N) : Fin n → ℤ)) v - βz (e j) :=
    fun v j => rfl
  have hsome : ∀ v ∈ V, ∀ j₁ : Fin t, zDot (((e j₁ : N) : Fin n → ℤ)) v - βz (e j₁) = 1 →
      A v - cvec = zVertex (some j₁) := by
    intro v hv j₁ h1
    funext j
    rw [hAv]
    by_cases hj : j = j₁
    · subst hj
      simpa [zVertex] using h1
    · have hne' : (e j : N) ≠ (e j₁ : N) := fun h => hj (e.injective (Subtype.ext h))
      rcases h01 v hv (e j) (e j).2 with h0 | h1'
      · simpa [zVertex, hj] using h0
      · exact absurd (hone v hv (e j) (e j).2 (e j₁) (e j₁).2 h1' h1) hne'
  have himg : ∀ v ∈ V, ∃ i : Option (Fin t), A v - cvec = zVertex i := by
    intro v hv
    by_cases hall : ∀ j ∈ J, zDot ((j : N) : Fin n → ℤ) v - βz j = 0
    · refine ⟨none, ?_⟩
      funext j
      rw [hAv]
      exact hall (e j) (e j).2
    · push Not at hall
      obtain ⟨j₀, hj₀, hne⟩ := hall
      have h1 : zDot ((j₀ : N) : Fin n → ℤ) v - βz j₀ = 1 := (h01 v hv j₀ hj₀).resolve_left hne
      refine ⟨some (e.symm ⟨j₀, hj₀⟩), hsome v hv _ ?_⟩
      rw [Equiv.apply_symm_apply]
      exact h1
  have hhitA : ∀ i : Option (Fin t), ∃ v ∈ V, A v - cvec = zVertex i := by
    intro i
    cases i with
    | none =>
      obtain ⟨v, hv, hv0⟩ := hzero
      exact ⟨v, hv, funext fun j => by rw [hAv]; exact hv0 (e j) (e j).2⟩
    | some j₁ =>
      obtain ⟨v, hv, hv1⟩ := hhitJ (e j₁) (e j₁).2
      exact ⟨v, hv, hsome v hv j₁ hv1⟩
  have ht1 : 1 ≤ t := Finset.card_pos.mpr hJne
  obtain ⟨k, hkt, hcay⟩ := cayley_of_projection V A cvec ht1 himg hhitA
  refine ⟨k, t, ?_, hcay⟩
  rw [Int.le_floor]
  have hk : (k : ℝ) + t = n := by exact_mod_cast hkt
  push_cast
  linarith

/-- MathDB 382145 holds in the literal native formulation. -/
theorem dickensteinNillCayleyConjecture_holds : DickensteinNillCayleyConjecture :=
  fun n P V hP hfull hμ => dickensteinNill_cayley n P V hP hfull hμ

end Cayley382145
```

### Cayley382145Sanity.lean

```lean
import Cayley382145Main

/-! # MathDB 382145: non-vacuity check of the native definitions

For the unit segment `[0,1] ⊆ ℝ^1` the actual facet normals are exactly `±1`, the native
Q-codegree evaluates to `2 > (1+1)/2`, and the main theorem applies. This is a sanity witness
only (optional, not part of the endpoint). -/

namespace Cayley382145

open Finset

/-- Generators of the unit segment. -/
def segV : Finset (Fin 1 → ℤ) := {0, fun _ => 1}

/-- The primitive vector `1 ∈ ℤ^1`. -/
def eOne : Fin 1 → ℤ := fun _ => 1

theorem intDot_one (x : Fin 1 → ℝ) : intDot eOne x = x 0 := by simp [intDot, eOne]

theorem intDot_negOne (x : Fin 1 → ℝ) : intDot (-eOne) x = -x 0 := by simp [intDot, eOne]

theorem zero_mem_segV : (0 : Fin 1 → ℤ) ∈ segV := by simp [segV]

theorem eOne_mem_segV : eOne ∈ segV :=
  Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

theorem seg_full : affineSpan ℝ (latticeHull segV) = ⊤ := by
  have h0 : castPt (0 : Fin 1 → ℤ) ∈ latticeHull segV := castPt_mem_latticeHull zero_mem_segV
  have h1 : castPt eOne ∈ latticeHull segV := castPt_mem_latticeHull eOne_mem_segV
  rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ (Fin 1 → ℝ) (Fin 1 → ℝ)
    ⟨_, h0⟩, eq_top_iff]
  intro x _
  have hv : castPt eOne -ᵥ castPt (0 : Fin 1 → ℤ) ∈ vectorSpan ℝ (latticeHull segV) :=
    vsub_mem_vectorSpan (k := ℝ) h1 h0
  have hx : x = x 0 • (castPt eOne -ᵥ castPt (0 : Fin 1 → ℤ)) := by
    funext i
    obtain rfl := Subsingleton.elim i 0
    simp [castPt, eOne]
  rw [hx]
  exact Submodule.smul_mem _ _ hv

theorem primitive_fin_one {a : Fin 1 → ℤ} (ha : IsPrimitive a) : a = eOne ∨ a = -eOne := by
  have hu := ha (a 0) (fun i => by
    obtain rfl := Subsingleton.elim i 0
    exact dvd_rfl)
  rcases Int.isUnit_iff.mp hu with h | h
  · left
    funext i
    obtain rfl := Subsingleton.elim i 0
    simp [eOne, h]
  · right
    funext i
    obtain rfl := Subsingleton.elim i 0
    simp [eOne, h]

theorem primitive_eOne : IsPrimitive eOne := fun _ hd => isUnit_of_dvd_one (hd 0)

theorem primitive_negOne : IsPrimitive (-eOne) := fun _ hd =>
  isUnit_of_dvd_one (dvd_neg.mp (hd 0))

theorem segV_nonempty : segV.Nonempty := ⟨0, zero_mem_segV⟩

theorem seg_offset_one : facetOffset (latticeHull segV) eOne = 0 := by
  obtain ⟨v₀, hv₀, h1, h2, -⟩ := facetOffset_latticeHull segV_nonempty eOne
  rw [h1]
  simp only [segV, Finset.mem_insert, Finset.mem_singleton] at hv₀
  rcases hv₀ with rfl | rfl
  · simp [zDot]
  · have := h2 0 zero_mem_segV
    simp [zDot, eOne] at this

theorem seg_offset_negOne : facetOffset (latticeHull segV) (-eOne) = -1 := by
  obtain ⟨v₀, hv₀, h1, h2, -⟩ := facetOffset_latticeHull segV_nonempty (-eOne)
  rw [h1]
  simp only [segV, Finset.mem_insert, Finset.mem_singleton] at hv₀
  rcases hv₀ with rfl | rfl
  · have := h2 eOne eOne_mem_segV
    simp [zDot, eOne] at this
  · simp [zDot, eOne]

theorem seg_facet_one : IsFacetNormal (latticeHull segV) eOne := by
  refine ⟨primitive_eOne, fun x hx => facetOffset_le segV_nonempty eOne hx,
    ⟨castPt 0, castPt_mem_latticeHull zero_mem_segV, ?_⟩, ?_⟩
  · rw [seg_offset_one, intDot_one]
    simp [castPt]
  · have hsub : facetFace (latticeHull segV) eOne ⊆ {castPt (0 : Fin 1 → ℤ)} := by
      rintro x ⟨_, hx⟩
      rw [seg_offset_one, intDot_one] at hx
      rw [Set.mem_singleton_iff]
      funext i
      obtain rfl := Subsingleton.elim i 0
      simp [castPt, hx]
    have hle := vectorSpan_mono (k := ℝ) hsub
    rw [vectorSpan_singleton] at hle
    have h0 : Module.finrank ℝ (affineSpan ℝ (facetFace (latticeHull segV) eOne)).direction = 0 := by
      rw [direction_affineSpan, le_bot_iff.mp hle, finrank_bot]
    simpa using h0

theorem seg_facet_negOne : IsFacetNormal (latticeHull segV) (-eOne) := by
  refine ⟨primitive_negOne, fun x hx => facetOffset_le segV_nonempty (-eOne) hx,
    ⟨castPt eOne, castPt_mem_latticeHull eOne_mem_segV, ?_⟩, ?_⟩
  · rw [seg_offset_negOne, intDot_negOne]
    simp [castPt, eOne]
  · have hsub : facetFace (latticeHull segV) (-eOne) ⊆ {castPt eOne} := by
      rintro x ⟨_, hx⟩
      rw [seg_offset_negOne, intDot_negOne] at hx
      rw [Set.mem_singleton_iff]
      funext i
      obtain rfl := Subsingleton.elim i 0
      have hx' : x 0 = 1 := by linarith
      simp [castPt, eOne, hx']
    have hle := vectorSpan_mono (k := ℝ) hsub
    rw [vectorSpan_singleton] at hle
    have h0 : Module.finrank ℝ
        (affineSpan ℝ (facetFace (latticeHull segV) (-eOne))).direction = 0 := by
      rw [direction_affineSpan, le_bot_iff.mp hle, finrank_bot]
    simpa using h0

/-- The actual facet normals of the unit segment are exactly `±1`. -/
theorem seg_facet_iff (a : Fin 1 → ℤ) :
    IsFacetNormal (latticeHull segV) a ↔ a = eOne ∨ a = -eOne := by
  constructor
  · exact fun h => primitive_fin_one h.1
  · rintro (rfl | rfl)
    · exact seg_facet_one
    · exact seg_facet_negOne

/-- The native Q-codegree of the unit segment is `2`. -/
theorem seg_qCodegree : qCodegree (latticeHull segV) = 2 := by
  have hT : IsGreatest {s : ℝ | 0 < s ∧ (adjointSet (latticeHull segV) s).Nonempty} (1 / 2) := by
    refine ⟨⟨by norm_num, fun _ => 1 / 2, fun a ha => ?_⟩, ?_⟩
    · rcases (seg_facet_iff a).mp ha with rfl | rfl
      · rw [seg_offset_one, intDot_one]
        norm_num
      · rw [seg_offset_negOne, intDot_negOne]
        norm_num
    · rintro s ⟨_, x, hx⟩
      have h1 := hx eOne seg_facet_one
      have h2 := hx (-eOne) seg_facet_negOne
      rw [seg_offset_one, intDot_one] at h1
      rw [seg_offset_negOne, intDot_negOne] at h2
      linarith
  rw [qCodegree, hT.csSup_eq]
  norm_num

/-- The hypothesis of the endpoint is satisfiable, and the endpoint applies. -/
theorem seg_hypothesis : (((1 : ℕ) : ℝ) + 1) / 2 < qCodegree (latticeHull segV) := by
  rw [seg_qCodegree]
  norm_num

theorem seg_cayley : ∃ k t : ℕ,
    (k : ℤ) ≤ ⌊2 * (((1 : ℕ) : ℝ) + 1 - qCodegree (latticeHull segV))⌋ ∧
      IsCayleySumIn (latticeHull segV) k t :=
  dickensteinNill_cayley 1 (latticeHull segV) segV rfl seg_full seg_hypothesis

end Cayley382145
```

### Cayley382145Audit.lean

```lean
import Cayley382145Main
import Cayley382145Sanity

/-! Axiom audit for the MathDB 382145 endpoint, its supporting theorems and the sanity witness. -/

#print axioms Cayley382145.dickensteinNillCayleyConjecture_holds
#print axioms Cayley382145.dickensteinNill_cayley
#print axioms Cayley382145.facetNormals_finite
#print axioms Cayley382145.exists_min_cert
#print axioms Cayley382145.projection_core
#print axioms Cayley382145.cayley_of_projection
#print axioms Cayley382145.seg_qCodegree
#print axioms Cayley382145.seg_facet_iff
#print axioms Cayley382145.seg_cayley
```
