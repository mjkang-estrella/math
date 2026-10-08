# Independent review: rational singular points on normal rational quartics

**Round:** 1. **Date:** 2026-10-08. **Verdict: ACCEPT.**

Scope: section 2 of `proposals/algebra_geometry.md` only. I read `AGENTS.md`, the pinned revision metadata, the relevant catalogue entry and manuscript sources. As requested, all upstream theorem statements are accepted as true; this review checks their application and the new deductions, not their proofs. No previous review findings or responses were supplied. No mathematical correction is required. The citation and presentation improvements below would make the result easier to reuse.

## 1. Exact upstream dependency

The immutable revision is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` of `openai/math`.

The decisive source is [Hilbert's tenth problem over the rational numbers, `build/sections/07-consequences.tex`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Hilberts-tenth-problem-over-the-rational-numbers-October-6-2026/build/sections/07-consequences.tex), section label `red:degree-normal-form`, corollary label `thm:degree-normal-form`, specifically item (ii). It explicitly assigns Turing degree $0'$ to rational solvability of the sum of squares of an input nonempty finite list of integral polynomials of degree at most two. Variables, summand count and coefficient heights are unrestricted. I read the complete consequences section, including its distinction between Turing and many-one reductions.

The [introduction, theorem label `thm:main`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Hilberts-tenth-problem-over-the-rational-numbers-October-6-2026/build/sections/01-introduction.tex) supplies undecidability of unrestricted rational polynomial solvability. That theorem alone would not justify degree $0'$; the cited consequences corollary does.

I also compared the [September 24 companion/version's complete consequences section](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Hilberts-tenth-problem-over-the-rational-numbers-September-24-2026/build/sections/07-consequences.tex): it is byte-identical to the October 6 section. Neither states the singular-point result. The catalogue's other companion, [the pointwise two-converse introduction](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-pointwise-2-converse-for-elliptic-curves-with-rational-two-torsion-October-7-2026/build/sections/introduction.tex), has an elliptic-curve Selmer-corank theorem (`thm:main`), not this consequence. This was a relevant-companion check, not an exhaustive search of all repository manuscripts.

## 2. Independent geometric proof

Let $n\geq0$, $s\geq1$, and $q_i\in\mathbb Z[x_1,\ldots,x_n]$ have total degree at most two. Write $N=n+1$, $z=(x,t)$, $S(z)=\sum_iq_i(x)^2+t^4$, and

\[
A_K=K[z,u,v]/(uv-S),\qquad Y_K=\operatorname{Spec}A_K
\]

for any extension field $K/\mathbb Q$. All geometry below works in particular over $\overline{\mathbb Q}$.

**Degree and integrality.** The coefficient of $t^4$ in $S$ is exactly one: none of the $q_i$ involves $t$. Hence $S\ne0$ and $uv-S$ has degree exactly four, including zero and constant lists. In the UFD $R=K[z,u]$, the only possible nonunit common divisor of the coefficients $u,-S$ would divide the prime element $u$. But $u\nmid S$, since $S\in K[z]\setminus\{0\}$. Thus $uv-S\in R[v]$ is primitive. It is a nonconstant linear polynomial in $v$ over $\operatorname{Frac}(R)$, hence irreducible there. Gauss's lemma makes it irreducible in $R[v]$; irreducible elements of this UFD are prime. Consequently $A_K$ is a domain. This proves geometric integrality, without asserting that $S$ is irreducible or squarefree.

**Chart, smooth point, density and rationality.** Localization gives

\[
(A_K)_u\simeq K[z,u,u^{-1}],\qquad v\mapsto S(z)/u.
\]

The chart is nonempty and dense because $A_K$ is a domain and $u\ne0$. Its inverse maps $(z,u)$ to $(z,u,S(z)/u)$. It is $\mathbb A_K^N\times\mathbb G_{m,K}$, and is smooth; also $F_v=u\ne0$ there. Its function field is purely transcendental of degree $N+1=n+2$, proving rationality over $\mathbb Q$. At $x=t=0,u=1$, the coordinate $v=S(0,0)$ supplies the promised rational smooth point. Finally $\mathbb Q^N\times\mathbb Q^\times$ is Zariski dense: a polynomial vanishing on that grid vanishes identically by induction on the number of variables over the infinite field $\mathbb Q$. This density passes through the chart to $Y$.

**Rational singular points.** Characteristic zero permits the hypersurface Jacobian criterion. The gradient is exactly the one displayed in the proposal. A singular point has $u=v=0$ and $t=0$, the latter also following directly from $F_t=-4t^3$. At a rational point, $F=0$ then says $\sum q_i(x)^2=0$, which is equivalent to all $q_i(x)=0$ in the ordered field $\mathbb Q$. Conversely these equations annihilate $F$ and every derivative. Projection to $x$ and $x\mapsto(x,0,0,0)$ are inverse bijections of the indicated rational-point sets. This is a statement about rational points, not an identification of the geometric singular scheme with the common-zero scheme of the $q_i$.

**Normality.** Over $K=\overline{\mathbb Q}$, the support of the singular locus lies in $Z=V_Y(u,v)$. Its coordinate ring is

\[
A_K/(u,v)\simeq K[z]/(S).
\]

Since $S$ is nonzero and nonconstant in the polynomial ring in $N\geq1$ variables, $\dim Z=N-1$. Meanwhile $\dim Y_K=N+1$. Thus every singular component has codimension at least two; finite-type domains over a field satisfy the usual dimension formula here. All codimension-one points are regular, giving $R_1$. At every point the ambient polynomial local ring is regular, hence Cohen–Macaulay, and $F\ne0$ is a nonzerodivisor. Its quotient is Cohen–Macaulay, so satisfies $S_2$. Serre's criterion gives normality of $Y_K$. The same proof applies over every extension of $\mathbb Q$; in particular $Y$ is normal and geometrically normal.

The cited Stacks section is relevant, but the exact quotient reference is [Lemma 10.104.2, tag 02JN](https://stacks.math.columbia.edu/tag/02JN). [Lemma 10.157.4, tag 031S](https://stacks.math.columbia.edu/tag/031S) is exactly Serre's criterion. The broader tag 00N7 currently called a “quotient lemma” in the proposal is a section containing that lemma. This is a citation precision issue, not a proof error.

## 3. Effectivity, degree and height

Fix the ordinary effective coding of finite lists, including their ambient variable count. Let $L$ be the source list-solvability language, and $D$ the language of such codes for which $Y_q$ has a rational singular point. The proved bijection gives $D=L$. Therefore 

\[
\deg_T D=0'.
\]

Equivalently, compiling the list to the expanded polynomial $F_q$, the chart formulas and the displayed smooth point is a total computable reduction. A decision algorithm valid on all promised hypersurfaces, even if supplied with these certificates, would decide $L$. It need not recognize the promise on arbitrary equations. Recovering a sum-of-squares decomposition from an arbitrary quartic is unnecessary.

Enumeration of rational tuples and exact evaluation of $F$ and all partial derivatives semidecides rational singular-point existence. Hence the upper bound is also valid for equation inputs. If “encoded family” means the set of generated expanded equations rather than list indices, that set of positive instances is still computably enumerable: enumerate lists and rational witnesses and output their compiled equations. The source reduction gives its lower bound. There is no hidden many-one completeness claim for the halting set: the reduction from $L$ is many-one, but the imported halting hardness is only asserted in Turing degree.

For precision, the height statement excludes a total computable function $B$ on the input presentations, with values in $\mathbb N$, such that every positive input has at least one singular rational point whose reduced coordinate numerators have absolute value at most $B$ and whose positive denominators are at most $B$. Compute $B$, enumerate the finite set of all tuples with those bounds, and evaluate the Jacobian equations. This halts on both positive and negative inputs and decides $L$, a contradiction. Even a function required to terminate only on every input in the promised family would give that contradiction after compilation. A partial search that terminates only on positive instances is entirely possible and is not excluded. Dependence on the supplied chart and smooth point cannot help, since these are computable from the original list.

## 4. Boundary checks

- If all $q_i=0$, then $Y=\mathbb A^n\times\{uv=t^4\}$. Its singular support is $\mathbb A^n\times\{0\}$, of codimension exactly two. This tests the sharp normality bound, repeated factors in $S$, and positive-dimensional singularities. Omitting $t^4$ would instead give $uv=0$, destroying integrality in this case.
- For the constant list $q_1=1$, $Y:uv=1+t^4$ is smooth: the simultaneous derivative conditions force $u=v=t=0$, which is not on $Y$. Thus the family contains negative inputs despite always having the displayed smooth rational point.
- Take $q_1=x^2-1,q_2=2x$. Then $S=(x^2+1)^2+t^4$, and $(x,t,u,v)=(\pm i,0,0,0)$ are geometric singular points although neither $q_i$ vanishes there. There is no common zero of the two $q_i$ even over the algebraic closure, and no rational singular point. This explicitly tests the indispensable restriction of the sum-of-squares equivalence to ordered fields. I verified the evaluation at $i$ with exact arithmetic in $\mathbb Q(i)$; the general proof is algebraic, not numerical.
- The affine hypothesis is essential for this reduction. Homogenize using $w$, with $Q_i(x,w)=w^2q_i(x/w)$. The projective closure has equation $uvw^2-\sum Q_i(x,w)^2-t^4=0$. The rational point $[x=0,t=0,u=1,v=0,w=0]$ lies on it and annihilates every first derivative for every input. Thus naive projectivization makes rational singular-point existence always true.
- The argument gives neither a fixed-dimension result nor an isolated-singularity promise. It proves no claim about the technical class of rational singularities. Geometric singular-locus emptiness remains decidable by polynomial ideal computations; it is rational-point existence on that locus that is hard.

## 5. Independent literature assessment and concrete suggestions

The elementary geometric construction itself is established. Arzhantsev, Kuyumzhiyan and Zaidenberg, [*Flag varieties, toric varieties, and suspensions: Three instances of infinite transitivity*](https://arxiv.org/html/1003.3164), Definition 0.3 and Definition 3.1, explicitly define $uv-f(y)=0$ as a suspension. Lemma 3.1 gives irreducibility over an irreducible base; their surrounding discussion studies geometry and automorphism actions. This is a useful prior reference for the construction, not a duplicate of the arithmetic undecidability statement.

I independently read the introduction and Theorems 1.1–1.2 of Garcia-Fritz–Pasten–Vidaux, [*Effectivity for existence of rational points is undecidable*](https://arxiv.org/html/2311.01958v2). Theorem 1.2 concerns systems over $\mathbb Q$ augmented by height-comparison predicates. It does not state the singular-point promise here, and should not be cited as independently establishing the current no-computable-bound consequence.

Bounded searches included `"rational singular points" undecidable`, `"singular locus" "Hilbert's tenth"`, `"singular" "hypersurface" "undecidable" "rational points"`, and suspension/Diophantine variants. I found no exact matching primary theorem. This is insufficient to establish priority, particularly for an elementary conditional reduction that might be folklore or appear under different terminology. The proposal's restrained novelty language is appropriate. The substantive addition relative to the checked upstream consequences is the simultaneous promise of geometric normality, geometric integrality, rationality, an explicit dense smooth chart and a known smooth point while rational singular-point existence stays hard.

Recommended editorial changes, none required to repair validity:

1. Cite `thm:degree-normal-form`, item (ii), directly in section 2; it is the precise source for $0'$, stronger than bare undecidability.
2. Replace the generic quotient-section link by Stacks tag 02JN.
3. Add the suspension reference and describe the contribution as the undecidability consequence under these geometric promises, with literature novelty unresolved.
4. Specify list-indexed coding when first assigning a Turing degree, and optionally state explicitly that the height bound must terminate also on negative promised inputs.
5. Add the projective-closure boundary if the result will be advertised simply as one about “quartics.”

**Disposition:** accept as a fully proved corollary under the stipulated upstream results; do not promote it to a demonstrated new-to-literature theorem. Only this assigned review file was written; proposals were not edited, and no staging, commits or agent delegation were performed.
