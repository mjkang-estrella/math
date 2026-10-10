# Discrete frontier scout: attempted constructions and certified obstructions

Date: 2026-10-08. Scope: combinatorics, complexity, and group theory. Corpus premise: all theorems in `openai/math` at **fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb** are accepted as true. The local catalogue contains 719 manuscripts / 372 result families; the full path search used `sources/preprints-tree.json`, not the truncated root tree.

**Outcome: no complete solution or demonstrated new substantial case of a remaining named problem was obtained. Do not promote this report as one.** The main attempted bridge is a new-to-this-investigation construction program connecting the accepted sharp Boolean-information theorem to Frankl's conjecture. It fails in its exact form, and an elementary quantitative theorem below obstructs its natural approximate repair. The quantitative ingredient has established biased-isoperimetric antecedents; it is not a claimed new-to-literature theorem. A separate graph construction toward Caccetta–Häggkvist also fails, for an explicit structural reason.

The first-pass edge/genus coloring estimates, matrix-update algorithms, cyclic affine actions, singularity undecidability, and related parameter substitutions are not proposed again. No index, existing finding, or shared source manifest was edited. Sources newly gathered for this scout are in `frontier/sources/discrete/`, with URLs and SHA-256 hashes in its own `manifest.json`.

## 1. Named-target screening and actual MathDB significance

The public HTML returned by MathDB on the retrieval date contains an `importance` field in its serialized page data. This is an observed category, **not a numerical score or rank**. The pages inspected did not expose a numerical significance ranking. List-position and unlabeled counters have not been interpreted as significance scores.

- **Frankl's union-closed sets conjecture:** [MathDB entry](https://mathdb.com/p/355601/the-union-closed-sets-conjecture). Public page data says `importance: celebrated`. The named target is: for every finite nonempty union-closed family \(\mathcal F\ne\{\varnothing\}\), some element of \(\bigcup\mathcal F\) occurs in at least \(|\mathcal F|/2\) members. No family in the complete pinned catalogue claims this conclusion. The accepted Courtade–Kumar and Hellinger theorems concern uniform product inputs, so their relevance requires a bridge, examined below. This is the principal high-significance target of the report.
- **P versus NP:** [MathDB entry](https://mathdb.com/p/315853/p-versus-np-problem), public data `importance: landmark`; the site also identifies it with the Millennium Prize collection. Families 108, 112, 129, and 135 give particular determinantal, depth-three, automaton, or homogeneous-depth-five bounds, rather than a lower bound for unrestricted deterministic polynomial-time computation. Family 105 and coloring hardness in 106 are hardness reductions, not unconditional separations. Catalogue screening supplied no new construction converting these results into a separation. **No claim of resolution or new complexity lower bound.** Also, the entry juxtaposes the question \(P=NP\) and the conjectural answer \(P\ne NP\); this report treats it as the decision problem, not as two interchangeable assertions.
- **Caccetta–Häggkvist:** [MathDB entry](https://mathdb.com/p/374186/caccetta-haggkvist-conjecture). This particular merged/source entry has `importance: corpus`; no claim that it has a high numerical MathDB rank is justified. The target is a directed cycle of length at most \(\lceil n/d\rceil\) in every finite loopless simple digraph with minimum outdegree \(d>0\). The one-sided triangle case remains outside the explicit accepted Seymour consequences. See Section 5. The regular/minimum-semi-degree triangle cases are already upstream and are excluded as discoveries.
- **Grigorchuk's modified Milnor problem:** [MathDB entry](https://mathdb.com/p/341285/grigorchuk-s-modified-milnor-problem). Its stated assertion is that finitely presented groups with vanishing algebraic entropy have at most polynomial growth. The corresponding candidate is an infinite finitely presented group of intermediate growth. Family 247 gives an infinite finitely presented residually finite periodic group but supplies no subexponential word-growth conclusion in its main statement. Periodicity alone gives no such upper bound. This remains a construction problem; see Section 6. No high numerical ranking was verified.

Two additional screening traps were excluded:

1. The [entropy–KL strengthening of Frankl on MathDB](https://mathdb.com/p/356898/the-entropy-kl-divergence-strengthening-of-the-union-closed) is already **false** in primary literature: David Ellis, [arXiv:2211.12401v1](https://arxiv.org/pdf/2211.12401v1), Section 2. It cannot be counted as an unresolved target merely because MathDB labels it open.
2. General nonsoficity, non-surjunctivity, the finitely presented Burnside question, Thompson-F nonamenability, Hadwiger, Sidorenko, and the named exact cycle–clique Ramsey formula are all already addressed in the pinned corpus. They are not remaining targets under this task's premise. Likewise the stronger finitely-presented-group alternative “virtually nilpotent or containing a free two-generator semigroup” cannot be advertised as a new construction from a periodic counterexample: that would be an immediate transfer from family 247, exactly the kind of first-pass corollary excluded here.

## 2. Actual accepted input: what the information theorem says

Read sources:

- Family 119, *Sharp binary-information contraction on the discrete cube*, [`build/main.tex`, `main:soft`, `main:ck`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Sharp-binary-information-contraction-on-the-discrete-cube-September-24-2026/build/main.tex). All its TeX components were downloaded; the main theorem statements were read and the component structure was checked.
- Its companion, *Hellinger contraction with arbitrary Boolean output bias*, [`build/main.tex`, `thm:main`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Hellinger-contraction-with-arbitrary-Boolean-output-bias-September-24-2026/build/main.tex). The main statement was checked and all TeX components cached. Searches of both papers found no Frankl/union-closed conclusion. This is a companion check, not a claim to have audited every proof line.

Precisely, let \(X\) be uniform on \(\{-1,1\}^m\), and obtain \(Y\) by independent coordinate noise of correlation \(\rho\in[-1,1]\). Let \(U\in\{-1,1\}\) be any randomized binary summary of \(X\), with the noise independent of \((X,U)\). Put
\[
 H(r)=-\frac{1+r}{2}\log\frac{1+r}{2}
      -\frac{1-r}{2}\log\frac{1-r}{2},\quad
 \psi(r)=\log2-H(r).
\]
The accepted theorem is
\[
 I(U;Y)\le \psi\bigl(|\rho|\psi^{-1}(I(U;X))\bigr),
\]
where the inverse takes values in \([0,1]\). Thus for deterministic Boolean \(U=f(X)\), crossover probability \(\epsilon\in[0,1/2]\),
\[
 I_2(f(X);Y)\le1-h_2(\epsilon).
\]
Randomizing **the summary** does not remove the uniform-product hypothesis on **the input**. Nor does “arbitrary Boolean output bias” in the Hellinger companion remove it.

The proposed construction was to encode a uniform random member of \(\mathcal F\) by fair bits while preserving the union operation, so that a cube-noise inequality could control the entropy of unions. That is a substantial missing construction, not an allowed change of variables. The following results test it independently of upstream truth.

## 3. Exact construction attempt: equal-fiber union coding is rigid

### Lemma A — characterization of balanced union maps (proved here)

Let \(q:2^{[m]}\to\mathcal F\) be a surjection onto a finite family of subsets of a finite ground set. Assume
\[
 q(S\cup T)=q(S)\cup q(T)\qquad(S,T\subseteq[m]).
\]
Assume also that \(q(X)\) is uniform on \(\mathcal F\) when \(X\) is a uniformly random subset of \([m]\). Define \(B=q(\varnothing)\), \(A_i=q(\{i\})\), and \(J=\{i:A_i\ne B\}\). Then:

1. \(q(S)=B\cup\bigcup_{i\in S}A_i\).
2. Every \(i\in J\) has a private witness
   \[
   e_i\in A_i\setminus\left(B\cup\bigcup_{j\in J\setminus\{i\}}A_j\right).
   \]
3. \(|\mathcal F|=2^{|J|}\), and union on \(\mathcal F\) is isomorphic to union on \(2^J\).

Conversely, a construction with these private witnesses sends uniform input to the uniform law on its image.

**Proof.** Taking one argument empty gives \(B\subseteq q(S)\). Decomposing a set into singletons proves (1). A subset maps to \(B\) exactly when it uses only the \(m-|J|\) inactive coordinates. Hence the fiber of \(B\) has size \(2^{m-|J|}\). Uniformity means all fibers have that size. Delete the inactive coordinates; the induced surjection on \(2^J\) is now a bijection. Its values on \(J\) and \(J\setminus\{i\}\) must differ, supplying \(e_i\). The bijection respects union, proving (3). Conversely, membership of the private witnesses recovers the active input subset, and the inactive coordinates give the same multiplicity to every output. ∎

“Boolean” here refers to the **abstract union structure**. It does not assert that the members are literally all subsets of their original ground set. For example, two generators may overlap while each has a private witness.

### Explicit counterexample to the hoped-for universal encoding

Take the four-member union-closed chain
\[
 \mathcal C=\{\varnothing,\{1\},\{1,2\},\{1,2,3\}\}.
\]
Its cardinality is already a power of two, so cardinality alone is not the obstruction. It is not a Boolean union semilattice, so Lemma A excludes **every** balanced union-preserving coding from **every** finite fair cube.

The natural three-generator map has fibers of sizes \(1,1,2,4\), producing probabilities \((1,1,2,4)/8\), rather than the uniform law. Simply declaring this pushforward uniform changes the measure. Reweighting inputs by reciprocal fiber size gives a dependent, nonuniform input law; the accepted theorem does not cover that law.

This disposes of the exact construction. It proves no new case of Frankl: for a family with such private-witness coding, one of those witnesses already appears in exactly half its members by an elementary count.

## 4. Approximate repair: a sharp positive defect for rare monotone bits

An obvious repair is to use a monotone encoding that only approximately preserves union, allowing rare output events to be generated from several fair bits. The following quantitative obstruction makes that repair testable.

### Lemma B — union defect lower bound (proved self-contained)

Let \(g:\{0,1\}^m\to\{0,1\}\) be increasing, let \(X,Y\) be independent uniform bit strings, and put
\[
 p=\Pr(g(X)=1),\qquad c=\frac{\log(3/4)}{\log(1/2)}\in(0,2/3).
\]
Then
\[
 \boxed{\Pr\{g(X\vee Y)\ne g(X)\vee g(Y)\}
 \ \ge\ p^c-2p+p^2.}\tag{1}
\]
For \(0<p<1/2\), the right side is strictly positive. Equality holds when \(g\) is the AND of \(k\) prescribed coordinates, so in particular the bound is sharp at every \(p=2^{-k}\).

**Proof of the biased-measure estimate.** For an increasing Boolean function write \(\mu_t(g)\) for its expectation under independent Bernoulli-\(t\) bits. We prove by dimension induction that
\[
 \mu_{3/4}(g)\ge \mu_{1/2}(g)^c.\tag{2}
\]
The dimension-zero case is immediate. Let \(a\le b\) be the uniform measures of the sections with the last bit zero and one. By induction,
\[
 \mu_{3/4}(g)\ge\tfrac14a^c+\tfrac34b^c.
\]
For \(0\le a\le b\),
\[
 \frac{a^c+3b^c}{4}\ge\left(\frac{a+b}{2}\right)^c.\tag{3}
\]
If \(b=0\) this is immediate. Otherwise set \(r=a/b\), and subtract the right side from the left. The resulting function
\[
 F(r)=\frac{r^c+3}{4}-\left(\frac{r+1}{2}\right)^c
\]
vanishes at \(r=0,1\), since \(2^{-c}=3/4\). Its derivative is positive near zero and negative at one, with exactly one zero in between: the derivative's sign is the sign of
\[
 \left(\frac{2r}{r+1}\right)^{c-1}-2,
\]
which strictly decreases from infinity to \(-1\). Thus \(F\) first increases and then decreases and is nonnegative. This proves (3), hence (2).

**Proof of (1).** Monotonicity gives
\(g(X)\vee g(Y)\le g(X\vee Y)\) pointwise. The left event therefore has probability
\[
 \mu_{3/4}(g)-\Pr(g(X)\vee g(Y)=1)
 =\mu_{3/4}(g)-(2p-p^2),
\]
which is at least (1) by (2). To see strict positivity for \(0<p<1/2\), divide the proposed lower bound by \(p\) and set
\(K(p)=p^{c-1}-2+p\). Then \(K(1/2)=0\), and
\[
 K'(p)=1-(1-c)p^{c-2}
 \le 1-3(1-c)=3c-2<0
 \quad(0<p\le1/2),
\]
since \((1/2)^{c-2}=3\). Thus \(K(p)>0\) below one half. Finally an AND of \(k\) bits has \(p=2^{-k}\), \(\mu_{3/4}(g)=(3/4)^k=p^c\), proving equality. ∎

### Consequence for the proposed sampler

For any monotone set-valued coding \(q:\{0,1\}^m\to2^{[n]}\), each output coordinate \(g_e(x)=1_{e\in q(x)}\) is increasing. If \(q(X)\) is uniform on \(\mathcal F\), then \(p_e=d(e)/|\mathcal F|\). For any coordinate with \(0<p_e<1/2\),
\[
 \Pr\{q(X\vee Y)\ne q(X)\cup q(Y)\}
 \ge p_e^c-2p_e+p_e^2>0.\tag{4}
\]
For a fixed family and a fixed rare element, this obstruction is independent of the dimension of the encoding. Adding fair bits cannot drive its union error to zero. Equation (4) does **not** assume that a monotone balanced encoding exists for every family.

For the simplest rare-bit gadget, AND of two bits, \(p=1/4\) and the defect is exactly \(1/8\). An AND of \(k\) bits has exact defect
\[
 (3/4)^k-2^{1-k}+4^{-k}.
\]
Although this absolute error tends to zero as \(k\to\infty\), its ratio to the intended event probability grows like \((3/2)^k\). Thus this construction does not give small *relative* error for a rare membership test.

**Novelty check.** Estimate (2) is a familiar consequence of the weak biased edge-isoperimetric inequality; see Ellis–Keller–Lifshitz, [*On a biased edge isoperimetric inequality for the discrete cube*, arXiv:1702.01675v2](https://arxiv.org/pdf/1702.01675v2), Theorem 1.6. The proof above was included to make the exact obstruction independent of a literature black box. Formula (1) packages that estimate for this attempted coding construction. Neither that packaging nor Lemma A is asserted to be a publication-level new theorem. The source check prevents presenting rediscovered isoperimetry as a new Frankl advance.

### The different entropy–KL escape route is already disproved

For distributions \(p\) of a random set \(A\) and \(q\) of \(A\cup B\), where \(B\) is an independent copy, the claimed inequality would be
\[
 H(q)+D(q\Vert p)>H(p)
\]
when every coordinate has probability below one half and \(H(p)>0\). Ellis's primary counterexample has probabilities
\((.3,.2,.2,.3)\) on \(\varnothing,\{1\},\{2\},\{1,2\}\), then the perturbation \(p_\epsilon=(.3,.2+\epsilon,.2+\epsilon,.3-2\epsilon)\), whose two marginals are \(1/2-\epsilon\). At the unperturbed point the difference is exactly
\[
 .08\log_2(2/3)<0.
\]
Continuity makes it remain negative under the indicated strict-marginal perturbation. This is an already known disproof, not a new result of this scout. The distribution is nonuniform; it is not a counterexample to Frankl.

The separate literature on nonuniform union-closed laws also explicitly leaves the uniform/zero-temperature case outside its scope: Zargar, [arXiv:2305.19338v2](https://arxiv.org/html/2305.19338v2), abstract and introduction. A successful new route must supply a measure-sensitive inequality for uniform union-closed families, with a justified treatment of coding error or nonproduct inputs. The accepted binary-noise theorem alone does not supply it.

## 5. Directed-graph construction attempt and its exact failure

### Accepted input and duplicate exclusion

Read the actual statements and consequence sections of family 173, *A proof of Seymour's second neighborhood conjecture*:

- [`00-introduction.tex`, `thm:main`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-proof-of-Seymours-second-neighborhood-conjecture-September-23-2026/build/source/00-introduction.tex): every nonempty finite oriented graph has \(|N_2^+(v)|\ge|N_1^+(v)|\) for some vertex, with **exact** second neighborhood.
- [`04-weighted-consequences.tex`, `cor:weighted-forms`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-proof-of-Seymours-second-neighborhood-conjecture-September-23-2026/build/source/04-weighted-consequences.tex): vertex-weighted, simultaneous-weight, and arc-weighted forms are already stated.
- [`05-directed-cycle-consequences.tex`, `cor:directed-cycle-consequences`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-proof-of-Seymours-second-neighborhood-conjecture-September-23-2026/build/source/05-directed-cycle-consequences.tex): triangle-free graphs have a vertex with \(2d^+(v)+d^-(v)\le n-1\). Minimum in- and outdegree at least \(n/3\) forces a triangle, and an \(r\)-regular girth-four digraph has at least \(3r+1\) vertices.

All TeX components were pinned. These consequences are **duplicates**, not findings. Primary historical context is Sullivan's [2006 AIM survey](https://aimath.org/WWN/caccetta/caccetta.pdf), Sections 2–4 and 6.

### Proposed bridge: balance an independent blowup

Let \(D\) be oriented, with adjacency matrix \(A\). Replace vertex \(v\) by \(m_v\ge1\) independent clones, and every arc \(v\to u\) by all arcs between the corresponding clone classes. This preserves the absence of directed triangles. Each clone of \(v\) has
\[
 d^+_{D(m)}(v)=\sum_{v\to u}m_u,
 \qquad d^-_{D(m)}(v)=\sum_{u\to v}m_u.
\]
Thus this construction is Eulerian exactly when
\[
 (A-A^{\mathsf T})m=0.\tag{5}
\]
If such masses could always be chosen with both weighted neighborhood masses at least a third of their total, the accepted minimum-semi-degree result would prove the remaining triangle target. This is a genuine construction obligation; stationarity of a random walk is an **edge-flow** balance and does not imply (5).

### Explicit obstruction: strong connectivity does not give positive masses

On \(\{0,1,2,3,4\}\), use the directed five-cycle
\[
 0\to1\to2\to3\to4\to0
\]
and the extra arc \(0\to2\). The digraph is strongly connected and triangle-free. Balance at vertices 2 and 4 would require
\[
 m_3=m_0+m_1,\qquad m_0=m_3,
\]
so \(m_1=0\). Therefore **no full-support independent blowup is Eulerian**, regardless of its size. This disproves the proposed universal balancing lemma even for strongly connected triangle-free digraphs.

One can delete vertex 1 and balance the resulting directed four-cycle. That does not save the asserted full-support construction. Conversely, this example has minimum outdegree only \(1\), with \(n=5\), so it does **not** disprove the special balancing assertion under the unproved triangle threshold \(\delta^+\ge n/3\).

### What remains conditional, and why a reformulation is not progress

Under the accepted weighted Seymour theorem, a triangle-free induced subgraph on a nonempty set \(S\) cannot have positive masses \(w_v\), total 1, satisfying
\[
 w(N^+(v))\ge1/3,\qquad w(N^-(v))\ge1/3\quad(v\in S).\tag{6}
\]
Indeed, choose a weighted Seymour vertex. Its own positive mass, its in-neighbors, its out-neighbors, and its exact second out-neighbors are disjoint, so
\[
 1\ge w_v+w(N^-(v))+w(N^+(v))+w(N_2^+(v))
 \ge w_v+1>1,
\]
a contradiction. This handles real weights directly; no rational approximation at an endpoint is being assumed.

But a directed triangle itself supplies (6), by putting mass \(1/3\) on its three vertices. Consequently, under the accepted premise, existence of a subset and weights as in (6) is **equivalent** to existence of a directed triangle. Proving that certificate always exists from \(\delta^+\ge n/3\) would solve the target, but naming the certificate alone is not a new partial result. No such construction was obtained.

## 6. Group/complexity frontier: precise remaining obstructions

The group-theory input actually inspected was family 247's [*An infinite finitely presented residually finite 2-group*, `sections/introduction.tex`, `thm:main`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-infinite-finitely-presented-residually-finite-2-group-October-5-2026/build/sections/introduction.tex), with the companion's finite-rule construction searched for word-growth estimates. It asserts an infinite ordinary finitely presented residually finite group in which every element has finite 2-power order. It uses a finitely presented graded algebra with matrix-nil positive-degree ideal and a finite-index subgroup of a rank-12 Steinberg group.

A possible substantive extension would be a new finite-rule algebra with a quantitatively controlled normal-form language, together with control of the Steinberg kernel, yielding \(\log|B_G(R)|=o(R)\). Neither finite-dimensionality of each homogeneous algebra component, nilpotence of every fixed matrix, nor residual-finiteness detection supplies that estimate. Even an upper bound on the elementary-matrix quotient does not bound its central extension without a bound on the kernel's contribution to word balls. No required growth bound or new algebra construction was proved. Thus no intermediate-growth claim is made.

For complexity, the desired new bridge would have to amplify a **restricted-model** lower bound into a bound applying to the circuits or machines produced by a simulation of every polynomial-time algorithm. The available degree/depth restrictions cannot silently be imposed on those simulations. Taking products of lower-bound instances does not establish multiplicativity of the lower-bound measure. No such amplification theorem, and no new named special case of \(P\) versus \(NP\), was obtained. These are screened directions only; none is a theorem supported by an unread manuscript.

## 7. Verification and recommendation

Run:

```sh
python openai-proof-research/frontier/experiments/discrete_union_bridges.py
```

The saved result is `frontier/experiments/discrete_union_bridges.results.json`. It checks:

- all increasing Boolean functions through dimension four: counts 3, 6, 20, 168;
- the exact union-defect identity by independent pair enumeration;
- the positive defect for every nonzero rare function in those dimensions;
- 5,802 base/generator systems on a three-element ground set, checking the equal-fiber/private-witness equivalence (500 balanced systems);
- exact rational AND-gadget defects, the chain fiber multiplicities, and the five-vertex graph's balance obstruction.

Integer/rational identities are exact. Comparisons with the irrational exponent \(c\) are only floating-point sanity checks; the proof is the induction in Lemma B. Finite checks establish no conjecture and no literature novelty.

**Classification:** Lemmas A and B and the five-vertex obstruction are proved; the hoped-for general encoding and full-support balancing lemma are disproved; the measure-sensitive Frankl bridge and the one-sided directed-triangle construction remain unproved; the entropy–KL route is a previously published disproof. No complete high-significance target or genuinely new substantial named case emerged. Retain this as a rigorous negative scout and a source/obstruction record, not as a replacement portfolio of routine corollaries.
