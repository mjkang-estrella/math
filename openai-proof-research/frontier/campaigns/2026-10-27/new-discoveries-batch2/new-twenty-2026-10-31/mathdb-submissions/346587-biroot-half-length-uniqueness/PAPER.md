# Additive bounds and half-length uniqueness of primitive bi-roots

MathDB 346587 · 20 November 2026 · formalization stage two

**Certification status: complete Lean proof, subject to the accompanying clean
replay receipts and later independent review.** The unconditional theorem
`BiRoot.half_length_biroot_unique` proves the literal source statement for every
finite alphabet, and `BiRoot.weighted_primitive_intersection_add_three` proves the
stronger positive-integer weighted bound with additive deficit three. The former
geometric premise `NontrivialGeometry` is now a theorem, proved by constructing
the flowers, their folded readers, the actual glued quotient, its preserved paths,
and its common-word prefix coverage. Only `propext`, `Classical.choice`, and
`Quot.sound` occur in the endpoint axiom output. All stage-one sources are retained
unchanged; historical comments there describe that earlier stage only.

## Source, definitions, and exact formal target

The primary source is G. Castiglione, G. Fici and A. Restivo, *Primitive Sets of Words*, [arXiv:2005.10668v1](https://arxiv.org/pdf/2005.10668v1), §§2–5, later *Theoretical Computer Science* 866 (2021), 25–36, [DOI](https://doi.org/10.1016/j.tcs.2021.03.003). The arXiv PDF and extracted text are retained locally. The cached primary source and the supplied proof and review were read for this continuation; no refused publisher endpoint was retried. The supplied MathDB record was extracted separately with the required isolated Python command.

The following are the source's mathematical definitions and conjectures as printed (mathematical typography normalized to Markdown).

**Primitive word, §2:**

> A word $w$ is primitive if $w=v^n$ implies $n=1$, otherwise it is called a power.

Next to it, the unchanged Lean definition from ReturnCodeBridge is

```lean
def PrimitiveWord {α : Type*} (w : FreeMonoid α) : Prop :=
  w ≠ 1 ∧ ∀ (v : FreeMonoid α) (n : ℕ), w = v ^ n → n = 1
```

The identity denotes the empty word. The explicit nonempty clause agrees with the source: the empty word fails its power condition, for instance at exponent two.

**Maximality, Definition 1:**

> A submonoid $M\in\mathcal M_k$ is $k$-maximal if for every $M'\in\mathcal M_k$, $M\subseteq M'$ implies $M=M'$.

Here $\mathcal M_k$ consists of submonoids with at most $k$ generators in $A^+$. **Primitive set, Definition 2:**

> A finite set $X\subseteq A^*$ is primitive if it is the basis of a $|X|$-maximal submonoid.

The source's basis description in §2 is:

> Conversely, given a submonoid $M$ of $A^*$, there exists a unique set $X$ that generates $M$ and is minimal for set inclusion. In fact, $X$ is the set
> $X=(M\setminus\{\varepsilon\})\setminus(M\setminus\{\varepsilon\})^2$,
> i.e., $X$ is the set of nonempty words of $M$ that cannot be written as a product of two nonempty words of $M$.

The literal Lean definitions, unchanged from the proof lane, are

```lean
def TwoGenerated (S : Submonoid M) : Prop :=
  ∃ x y : M, S = Submonoid.closure ({x, y} : Set M)
def TwoMaximal (S : Submonoid M) : Prop :=
  ∀ T : Submonoid M, TwoGenerated T → S ≤ T → S = T
def AtomIn (S : Submonoid M) (x : M) : Prop :=
  x ∈ S ∧ x ≠ 1 ∧ ∀ a b : M, a ∈ S → b ∈ S → x = a * b → a = 1 ∨ b = 1
def generatedMonoid (X : Finset (FreeMonoid α)) : Submonoid (FreeMonoid α) :=
  Submonoid.closure (↑X : Set (FreeMonoid α))
def PrimitivePair (X : Finset (FreeMonoid α)) : Prop :=
  X.card = 2 ∧ TwoMaximal (generatedMonoid X) ∧
    ∀ z : FreeMonoid α, z ∈ X ↔ AtomIn (generatedMonoid X) z
```

Allowing identity generators in `TwoGenerated` includes the cases of zero and one nonempty generator. It does not enlarge the class of generated submonoids beyond those with at most two nonempty generators.

**Bi-root, §5:**

The preceding sentences ask whether the primitive word is a concatenation of copies of two words x and y. The printed defining sentence is:

> If we further require that $\{x,y\}$ is a primitive set, then we call $\{x,y\}$ a bi-root of the word $w$.

The Lean encoding is `PrimitiveWord w`, `PrimitivePair X`, and `w ∈ generatedMonoid X`. In particular, “primitive pair” does not mean merely that its two words are individually primitive.

**Conjecture 2, verbatim:**

> Let $w$ be a primitive word. Then $w$ has at most one bi-root $\{x,y\}$ such that $|x|+|y|<|w|/2$.

The half-length condition is encoded by `2 * (∑ x ∈ X, FreeMonoid.length x) < FreeMonoid.length w`; multiplication by two is exact over natural lengths. The full unchanged target is

```lean
def HalfLengthUniquenessStatement (α : Type*) [DecidableEq α] : Prop :=
  ∀ (w : FreeMonoid α), PrimitiveWord w →
    ∀ (X U : Finset (FreeMonoid α)),
      PrimitivePair X → PrimitivePair U →
      w ∈ generatedMonoid X → w ∈ generatedMonoid U →
      2 * (∑ x ∈ X, FreeMonoid.length x) < FreeMonoid.length w →
      2 * (∑ u ∈ U, FreeMonoid.length u) < FreeMonoid.length w → X = U
```

**Conjecture 1, verbatim mathematical statement:**

> Let $X^*=\{x,y\}^*$ and $U^*=\{u,v\}^*$ be $2$-maximal submonoids. If $X^*\cap U^*=z^*$, with $z$ primitive, then $|z|<|x|+|y|+|u|+|v|$.

This stronger additive conjecture motivates the weighted induction. The principal MathDB endpoint remains Conjecture 2. The proof uses literal word monoids; there is no model equivalence accepted only on paper.

## The ordinary theorem and its scope

Let A be a finite alphabet and let ρ:A→Z_{>0}. For a word t write Lρ(t) for the sum of its letter weights. Suppose X={x,y} and U={u,v} are distinct primitive pairs and w is a nonempty primitive word belonging to X*∩U*. Then

**Lρ(w) < Lρ(x)+Lρ(y)+Lρ(u)+Lρ(v).**

Taking all weights equal to one proves source Conjecture 1 in its two-basis case. If a printed two-generator 2-maximal monoid has a one-element basis r, it must be the whole one-letter alphabet monoid: otherwise adjoining a word outside it gives a proper two-generated extension. In that degenerate case the primitive intersection word is the one letter and the additive inequality is immediate. If the two printed monoids coincide and their intersection is cyclic, their common basis has one element and falls in this case. Otherwise two-element bases are distinct and covered by the theorem. Thus this causes no gap in the stronger source statement. If both alleged bi-roots have size strictly smaller than |w|/2, the right-hand side is smaller than |w|, contradicting the displayed bound. Thus source Conjecture 2 holds with its full strict half-length hypothesis and without an alphabet-size or parameter cutoff.

The source assumes a finite alphabet, and the Lean theorem uses `[Fintype A]`, as expressly allowed by the supplied statement-fidelity review. It quantifies over every such alphabet without a cardinality cutoff. No all-alphabet endpoint is present in the packet. The mathematical extension to an arbitrary alphabet follows by restricting to the finite union of the letters in w and in the four generators. The inclusion of this finite alphabet induces an injective free-monoid morphism. Maximality and atoms reflect along it, as in `primitivePair_reflected`; primitivity reflects by `primitiveWord_reflected`, membership reflects by injectivity, and lengths are unchanged. Apply the finite-alphabet theorem and map the resulting pair equality back. This short restriction argument is not a separately kernel-checked endpoint here. The public row should say “for every finite alphabet, as in the source.”

## Elementary graph conventions

All graphs in the proof are finite directed edge-labeled multigraphs with positive-letter labels in A. There are no formal inverse-letter edges. Their underlying undirected multigraph may have loops and parallel edges. Each graph has a distinguished root. For a connected graph define its cycle rank by

r(G)=|E(G)|−|V(G)|+1.

A directed graph is deterministic if there is at most one outgoing edge of a given label at each vertex, and codeterministic if there is at most one incoming edge of a given label at each vertex. In a graph having both properties the transition of any fixed letter is an injective partial map on vertices.

An elementary fold identifies two equally labeled edges with the same initial vertex, identifying their terminal vertices as well; or the analogous operation for two edges with the same terminal vertex. Exactly one edge is removed. If the two other endpoints were different, one vertex is also removed; otherwise no vertex is removed. Thus a fold leaves the cycle rank unchanged or decreases it by one. Root and labels are carried to the quotient. Folds preserve every positive labeled closed path already present, and preserve strong connectivity. Repeatedly folding terminates because the number of edges decreases. The resulting graph is deterministic and codeterministic. No confluence or group-theoretic version of Stallings folding is needed.

For a pair of nonempty words s,t, its flower graph consists of two directed cycles, labeled s and t, based at one common root and otherwise using separate vertices and edges. Its cycle rank is two. For a positive letter weight ρ, the total edge weight of the flower is Lρ(s)+Lρ(t), and folding cannot increase this total edge weight.

### Lemma 1: folded flowers of primitive pairs have cycle rank two

Take a flower for a primitive pair and perform folds until the graph is deterministic and codeterministic. Its rank is at most two and it is strongly connected. Every strongly connected finite directed graph has at least as many edges as vertices. If equality holds, each vertex has outdegree and indegree exactly one, so the graph is one directed cycle. Its rooted positive closed words are powers of the label r of that cycle.

Rank zero is impossible because there is a nonempty positive closed path. Rank one would put both generators in r*, a monoid with at most one generator. This contradicts 2-maximality and the fact that the given pair is a two-element basis. Hence the folded graph has rank two.

## The incidence-graph calculation

Let G and H be deterministic and codeterministic, strongly connected rooted graphs of rank two. Suppose a word w=a_0...a_(N−1), N>0, labels a rooted closed path in both. Write g_i and h_i for the states just before letter a_i. Indices on positions are modulo N.

Construct an undirected bipartite **multigraph K** with vertex set the disjoint union V(G)⊔V(H). For each position i add a separate edge e_i joining g_i to h_i, colored a_i. Even if two positions give the same pair of states, their edges remain separate. Isolated vertices are retained.

For a letter a, let K_a have as vertices the sources of all a-edges of G and H, again on separate sides, and as edges those e_i with a_i=a. Include sources whose corresponding edge is not traversed by w, as isolated vertices. Determinism identifies this vertex set bijectively with the disjoint union of the a-edges of G and H. Thus

|V(K_a)|=|E_a(G)|+|E_a(H)|.

For an undirected multigraph F, put β(F)=|E(F)|−|V(F)|+c(F), where c counts all connected components, including isolated vertices. This is the dimension over F_2 of its usual cycle space: choose a spanning forest; the fundamental cycles of the non-forest edges form a basis, since each has its own non-forest coordinate and an even edge subset supported in a forest must be empty. This proves the formula also for parallel edges and isolated vertices. Set β=β(K) and β_a=β(K_a).

Form a directed labeled graph P by taking the disjoint union of G,H and identifying the two occurrences of every state and edge along the common w-path. More explicitly, identify g_i with h_i and identify the two a_i-edges used at position i, taking the equivalence relations generated by these identifications. The terminal-vertex identifications are already included because the terminal states are g_(i+1),h_(i+1).

P is connected, since the roots are identified. Its vertices are exactly the components of K. Its a-edges are exactly the components of K_a. Consequently

|V(P)|=|V(G)|+|V(H)|−N+β,

|E(P)|=|E(G)|+|E(H)|−N+∑_a β_a,

and therefore

**r(P)=3+∑_a β_a−β.**                                     (1)

These counts concern the edge-equivalence relation just specified, not an additional automatic identification of all equally labeled parallel edges. Any further determinization is a further fold and may decrease the rank.

The cycle spaces of K_a embed in that of K and have disjoint edge supports. Hence ∑β_a≤β and r(P)≤3. If equality ∑β_a=β holds, every simple cycle of K is monochromatic. Indeed, otherwise the edge vector of a mixed-color simple cycle would not belong to the direct sum of the monochromatic cycle spaces: restricting its edges to a color that changes along the cycle gives a vertex of odd degree. This contradicts equality of dimensions. This argument also covers two-edge cycles formed by parallel edges.

The literal quotient maps from each input reader to P preserve all positive paths. The two roots are identified at position zero. Every vertex in either strongly connected summand has paths to and from its root, so P is strongly connected and retains the four generator loops and the common loop. Apply the least folded quotient to P and call the result F. Rank nonincrease gives r(F)≤r(P)≤3. The implementation needs only the split r(F)≥3 or r(F)≤2, so it does not depend on a separate upper-bound-three lemma.

### Lemma 2: the rank-three case forces K to be a forest

Suppose F has rank at least three and w is primitive. Since folds do not increase rank, (1) and ∑β_a≤β force r(P)=3 and β=∑β_a. Thus every simple cycle of K is monochromatic.

Suppose K had a simple cycle C. All its edges have one color, say a. Apply the a-transition to every vertex of C, in G or H respectively, and replace each edge indexed i by the edge indexed i+1 modulo N. Determinism makes these transitions well-defined, while codeterminism makes the vertex maps injective separately on the two sides. The image is therefore again a simple cycle in K, with the same distinct position indices shifted by one. It too must be monochromatic. Repeat this argument.

For any two distinct position indices i,j on C, it follows that a_(i+t)=a_(j+t) for every integer t≥0, with indices modulo N. Hence the cyclic word w is invariant under the nonzero shift j−i modulo N. If d=gcd(N,j−i), the word is a power of its prefix of length d, with exponent N/d≥2. This contradicts primitivity. Thus K has no cycle.

In particular each K_a is a forest. For every letter a occurring in w, its N_a position edges satisfy

N_a≤|E_a(G)|+|E_a(H)|−1.

For unused letters the analogous weak inequality with no subtracted one is immediate. Multiplying by positive letter weights and summing gives

**Lρ(w) < total_edge_weightρ(G)+total_edge_weightρ(H).**     (2)

The strict inequality follows because w is nonempty and at least one positive weight is subtracted. This weighted conclusion is essential for the induction below.

## First-return recoding

### Lemma 3: the return words used by finitely many rooted loops form a finite prefix code

Let F be any finite deterministic labeled rooted graph, and let z_1,...,z_s be finitely many rooted positive closed words. Split their rooted paths at every visit to the root. Each piece is nonempty and has no internal root visit. Collect the distinct labels of these pieces into a finite set B.

No element of B is a proper prefix of another. Otherwise the unique path for the longer label would visit the root after reading the shorter label, contradicting its first-return property. Thus B is a prefix code. Replace each b∈B by a new letter and let φ:B*→A* be its nonerasing decoding morphism. Greedy prefix parsing proves φ injective. Each z_i has a unique encoding, namely its sequence of first-return pieces.

If x,y generate a 2-maximal monoid with a two-element basis and x=φ(x'), y=φ(y'), then x',y' form a primitive pair over the new alphabet B. Indeed, if Q is generated by at most two nonempty B-words and {x',y'}* ⊊ Q, then φ(Q) would be a monoid generated by at most two positive A-words properly containing {x,y}*. Injectivity makes properness persist. This contradicts 2-maximality. The decoding map restricts to an isomorphism from the encoded pair monoid onto the original pair monoid. It preserves nonempty elements and decompositions into two nonempty monoid elements. Hence it preserves the nonempty indecomposable elements, which are exactly the unique minimal generating basis. The two distinct encoded words are therefore that basis. Any equality of two different factorizations into the encoded generators would decode to one in the original free basis, so freeness is inherited as well. The atom, maximality and primitivity reflections are checked in ReturnCodeBridge and TargetDefinitions; their simultaneous instantiation is checked in ReaderDescent.

Likewise, distinct pair monoids stay distinct after encoding; and if an encoded w' were a proper power, φ(w') would be a proper power. Thus primitive words stay primitive under this encoding. These statements use only injectivity and nonerasing decoding, not a claim that arbitrary forward encodings preserve maximality.

Give each new letter b the positive weight Lρ(φ(b)). Then the weighted length of every encoded z_i is exactly Lρ(z_i).

## Proof of the weighted theorem

Use strong induction on the **ordinary unweighted number N of letters of w**, proving the stated theorem simultaneously for all finite alphabets and all positive integer letter weights. The weights are not the induction measure.

If a factorization of w over one of the pairs uses only one generator s, then w=s^k with k≥1. Primitivity gives k=1. Its weighted length is already strictly smaller than the sum of the four positive generator lengths. We may therefore assume both generators of each pair occur in its w-factorization.

Build and fold the two flowers. By Lemma 1 their folded graphs G,H have rank two. Build P from their common w-path and fold it to F as above. Split into r(F)≥3 and r(F)≤2. This split does not require ruling out the small ranks separately.

If r(F)≥3, Lemma 2 and the nonincrease of weighted edge totals under flower folding give

Lρ(w)<edgeweightρ(G)+edgeweightρ(H)
       ≤Lρ(x)+Lρ(y)+Lρ(u)+Lρ(v),

as required.

Suppose r(F)≤2. The original four words label rooted positive loops in F, as does w. If F has only its root as vertex, it has at most two edges. All four words then belong to the monoid generated by their single-letter labels (with repeated or identity generators allowed if needed). By 2-maximality both pair monoids would equal that monoid, contradicting their distinctness: a submonoid of finite words has a unique minimal generating set (its nonempty indecomposable elements), and both pairs are that basis. So F has a non-root vertex.

Every vertex of F is visited by a prefix of w, as follows. Each literal
flower vertex is the endpoint of a prefix of one of its generators (the shared
root is the empty prefix of either). Every generator occurs in a factorization
of w: if one is omitted, the factorization uses only the other and primitivity
would make w itself that generator. If w=a·x·b and the selected flower vertex is
reached after i letters of x, then the prefix of length |a|+i reaches its image:
a belongs to the generated monoid and is a rooted loop. This proves prefix
coverage first in each folded flower. Quotient path transport carries that
coverage into F; surjectivity of both successive vertex quotients covers all its
vertices. In particular a non-root vertex is visited. At least one first-return
piece of w therefore has ordinary length at least two. This is the exact
vertex-coverage argument formalized in GeneratorCoverage, PairAutomaton and
GeometryAssembly; no edge-coverage premise remains.

Apply Lemma 3 to x,y,u,v,w in F. Their finite return alphabet B gives encoded words x',y',u',v',w', distinct primitive pairs, and a primitive common word w'. The first-return segmentation is compatible with concatenation of rooted loops, so w' belongs to both encoded pair monoids. Since at least one return piece of w has length at least two, |w'|<|w|=N.

With the new positive letter weights from Lemma 3, the strong induction hypothesis yields

Lρ(w)=Lρ'(w')
 <Lρ'(x')+Lρ'(y')+Lρ'(u')+Lρ'(v')
 =Lρ(x)+Lρ(y)+Lρ(u)+Lρ(v).

This completes the induction, including all small words and all root/non-root configurations.


## Sharp uniform integer deficit

For positive integer letter weights the argument proves the slightly stronger uniform bound

**Lρ(w)+3 ≤ Lρ(x)+Lρ(y)+Lρ(u)+Lρ(v).**

Here is a complete verification of the strengthening. Run the same strong induction on ordinary common-word length with this endpoint. In the unused-generator case w=s, each of the other three nonempty generators has weight at least one, so the bound follows. In the rank-three case put d_a=|E_a(G)|+|E_a(H)|−|w|_a. Every d_a is nonnegative by the forest argument. Since both input graphs have rank two,

|V(K)|=|V(G)|+|V(H)|=|E(G)|+|E(H)|−2.

The nonempty forest K has N edges and at least one component, hence N≤|V(K)|−1. Consequently ∑d_a=|E(G)|+|E(H)|−N≥3. As ρ(a)≥1,

edgeweightρ(G)+edgeweightρ(H)−Lρ(w)=∑ρ(a)d_a≥∑d_a≥3.

Flower folding does not increase edge weights, so the claimed generator bound follows. In the rank-two case the return-letter weights remain positive integers, so the stronger induction hypothesis applies to the shorter encoded word, with every weighted length preserved. This handles all branches and proves the uniform deficit.

The constant three is optimal already for w=abc, X={a,bc}, U={ab,c}, where the total generator length is six. These are the source's elementary all-distinct-letter factorizations, used only to show sharpness, not offered as a separate discovery. A less trivial exact equality example is

X={ca,aab}, U={bcacac,a}, w=aabcacaca=aab·(ca)³=a²·bcacac·a.

It has |w|=9 and total generator length 12. For X, any at-most-two-generator extension must have a generator carrying c and another carrying b. Both must be used among the factorizations of ca and aab: a single word cannot generate both, since their letter supports differ. Neither generator can carry both b and c, since neither target word contains both letters. Thus ca is a power of the c-generator and aab a power of the b-generator; their single occurrences of c and b force both powers to have exponent one. For U, any extension must contain the one-letter generator a. Its other generator must contain b and occur exactly once in bcacac. All remaining factors are a's outside that occurrence; the initial b and terminal c force them absent, so the other generator is bcacac itself. Thus both pairs are literally 2-maximal. They are prefix codes and their displayed generators are the minimal bases. The common word is primitive because it contains exactly one b. Its letter counts are (5,1,3), while the four generators total (6,2,4) in the order (a,b,c), so all three strict letterwise inequalities are simultaneously sharp.

Unit weights additionally give uniqueness whenever both alleged bi-roots have size at most floor((|w|+2)/2), since their total would be at most |w|+2. The original printed strict half-length theorem remains the principal source endpoint. This sharpening is part of the same result family; it is not a separately kernel-checked endpoint.


## The quotient-fold proof used in Lean

The manuscript's local-fold argument proves rank monotonicity ordinarily. The implementation gives a different, direct proof for the least quotient. Let C_V be the space of vertex potentials constant on vertex classes and C_E the space of edge functions constant on edge classes. The coboundary d(f)(e)=f(s(e))−f(t(e)) maps C_V to C_E. Conversely, if d(f) belongs to C_E, induction on the generating vertex fold equivalence proves f belongs to C_V. For a forward fold the equal initial potentials and equal edge differences give equal terminal potentials; for a backward fold the equal terminal potentials give equal initial potentials. The current backward identification is usable as an edge-class relation, without being an induction hypothesis. Thus d induces an injection (K^V/C_V)→(K^E/C_E). The constant spaces have dimensions equal to the numbers of quotient vertices and edges. Comparing quotient dimensions gives |E_F|−|V_F|≤|E|−|V|. This is formalized in FoldRank, without a fold sequence or termination assumption.

For the glued graph, both vertex and edge types are actual endpoint quotients. The edge-incidence kernel is linearly equivalent to the product of the color-supported positional kernels, by restricting coordinates to each label. Injectivity of the pair (source,label) identifies actual transitions with colored sources, including unused transitions as isolated vertices. Rank-nullity then proves the exact quotient count and the dimension hypothesis needed for primitive cycle propagation. This closes the counting bridge at the abstract transition level. The formal cycle argument is expressed directly in signed incidence coordinates over the rationals, so it needs no conversion theorem from a graph library's simple-cycle definition. A nonzero vector of minimal support in the positional boundary kernel exists whenever that kernel is nonzero. The disjoint color-space dimension equality implies its support has one color. Injective partial transitions transport that support to the shifted positions while preserving nonzero minimality; every shifted support is therefore monochromatic too. Selecting two distinct indices from this support gives equality of the corresponding cyclic letter streams, and PeriodicWord contradicts primitivity. Thus the signed kernel is zero directly. The rank-nullity and weighted-forest arguments then supply the required counts and inequalities, exactly as in the combinatorial account above. ReaderTrajectories and TwoFlowerGeometry now produce these data from the literal folded flowers, with the exact transition count and weight bound. GluedGraph constructs P on these quotient types, and GeometryAssembly uses its rank lower bound directly in the original RankThreeCertificate.

## Complete formal assembly and literal endpoint

All three stage-one contracts are discharged: `flowerConstruction`,
`oneVertexRigidity`, and `nontrivialGeometry`. The latter is obtained from
`geometricInput_exists` and `GeometricInput.certificates`, not assumed. The
conditional theorems in the unchanged stage-one files are used only with this
proved argument.

The alphabet-changing induction is simultaneous over types in one universe.
A first-return alphabet is a finite subtype of `List A`, so stays in the same
universe; its `Fintype` comes from actual proved finiteness. The induction measure
is the ordinary encoded length, whereas positive integer weights transfer the
original weighted lengths exactly. Applying the same induction to the stronger
`+3` bound proves `weighted_primitive_intersection_add_three`.

The unconditional theorem is:

```lean
theorem half_length_biroot_unique {A : Type u} [Fintype A] [DecidableEq A]
    (w : FreeMonoid A) (hw : PrimitiveWord w) (X U : Finset (FreeMonoid A))
    (hX : PrimitivePair X) (hU : PrimitivePair U)
    (hxw : w ∈ generatedMonoid X) (huw : w ∈ generatedMonoid U)
    (hx : 2 * ∑ x ∈ X, x.length < w.length)
    (hu : 2 * ∑ u ∈ U, u.length < w.length) : X = U
```

`half_length_uniqueness_statement` checks its exact type identity with the
unchanged `HalfLengthUniquenessStatement A`. No geometry, dimension, coverage,
or recoding hypothesis remains. `half_length_hypotheses_inhabited` supplies the
literal primitive word 000001 and the primitive pair {0,1} twice, showing all
source hypotheses are simultaneously satisfiable. Nonvacuity uses ordinary
kernel reduction for finite calculations.

The appendix contains every source in import order, byte-identical to src/.
REPORT.md gives the full endpoint statements, axiom output and individual
compile/kernel-check receipts. The required independent final review remains
outside this implementation lane.

## Significance and bounded prior art

The result strengthens the source's square-root bound to the full strict half-length range and gives a sharp additive deficit of three. Its interest lies in the colored positional incidence calculation and weighted return descent; numerical examples alone do not prove it. The packet supplies an unconditional formal proof; acceptance and discovery credit remain root decisions after independent review and source/prior-art clearance.

The final-check lane refreshed the registry searches and read the accessible source preprint, the Castiglione–Holub 3-maximal preprint, and both Echi–Khalfallah–Kroumi product papers (RAIRO 2022 and arXiv:2202.09091). None of these supplies the additive bound or half-length uniqueness. The 2023 open manuscript of the 3-maximal paper still recalls a structural cyclic-intersection theorem rather than a length bound. The omega issue and PR searches on the source identifier and primitive bi-roots were empty, as were the two GitHub code searches. Local Principia, mio-qwq, omega and openai/math searches found no relevant resolution.

Journal-text and citer-census limitations remain. The publisher body returned HTTP 403 in the final check. The author's institutional repository lists the journal editorial PDF as restricted to archive managers and the openly available PDF explicitly as a preprint. Its plain-text abstract loses the square-root sign; the publisher's indexed abstract retains the square-root result. Neither abstract establishes the final journal conjecture wording. Fresh OpenAlex and Semantic Scholar citation requests returned HTTP 429, so a complete current citing list was not obtained. Echi's 2022 topology paper and 2025 primitive-deficiency paper were inspected at the primary abstract level only; they concern primitive-root topology and periodic products respectively. No claim of complete novelty clearance is made.

The closest prior results are the source's Theorem 6, Proposition 7 and Theorem 14: cyclic intersection, a multiplicative length bound and square-root uniqueness. The additive conclusion needs the positional cycle calculation and weighted return descent above; no short deduction from those published bounds was found. This is a bounded assessment. Final discovery credit requires resolving the remaining journal-text and citation-census uncertainty, in addition to root's independent kernel replay.
