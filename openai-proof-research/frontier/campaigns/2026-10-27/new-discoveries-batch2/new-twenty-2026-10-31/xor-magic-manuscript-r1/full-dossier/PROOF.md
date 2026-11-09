# All corrected odd-open and even-closed XOR-magic degrees at powers of two

DRAFT - 1 November 2026 (America/Los_Angeles). Prepared with AI assistance by the Codex research agent. No human authorship or affiliation is asserted. This is an unaccepted research draft; accepted credit is zero and the campaign count remains 14/20 beyond 39.

## Abstract

For every n >= 4, we construct a connected simple open zero-XOR graph of order 2^n for each odd degree from 5 through 2^n-5, and a connected simple closed zero-XOR graph for each even degree from 4 through 2^n-6. A four-fold affine lift over F4 preserves low-degree seeds and their matching decompositions; block replacement then supplies all intermediate degrees. Complements give the top degrees. Finite certificates supply orders 16 and 32. The complete existence theorem is formalized in Lean, together with the uniform negation of the printed Conjecture 25 of Cichacz, Grochowski and Zuazua [1]. Its printed closed endpoint 2^n-4 is already forbidden by their Proposition 24, attributed to Batal. That correction carries no novelty claim. The dossier contains source-identical Lean modules from xor-magic-formal-r5, a portable strict replay, declaration audits and negative controls.

## 1. Source statement and corrected theorem

Write N=2^n and A_n=(Z/2Z)^n. A graph is simple and connected. An open XOR-magic labeling is a bijection l:V -> A_n for which sum_{u in N(v)} l(u)=0 at every vertex. A closed XOR-magic labeling instead requires l(v)+sum_{u in N(v)} l(u)=0. The constant must be zero; an arbitrary group-distance-magic constant is insufficient. Degree d means regularity at every vertex. The order follows from bijectivity.

Conjecture 25 [1, Section 4] asserts existence for each d in {5,7,...,2^n-7,2^n-5} in the open case and each d in {4,6,...,2^n-6,2^n-4} in the closed case. It leaves n implicit. In the nonempty intended scope n >= 4, its fully quantified interpretation is: for every n >= 4, every odd integer d with 5 <= d <= 2^n-5 has an open witness, and every even integer d with 4 <= d <= 2^n-4 has a closed witness. MathDB 372205 says n is positive; that universal reading is also false, since n=4 already refutes it.

Theorem 1 (corrected complete existence). For every integer n >= 4, open witnesses exist for every odd 5 <= d <= 2^n-5, and closed witnesses exist for every even 4 <= d <= 2^n-6. Together with Proposition 24 of [1], these are precisely the possible degrees within the odd-open and even-closed parity classes. This does not classify graphs or address arbitrary labeling groups.

Theorem 2 (printed obstruction). For every n >= 4 the printed assertion is false. This is a zero-credit correction of an inconsistency already excluded by Proposition 24, not an independent discovery. Sections 2-6 prove Theorem 1; Section 2 also proves Theorem 2.
<!-- PAGE -->
## 2. Complements and the affine lift

For n >= 2, the sum of every element of A_n is zero: each coordinate is 1 exactly 2^(n-1) times, an even number. Partitioning V into {v}, N_G(v), and N_complement(v) gives

    sum_{u in N_complement(v)} l(u)
      = l(v) + sum_{u in N_G(v)} l(u).                    (1)

Thus complementation swaps the two zero-sum conditions, irrespective of connectivity. To obtain XOR-magic graphs in the source's sense one must establish connectivity separately. If a graph on N vertices has minimum degree at least N/2, every component has at least N/2+1 vertices, so it is connected.

Suppose a closed (N-4)-regular witness exists. Its complement is cubic and open-zero by (1). Let z have label 0 and let u be a neighbor of z. The other two neighbors a,b of u are distinct and satisfy l(a)+l(b)=0. In characteristic two l(a)=l(b), contrary to injectivity. This does not need connectivity. It is the closed N-4 obstruction already credited to Batal in [1, Proposition 24].

For completeness, open degree 1 would force all neighbors to have label zero. Open degree 3 is excluded by the preceding argument. Degree N-1 has open sum l(v), not identically zero. At degree N-3, the two vertices outside each closed neighborhood must have label sum l(v); at z labeled zero they would have equal labels. These exclude all four odd degrees outside Theorem 1. Identity (1) transfers the four exclusions to closed degrees 0,2,N-4,N-2. These necessity arguments are ordinary mathematics here; the advertised Lean endpoints certify the corrected positive ranges and the printed N-4 obstruction.

A seed consists of a connected d-regular zero-XOR graph G on m=2^r vertices, of the required type, with d >= 4, ordered perfect-matching decompositions M_0,...,M_(d-1) of G and of its complement, and a proper Boolean coloring of M_0 union M_1. It also carries an oriented genuine cycle C in that union, of length L >= 3 with 3 not dividing L. The orientation specified below must follow C consistently.

Use F4={0,1,w,w^2}, w^2+w+1=0. Direct M_0 from color true to false and M_1 from false to true. At every vertex exactly one of these edges enters and one leaves, so every cycle is oriented consistently. Give a directed cycle edge slope w and its reverse w^-1; all other edges have slope 1. Choose one orientation of each undirected edge for indexing. Let a_e denote its slope, and put T_e(x)=a_e x+c_e. The reverse is a_e^-1 x+a_e^-1 c_e. Define the lift on V x F4 by joining (u,x) to (v,T_e(x)) for e=(u,v). It is simple, d-regular, and labeled bijectively by (l(u),x) in A_(r+2).

Two perfect matchings have even cycle lengths and hence admit a proper coloring. The seed includes a chosen coloring to make the orientation and its persistence literal, rather than relying on an unspecified later choice.
<!-- PAGE -->
## 3. Choosing the translations and proving connectivity

Define additive (indeed F4-linear) maps D:F4^V -> F4^E and B:F4^E -> F4^V by

    (Db)_e = b_v + a_e b_u,        e=(u,v),
    column_e(B): 1 at u, a_e^-1 at v, zero elsewhere.     (2)

Here Bc is exactly the vector of constant terms in the lifted neighborhood sums. We need c in ker B but outside im D. The following cardinality argument is the one used in Lean, and requires no rank assertion about either map.

Since |E|=dm/2 >= 2m, |F4^E| >= |F4^V|^2. The composite BD is nonzero: for adjacent distinct u,v its (u,v) coefficient is 1, since their unique edge contributes 1 and no other edge contributes to that off-diagonal entry. Thus im D is not contained in ker B. If ker B were contained in im D, this would be a proper inclusion, so

    |ker B| < |im D| <= |F4^V|.

But |F4^E|=|ker B| |im B| and |im B| <= |F4^V|, contradicting the previous lower bound. Choose c in ker B outside im D. Finite enumeration could make the choice effective; no random success assumption is used.

At (u,x) the first label coordinate is the base zero-sum condition, with l(u) added for the closed case. Put epsilon=0 for open and 1 for closed. The second-coordinate linear coefficient is

    (d-2) + w + w^-1 + epsilon = d+1+epsilon = 0,        (3)

because w+w^-1=1, and d is odd in the open case or even in the closed case. The constant term is (Bc)_u=0. Therefore the lift is zero-XOR of the same type.

We now prove connectivity directly by fibre sizes, avoiding an unproved holonomy-transitivity equivalence. Fix a lifted component K and let S_u={x:(u,x) in K}. Every edge bijection T_uv sends S_u onto S_v: an edge gives one inclusion and its inverse gives the other. Connectivity of G implies that all these sets have the same positive cardinality t.

Around C the composite affine map is x -> a x+b with a=w^L != 1. Such a map has exactly one fixed point (solve (1+a)x=b); conjugating by that point identifies it with multiplication by a, whose remaining orbit has length 3. The set S at the starting vertex is invariant under this map and its inverse. Therefore t is 0,1,3, or 4, never 2. Positivity rules out 0.

If t=1, the unique b_u in S_u obeys T_uv(b_u)=b_v. If t=3, the unique b_u outside S_u obeys the same identity because each edge map also transports complements. Either case gives c_e=b_v+a_e b_u, that is, c=Db, a contradiction. Hence t=4 for every component and every base vertex. Each component therefore contains all vertices of every fibre, proving that the lift is connected. This supplies the precise argument missing in the earlier ordinary exposition.
<!-- PAGE -->
## 4. Persistence and interpolation

Each base perfect matching lifts to a perfect matching: every vertex has exactly one partner over its base mate, with inverse partner map. These lifted matchings partition the lifted graph. Its complement also factors into perfect matchings. Inside each fibre, decompose K4 into its three translation matchings x <-> x+t, t != 0. Over a base G matching the missing edges form K4,4 minus the designated matching; the three maps x -> T_e(x)+t, t != 0, split it into three matchings. Over a base-complement matching, the four maps x -> x+t split the full K4,4. The resulting number is

    3 + 3d + 4(m-1-d) = 4m-1-d.

Every complement edge lies in exactly one of these disjoint blocks. The global base matchings ensure these blockwise matchings cover every lifted vertex exactly once.

Color (u,x) by the color of u. This remains proper on the first two lifted factors. The affine return map around C has a fixed point x_0 by Section 3. Starting there and lifting C gives a closed walk of length L. It is a genuine simple cycle: its projected vertices before return are distinct. It uses the first two lifted factors, keeps their orientation and the same sequence of base colors, and still has 3 not dividing L. Its other return orbit yields a cycle of length 3L, but only the fixed-point cycle is needed. Thus the entire colored seed structure persists. Repeated lifts give degree-4 closed and degree-5 open seeds with both factor decompositions at each exponent r+2.

For interpolation, begin with a lift of a degree-d seed on m vertices. Choose k entire factors of G, 0 <= k <= d. Over their edges replace the designated matching by its three-edge complement in K4,4, increasing every degree by 2k. Choose j entire factors of the base complement, 0 <= j <= m-1-d, and add their full K4,4 blocks, increasing every degree by 4j. Hence the new degree is

    q = d + 2k + 4j.                                    (4)

The sum of all four labels in any fibre is zero: the first coordinate occurs four times and the sum of F4 is zero. A matching edge and the complementary three edges consequently give the same label sum at their endpoint; a full block contributes zero. Thus all neighborhood zero sums persist, including the vertex term in the closed case.

Connectivity needs two cases. If k=0, the original connected lift remains a subgraph. If k>0, one replaced block is K4,4 minus a matching, which is connected: any two vertices on one side share at least two neighbors, and every vertex has a neighbor on the other side. All four vertices in its endpoint fibres are therefore in one component. Along every adjacent base edge, either a matching or a triple block meets every vertex in the next fibre. This propagates fullness through connected G. Added full blocks do not destroy paths.

Dividing q-d by 2, the possible increments form the integer intervals [2j,2j+d], for 0 <= j <= m-1-d. Consecutive intervals overlap since d >= 4. Their union is [0,2m-2-d], so all degrees of parity d from d to 4m-4-d occur.
<!-- PAGE -->
## 5. Finite bases and their certificates

Vertices at order 2^r are integers 0,...,2^r-1 with their binary labels (least significant bit is coordinate 0). Encode row v of the adjacency matrix by the hexadecimal integer h_v, where bit u is 1 exactly when u is adjacent to v. The four persistent seeds have the following compact data. The row arrays, all remaining base witnesses, descent parents and ranks are also in base-data.json; the Lean sources contain the literal lists.

    Base16Closed4:
    aa00,4484,8882,5030,528,5018,8d00,1106
    20d0,6401,252,8045,20a8,1301,22a,845
    Base16Open5:
    7240,e880,2e20,44e0,d840,148c,4219,812a
    b280,1145,882c,2416,331,907,5b,592
    Base32Closed4:
    1414,10020220,24000021,88001800,10010101,140006,8100c000,3820000
    c02010,90000802,488001,300208,1800009,40108100,428040,6440
    14040010,2004082,42010020,a8000400,802820,29000800,4004500,101180
    2010c0,20060080,40410004,40280008,10212,2280004,c042000,80248
    Base32Open5:
    12440002,3d,221202,50902,4800442,a0000602,90008110,b0200800
    2022048,8022024,4010830,1400488,44280004,2404300,10942000,30810040
    41008408,9000304,8404009,c1201000,68404000,4081084,142801,8400c010
    20b0800,21002101,a01410,40160200,c0c1,21080a0,8191000,8800e0

A row list proves the finite conditions by checking symmetry, zero diagonal, exactly d set bits in each row, and XOR of the set-bit indices equal to 0 (open) or v (closed). Connectivity has a separate certificate: parents p(v) and natural ranks r(v), with v adjacent to p(v) and r(p(v)) < r(v) for every v != 0. Iterating parents terminates at 0, yielding a path from every vertex. These checks use only finite integer arithmetic, not a solver's feasibility verdict. The supplied certify_bases.py independently checks every row and every descent, while the corresponding Base*.lean modules prove them by kernel reduction.

At order 16, open degrees 5,7,9,11 and closed degrees 4,6,8,10 have direct certificates. At order 32, open degrees 5,7,...,27 and closed degrees 4,6,...,26 have direct certificates. In particular Base16Closed6 and Base32Closed4 each have their own parents, ranks and descent theorem. These are the two low-degree complements for which the minimum-degree bound does not apply. Their connectivity is certified directly; no invocation of a high-degree complement lemma is made.

For seed iteration the ordered matching lists live in Seed16Closed4, Seed16Open5, Seed32Closed4 and Seed32Open5. Their mate arrays are involutions without fixed points; distinct factor mates at each vertex and coverage of adjacency prove a decomposition. Complement factors satisfy the same conditions. ColourSeed* supplies the Boolean color lists and an indexed oriented walk with an IsCycle proof. The distinguished cycle lengths are 16,16,32,8 respectively. Every one is at least 3 and not divisible by 3. The union for the order-32 open seed has cycles of lengths 8,16,8; the chosen cycle has length 8.

The original authors' graph files at immutable repository revision 7f21f7e0ade3f35b95c1593af97af5defcd54f02 supply several base examples, including the open order-32 degree-27 graph whose complement is the closed degree-4 seed. The dossier preserves those files as inert text. The local closed degree-6 witness at order 32 and other local finite witnesses supplement these bases. Base discovery by an optimizer is separate from exact verification of its edge data.
<!-- PAGE -->
## 6. Induction and the final ranges

Starting separately with exponent 4 and exponent 5, Sections 2-4 produce both colored low-degree seeds at every exponent n >= 4 by steps of two. Relabeling V x F4 by Fin (4m) transports adjacency, labels, mate arrays, coloring, and the actual indexed distinguished cycle. The walk itself is retained, so no claim that an arbitrary closed walk is a cycle enters the induction.

Now let n >= 6 and put N=2^n and m=2^(n-2). There are degree-5 open and degree-4 closed seeds on m vertices. Formula (4) applied to them supplies respectively

    open odd degrees:     5,7,...,N-9;
    closed even degrees:  4,6,...,N-8.                   (5)

Closed degrees 4 and 6 are included in (5). Their complements have open degrees N-5 and N-7. Open degree 5 is included in (5); its complement has closed degree N-6. Since N >= 64, all three complementary degrees are at least N/2. Their complements are therefore connected by the component-size bound of Section 2. Equation (1) proves their required zero sums. Combining these endpoints with (5) proves exactly the two ranges in Theorem 1. For n=4 and n=5 use Section 5's direct certificates, completing both induction parities.

The proof does not append closed degree N-4: Section 2 proves it impossible. Proposition 24's exclusions together with the construction give the complete existence picture only for odd-open and even-closed degrees, as specified. No restriction to bipartite, Cayley, vertex-transitive or planar graphs is asserted. The coloring concerns two matching factors, not the whole graph.

## 7. Literal formal statement

The Lean dossier uses the following definitions verbatim from Literal.lean. The context is V : Type with Fintype V and DecidableEq V; each graph has a decidable adjacency relation. Natural subtraction is harmless in the advertised n >= 4 range. A simple graph is part of the type, connectedness is explicit, and the equivalence supplies every label exactly once.

    abbrev Bits (n : Nat) := Fin n -> ZMod 2

The six literal definitions are displayed on the next page using the original Lean notation. Their type quantifiers prevent the existential graph from being fixed in advance: the witness may depend on n and on the requested degree d. The finite underlying type is allowed to vary. No construction hypothesis, unproved seed premise, or assumed connectivity remains in the final endpoints.

The main theorem is XorMagic.corrected_all : forall n : Nat, 4 <= n -> CorrectedAt n. The second endpoint is XorMagic.not_printed_each_ge_four : forall n : Nat, 4 <= n -> not (PrintedAt n). The latter is a pointwise impossibility assertion at every exponent in scope, stronger than merely finding one failure of the universal printed claim. The re-exports printed_not_all and printed_not_positive also negate the unrestricted and positive-exponent readings. These statements have different scientific roles: only the corrected existence theorem supplies the substantive construction.
<!-- PAGE -->
## 7. Literal definitions (continued)

    def OpenMagic (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) : Prop :=

      G.Connected ∧ ∃ l : V ≃ Bits n, ∀ v, ∑ u ∈ G.neighborFinset v, l u = 0

    

    def ClosedMagic (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) : Prop :=

      G.Connected ∧ ∃ l : V ≃ Bits n, ∀ v, l v + ∑ u ∈ G.neighborFinset v, l u = 0

    

    def OpenExists (n d : ℕ) : Prop :=

      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V)

        (_ : DecidableRel G.Adj), G.IsRegularOfDegree d ∧ OpenMagic G n

    

    def ClosedExists (n d : ℕ) : Prop :=

      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V)

        (_ : DecidableRel G.Adj), G.IsRegularOfDegree d ∧ ClosedMagic G n

    

    def PrintedAt (n : ℕ) : Prop :=

      (∀ d, Odd d → 5 ≤ d → d ≤ 2^n-5 → OpenExists n d) ∧

      (∀ d, Even d → 4 ≤ d → d ≤ 2^n-4 → ClosedExists n d)

    

    def CorrectedAt (n : ℕ) : Prop :=

      (∀ d, Odd d → 5 ≤ d → d ≤ 2^n-5 → OpenExists n d) ∧

      (∀ d, Even d → 4 ≤ d → d ≤ 2^n-6 → ClosedExists n d)

The namespace of these definitions is XorMagic. The declarations appear without alterations in the source-only packet; all 107 Lean modules are byte-identical to xor-magic-formal-r5/formal. The prose expansion on the previous page explains the binders but does not replace the literal source.

In particular OpenMagic and ClosedMagic conjoin connectedness with existence of a bijective zero-sum labeling. OpenExists and ClosedExists additionally quantify the simple graph and demand degree regularity. PrintedAt includes the forbidden closed upper bound; CorrectedAt changes that bound to 2^n-6 and preserves the entire open range. Finite decidability instances are elaboration data and do not weaken these propositions.
<!-- PAGE -->
## 8. Correspondence, replay, and trust

Paper statement | Lean declaration (namespace prefix XorMagic unless shown)
Total sum; complement identity | total_bits; complement_identity
Literal graph definitions | Literal: OpenMagic, ClosedMagic, OpenExists, ClosedExists
Seed and orientation | ColouredSeed; FactorColouring; chosen_outgoing
Translation choice (Section 3) | translation_exists; TranslationFour module
Component fibre argument | EdgeTransport.fibre_transport; fibre_card_reachable;
section_of_singleton; section_of_three; connected_of_affine_loop
Matching/cycle/color persistence | persistedCycle; ColourPersistence, ComplementDecomposition
Interpolation and intervals | InterpAssembly, InterpEndpoints, InterpolationArithmetic
Direct finite bases | Base*.connected; corrected_at_4; corrected_at_5
Two induction bases | seeds_all; main_ranges
Theorem 1 | corrected_all : ∀ n : ℕ, 4 ≤ n → CorrectedAt n
Theorem 2 | not_printed_each_ge_four : ∀ n : ℕ, 4 ≤ n → ¬ PrintedAt n
Universal printed negations | printed_not_all; printed_not_positive

Only propext, Classical.choice and Quot.sound are allowed as transitive axioms. The packet's audits inspect local declarations, full types and bodies, safety flags and transitive axioms, including auxiliary declarations. Shared expression DAGs are checked independently; duplicate generated declarations must have identical canonical type and body hashes. No sorry, admit, new axioms, unsafe, native_decide or ofReduceBool is permitted in the delivered proof modules. The audit does not reinterpret upstream mathlib theorems.

The pinned installation is Lean 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52. The read-only package cache uses mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. Set LEAN_BIN and LEAN_PACKAGES as documented in REPRODUCE.md. The portable driver rejects existing oleans, checks source hashes, discards inherited Lean configuration, retains actual HOME, and writes logs and per-call receipts. Each module is compiled with -j1 -DwarningAsError=true, then checked by leanchecker. The extraction is fresh and path-safe. All deletions, if any, are confined to driver-owned temporary files; this version requires no cleanup deletions.

Each child invocation has affinity to at most two CPUs, 120 CPU seconds, a 140-second wall guard, aggregate sampled RSS <= 6 GiB and MALLOC_ARENA_MAX=2. Upstream cached oleans are trusted. leanchecker shares the same installation; it is an additional check, not an independent implementation of Lean's kernel. Sampling RSS is not a continuous hardware-enforced memory measurement.

Negative controls deliberately corrupt concrete arithmetic, labels, sums, degrees, seed and coloring facts, slope/reverse/composition facts, incidence and holonomy facts, the top endpoint and the inference from CorrectedAt to PrintedAt. Their rejection demonstrates only rejection of these particular false claims with imports resolved; it does not prove the completeness of the audit or guard against every possible specification error. The source-only archive contains no oleans. The full dossier adds the manuscript, evidence, QA images, receipts and manifests. Replay results and hashes are recorded outside this static draft in results.json and SUMMARY.md. Root must perform the final replay and paper review before any acceptance.
<!-- PAGE -->
## 9. Related work, access limits, and bibliography

Siehler [2] develops the closed XOR condition, constructs cubic examples at every exponent at least 2, and studies small cubic graphs with nullity and row-distinctness tests. That is the odd-closed parity class, rather than the two classes constructed here. The author-copy body was read. Cichacz, Grochowski and Zuazua [1] place XOR magic within group distance magic labeling: the group is elementary abelian and the magic constant is zero. Their Theorem 5 supplies some odd-open and even-closed graph at every exponent greater than 3; their finite examples, Cartesian products and complements do not by themselves assert every degree.

Batal's construction paper is credited by [1] for both Observation 1 (complementation) and Proposition 24 (nonexistence). Those are prior results; neither the complement identity nor the printed endpoint correction is offered as novel. The body of Batal's Discrete Applied Mathematics article remains unread: the preserved publisher route returned 403, and repository access produced a bot challenge. No challenge was bypassed. The bibliographic information below for that article is explicitly indirect, from [1] and preserved metadata. Its unread body precludes a complete subsumption assessment.

Batal's arXiv:2609.05934 [3] treats generating and affinely generating group-magic maps and distance-magic labelings via modular kernels and reduced Smith groups. Its introduction explicitly relates Siehler's and Batal's XOR row-separation characterizations to this broader framework. The preserved abstract, introduction, principal statements and relevant binary discussion were read; this is a bounded screen, not a complete audit of every proof. Its order-27 example concerns a different distance-magic conjecture and does not supply the construction proved here.

The dossier inherits dated access receipts from the focused and independent-review lanes (2 November 2026 UTC / 1 November Los Angeles). No new live literature or registry search was performed for this manuscript. Empty citation lists and registry HEAD identities do not establish absence of prior proofs. The bibliography includes only primary bodies actually read, plus the explicitly marked unread Batal item required to give proper credit. No priority claim or worldwide novelty clearance is made. Independent review qualified scope and significance and passed the ordinary mathematics with the two exposition issues repaired above. Root alone can accept; credit remains zero.

[1] S. Cichacz, H. Grochowski and R. Zuazua. Open XOR-magic odd graphs and closed XOR-magic even graphs. arXiv:2512.19278v1, 22 December 2025. https://arxiv.org/html/2512.19278v1. Definitions; Observation 1; Theorems 5, 17, 18; Corollary 20; Proposition 24; Conjecture 25. Primary body read. Associated graph data: grochowskih/RegularXorMagicGraphs, revision 7f21f7e0ade3f35b95c1593af97af5defcd54f02.

[2] J. A. Siehler. Xor-magic graphs. Recreational Mathematics Magazine 6(11) (2019), 35-44. DOI 10.2478/rmm-2019-0004. Primary author-copy body read, especially Theorems 1-4; preserved under evidence/xor-magic-review-r1/work/web/siehler/.

[3] A. Batal. Algebraic characterizations of generating and affinely generating Gamma-magic maps and Gamma-distance magic labelings on regular graphs. arXiv:2609.05934 (2026). https://arxiv.org/html/2609.05934. Primary body sections specified above read; preserved in focused sources/later.html and outputs/later.txt.

Indirect credit, body unread: A. Batal. On the construction of XOR-magic graphs. Discrete Applied Mathematics 379 (2026), 288-315. DOI 10.1016/j.dam.2025.08.055. Attribution follows [1, Observation 1 and Proposition 24]; this item is not presented as a primary body inspected for novelty clearance.
