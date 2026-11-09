# NEWr334 ordinary mechanisms and exclusion bridges

## 357238 — full localized clique inequality, routine source bridge (zero credit)

The source is Kirsch–Nir arXiv:2301.05678v1/v2, Conjecture 6.5, published EJC 31(3) (2024) P3.34 Conjecture 24. The source sums over t-cliques, not all clique sizes; the corpus drops the superscript t in its K notation. Work with its intended t-cliques. No transcription fix is proposed as discovery.

Let H be q-uniform, t≥q>i≥1. Write d(I)=C(x(I)−i,q−i) and x(T)=max_{I⊂T,|I|=i} x(I). Only I in some t-clique are needed. Such I have d(I)≥C(t−i,q−i), so on the source's increasing binomial branch x(I)≥t. All denominators below are positive. The link H(I) has d(I) edges and is (q−i)-uniform. Every t-clique containing I gives a distinct (t−i)-clique in that link. By the Lovász clique bound as actually used in source Theorem 5.8 (journal Theorem 18),

 N_I := #{T∈K^t(H):I⊂T} ≤ C(x(I)−i,t−i).

Since x(T)≥x(I) and C(z−q,t−q) is nondecreasing for z≥t,

 Σ_{T⊃I} 1/C(x(T)−q,t−q)
 ≤ N_I/C(x(I)−q,t−q)
 ≤ C(x(I)−i,t−i)/C(x(I)−q,t−q)
 = d(I)/C(t−i,q−i).

The last equality follows by cancellation of the falling products (or factorial identities); it holds for real x(I)≥t. Sum over I, count every t-clique C(t,i) times and every q-edge C(q,i) times:

 C(t,i) Σ_T s'(T) ≤ Σ_I d(I)/C(t−i,q−i)
                       = m C(q,i)/C(t−i,q−i)
                       = C(t,i) m/C(t,q).

Cancel C(t,i)>0. I not lying in a t-clique contribute zero on the left and may simply be included on the nonnegative right. For t=q every edge contributes one and equality holds directly. This proves the entire intended endpoint for all finite H.

First attempt was to charge weighted t-cliques directly to q-edges; a uniform cap on clique extensions of one edge is not supplied by the i-degree alone. The successful second attempt charges to i-sets and retains d(I) rather than bounding each link contribution by one. This is exactly the existing Theorem 5.8 proof with a changed denominator and the displayed binomial identity. It is therefore a complete routine source adaptation, not a new credited result. The companion Kirsch–Radcliffe arXiv:2207.02336v2 Theorem 27 proof uses the same (I,E,K) double count and link clique bound; Theorem 51 supplies packing-shadow equality. Aragão–Souza's local Maclaurin companion is about the other source conjecture, not needed for this deduction. The journal statement was compared in extracted text; printed reference page inspected, but not all figures/citing bodies. No Pi plan.

## 382297 — full exact endpoint

See CANDIDATE.md: attempted scalar-mean induction and pathwise count domination were replaced by the full antisymmetric distribution invariant. The proof covers fixed ordered endpoints, bidirectional vertical-edge tokens, every n and the original uniform E7 sample space. Ordinary mathematics complete; source/novelty and independent acceptance review remain bounded gaps, not accepted credit.

## 374717 — third sustained route, unresolved

Source arXiv:2605.13662: distance-reducing minimal Markov basis versus circuits for a simple graph incidence matrix. A tempting full route is to decompose an arbitrary Graver move into conformal circuits and transfer a circuit-reducing basis move to the whole Graver move. The first obstruction is applicability: positive-coordinate domination must hold, not just support containment. Source Lemma 3.15 proves a special transfer when the reducing move itself is a cycle (all nonzero coordinates ±1); it derives zhat+≤z+ from support inclusion and transfers negative-support intersection. General primitive walks can have repeated bridge edges with coefficient 2. A circuit nested only in support need not have matching coordinate multiplicities, so the same implication is not proved.

A second route is to strip a leaf block of a primitive even walk and lift a reducing move from the remaining walk. This needs the selected reduction to retain a strict l1 improvement after restoring the stripped block and to be a member of the ORIGINAL arbitrary minimal Markov basis. Those properties do not follow from circuit support decomposition. The complete-intersection Theorem 3.14 proof uses technical Lemmas 3.15–3.16; dropping that hypothesis is the unpaid step. No exact graph/move witness was constructed and no computation was run. Example 1.1 has a column with THREE ones and therefore is not an incidence matrix of a simple graph; treating it as a refutation is an out-of-domain shortcut and is rejected. Residual: for every primitive walk and every minimal graph Markov basis reducing all circuits, exhibit an applicable basis move with strict l1 reduction, or give one genuine graph whose basis fails this implication. No Pi plan.

## Other source/classical bridges and compact parked routes

366106: Davila–Schuerger–Small arXiv:2412.03463v1/v2 Theorem 5 is already the connected claw-free statement. Lemma 4 supplies a minimum PSD forcing set with connected white complement. During a PSD force x→y, white connectedness makes it a standard force. If deletion of y split the white graph, y would have neighbors in two different remaining white components; these two nonadjacent vertices and blue x form an induced claw (x has no other white neighbor). Thus white connectedness persists. For a disconnected graph, both forcing numbers are sums over connected components: a forcing process cannot use edges between components, and componentwise optimal sets can be united. Every component is claw-free. Sum the source equalities; isolated vertices contribute one to both, the empty graph zero. Exact full corpus endpoint already public, zero credit.

357397: Cordero's source states Conjecture 7.1 and proves stronger Theorem 7.2 immediately. For X an n-cbc take the compatible singleton {X}; Proposition 3.3 supplies a border (P,Q) for its stable closure, with n=|P||Q|. A d coprime to n is coprime to |P|, and 1 is coprime to |Q|. Set d1=1,d2=d in Theorem 7.2: its two-coordinate multiplier becomes exactly a^i b a^{dj mod n}, and membership in the resulting compatible set guarantees the n-cbc property. Its proof inducts on occurrences of the substituted code, transports borders by Proposition 3.5 and uses duality. This exact implication is explicitly printed after the proof. No new theorem.

357265: source Corollary 6.9 already bounds the number of distinct primitive circular words of Φ(n^{a_n}…2^{a_2}) by ceil((n−1)/2). Map each distinct primitive conjugacy class to its length. The image cardinality is at most the domain cardinality, hence the exact distinct-length bound follows. Corollary proof invokes Theorem 5.11's correspondence with band-brick families and Theorem 6.7's bound; the source explicitly states the same implication to the thesis conjecture. This is a complete public bridge, zero credit.

357186: source Theorem 2.11/Proposition 4.1 proves an O(α²/c⁴) energy difference under Assumption 2.8; for fixed α the ratio to c^−2 is O(α²/c²)→0. This is strong evidence that the record mislabels a source theorem as open. Exact physical charge/spectral hypotheses are not all present in the corpus; retain source-resolution/fidelity HOLD rather than invent an unconditional claim. Section 4 proof was read, not the full analytic dependency chain.

374596: latest arXiv:2605.05346 (August 2026 body) announces the exact n²/9 theorem, not merely a conjecture. The theorem statement is a public resolution signal. The long analytic/flag-algebra proof is not independently rederived here. No discovery or proof-body clearance claim.

366058: LR specialization is not a polynomial reduction without compatible encodings; the actual source explicitly notes binary/unary input mismatch. Missing: polynomial-size reduction to permutation-encoded Schubert coefficients. 366059: a signed GapP formula is not a nonnegative witness interpretation or a proof of #P nonmembership. Missing: an unconditional separation mechanism; neither direction is established here.

366131/366132: identity cover gives the easy forward existence from embeddings; lifting an embedding through the orientation double cover supplies familiar sufficiency in the orientable variant. Neither supplies necessity for arbitrary finite graph covers. Missing: exact surface-embedding obstruction surviving finite covers. No endpoint correction/algorithmic existence is counted.

366185: source Conjecture 8.5; reverse-partition/Schur case and checked small compositions do not imply the arbitrary key basis formula. Missing: deletion-compatible decomposition in back-stable key tableaux for every composition. No negative-entry/zero-index transcription shortcut.

366259: minimality of a generalized Lyubeznik matching does not prove existence of a minimal generalized Barile–Macchia matching. Missing: construct the required orders and critical-cell bijection preserving all multidegrees. Source Conjecture 3.4 remains only a question in the body reviewed.

366410: Tutte obstruction route must convert every failed one-edge extension on torus/Klein bottle to an odd-region quadrangulation. Projective-plane theorem and mere parity do not classify noncontractible barriers. Missing that full topological extraction; Conjecture 19 in source.

366446: pairwise intersection of longest paths does not give a common vertex. Projecting subtree paths to the caterpillar spine suggests a Helly route, but a common HOST-tree point is a clique of G, not a common vertex of all longest paths. Missing: a longest-path exchange argument selecting one member of the clique uniformly, including subdivided branches. The source's ≤26 transversal bound is not equality one.

367723: existing embeddings for Aut(F_n)/mapping-class groups do not construct type-(A) actions for every finitely generated solvable-word-problem group. Higman embedding alone gives no finitely generated point stabilizers or finite pair-orbit property. No full route.

371549: a greedy exchange increasing target overlap would need both bases to stay bases and not undo progress; ordinary symmetric exchange is not that monotone lemma. Source counterexample to EMBRACING oriented exchanges is a stronger failure and cannot refute the ordinary endpoint. No full rank-r bound.

382335: reflection across a hyperplane through a swaps chamber signs and preserves the ball, proving the vanishing-on-walls direction. Away from all walls, antisymmetry alone gives no nonvanishing. Source leading terms for small dimensions do not control every radius/center/type. Missing: globally sign-definite chamber expression, including all Coxeter factors; no R=0/ambient-dimension correction claimed.

357132: periodic directing words do not force periodic outputs, and an iid almost-sure density theorem does not apply to a deterministic periodic input. Missing: convergence and unbiased phase frequencies for the directed expansion for every periodic word. No finite computation would settle the full statement.
