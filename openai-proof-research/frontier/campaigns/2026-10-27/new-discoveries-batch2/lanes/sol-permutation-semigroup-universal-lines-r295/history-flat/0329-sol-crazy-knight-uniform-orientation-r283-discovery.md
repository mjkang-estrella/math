# Research hold: no full resolution and no discovery nomination

## Exact source and scope

Mella–Pasotti, *A conjecture on the Crazy Knight's Tour Problem*, arXiv:2311.09054v2, revised 4 May 2026, Conjecture 2.3, printed p3. Primary PDF/text are immutable references in bindings.json. Initial submission: 15 November 2023. Live arXiv metadata checked 30 October 2026 at 18:07 UTC still identifies v2. The source defines D_a={(a,1),(a+1,2),…,(a−1,n)}, with indices modulo n. Thus after translating indices the support is precisely

    F={(i,j) in (Z/n)^2 : (i−j) mod n in {0,…,k−1}}.

The occupied diagonals must be cyclically consecutive. Contents of cells play no role. This is not an arbitrary regular bipartite support. A positive row advances to the next occupied column in cyclic increasing order; a positive column advances to the next occupied row. The move is V_C H_R, with the COLUMN SIGN AT THE HORIZONTAL DESTINATION. The question asks for signs constant on each entire row/column giving one nk-cycle. For every odd n≥k≥3 this is conjectured possible. Necessity is already public: both H_R and V_C have sign (−1)^{n(k−1)}, so their product is even, whereas an nk-cycle has sign (−1)^{nk−1}. Thus nk is odd. For n=k use the known full-board result (source Theorem 2.2). For k=1,n>1 each cell is fixed; n=k=1 is a singleton degeneracy outside the intended k≥3 domain, not a credited refutation. Even k, including k=2, is excluded by parity. No change of domain is proposed.

## Early duplicate and subsumption gate

Before sustained calculations, screen.py hash-froze candidate files before semantic interpretation, rechecked bytes afterwards, and screened 1,410 enumerated cached TeX and top-level campaign handback paths (not 1,410 independent papers). Seven matching files are recorded; the only target matches are r277 and its root disposition aliases. The Pasotti growable-realization hit is a different question. Zero matching cached TeX bodies is a bounded observation, not literature clearance. Source-bound r277 primary successor feeds were reused, without recursively copying old trees. The current phrase search returned two arXiv entries: this paper and its ancestor, not a complete citation search.

The ancestor was obtained lawfully from https://ajc.maths.uq.edu.au/pdf/76/ajc_v76_p183.pdf and frozen before reading its extracted body: Costa–Dalai–Pasotti, *A tour problem on a toroidal board*, Australasian Journal of Combinatorics 76(1) (2020), 183–207; arXiv1902.05491v2 was updated 29 August 2019. Actual Lemmas 4.7/4.9 pp191–193 and Proposition 4.11/Theorems 4.12/4.15 pp193–195 were read. They already give the complete uniform-row return-map criterion, propagation by k−1, computer-verified k<200, and n≥(k−2)(k−1). This defeats novelty for the first reduction below. The original 2018 companion proof body was not retrieved here; its gcd-one theorem is also explicitly restated in both obtained primary bodies.

For the target v2, definitions and the actual proofs of Proposition 3.1, Corollary 3.2, Proposition 3.6 (including its induction), Section 4's boundary equivalences, Proposition 4.13, Lemma 4.14, Theorems 5.1/5.4 and Corollary 5.6/Proposition 6.3 were read after binding. Proposition 3.6 restricts E to ordered g-blocks with a truncated final block; h=k−1−|E|. It is not an unrestricted selection theorem. Proposition 4.13 passes through a vertically inflated board, a left-holed board, and a right-holed bishop board. Its supporting lemmas impose positive-parameter inequalities; this chain cannot simply be applied with arbitrary h or E. Theorem 5.1 uses |E|=g+1 and gcd(g+1,k−1)=2. Theorem 5.4 uses |E|=(k−1+g−1)/2 plus the same block admissibility. Corollary 5.6 and Proposition 6.3 give the residue n≡g mod(k−1) through propagation. All are public, including classes where Theorem 5.1 fails.

Current public proof-registry HEAD and unavailable historical registry intervals remain UNKNOWN. Denied GitHub API/raw/codeload/diff/patch, ScienceDirect and challenge routes were not retried. The extra author-query attempt was malformed (literal underscores changed parsing); its zero response is preserved and supplies no clearance. No title or abstract establishes absence of a successor. Acceptance would require additional lawful primary/registry body access.

## Mechanism A: exact simultaneous column switches

Write H=∏H_i and V=∏V_j for the positive row and column k-cycles and T0=VH. Reversing a set E of columns, keeping rows positive, gives EXACTLY

    T_E=(∏_{j∈E} V_j^(−2)) T0.

Proof: V_j^−1=V_j^−2 V_j, and the column supports are disjoint. For odd k, V_j^−2 is a k-cycle. Distinct column multipliers commute, but this does not mean their cycle-merging effects are independent. Initially T0 has k−1+g cycles, not merely g, where g=gcd(n,k−1). In coordinates d=i−j, d≠0 gives k−1 separate n-cycles translated by (+1,+1); d=0 translates by (−(k−1),−(k−1)) and has g cycles. This proves the cycle count, including n=k.

A useful fully proved cut formula handles one, two, or many switches. For any permutation p and any q supported on U, let ρ_U(u) be the first strictly positive return of p to U. Then

    cycles(qp) = [number of p-cycles disjoint from U] + cycles(q|U · ρ_U).

Proof: cut every p-cycle meeting U immediately before its marked vertices. Starting at u∈U, follow the unchanged p-segment to the next marked arrival ρ_U(u), which q sends to qρ_U(u). Concatenating these segments gives a bijection of cycles meeting U with cycles of qρ_U. The disjoint cycles are untouched. Taking U to be the union of selected columns and q=∏V_j^−2 gives a literal finite normal form and includes repeated encounters with the same original cycle. If one column meets k distinct p-cycles, its k-cycle multiplier merges all k into one. If several marked vertices lie on one p-cycle, the cut formula, rather than a connectivity claim, decides splitting.

On the uniform side this is subsumed by the source's return map: let E=(e_0<…<e_{w−1}), Ω(e_a)=e_{a+k−1}, and τ_E be first return of x↦x−(k−1) modulo n to E. Tour existence is equivalent to E meeting every residue mod g AND Ωτ_E being a w-cycle (ancestor Lemma 4.9). The target's row-reversal convention yields the conjugate ordering τ_EΩ. Its diagonal map is p_E(x)=Ω(x)−(k−1) for x∈E and x−(k−1) otherwise. The executable verifies source-coordinate consistency against the full board. This is an exact known bridge, NOT a new result.

Missing universal selection: for every odd k≥3 and odd n with k<n≤2k−1, find E meeting all g residues with Ωτ_E one cycle. With uniform-side propagation this would prove every larger n. The interesting residual regime is g≥3 with gcd(g+1,k−1)>2 after removing other public classes, not just g=1. For example n=15,k=13 has g=3 and gcd(4,12)=4; a contiguous E of length7 works, but k=13 was already public. For k≤99 the interval diagnostic found at least one odd interval length in every tested g>1 base case. These are known finite ranges and no universal interval lemma follows. A statement restricted to intervals is stronger than what the source asks and remains unproved. A proof merely rederiving Lemma 4.9 or the source block constructions should be excluded candidly.

## Mechanism B: mixed row/column switches and overlap

Let I,J be reversed row/column sets. With positive H,V fixed, put

    A_i=V H_i^(−2) V^−1,  B_j=V_j^(−2).
    T_{I,J}=(∏_{j∈J}B_j)(∏_{i∈I}A_i) T0.

This follows directly by factoring V_J H_I; the order of the two products is essential. The A_i have disjoint supports V(row_i); the B_j have disjoint column supports. A_i and B_j share exactly ONE point when (i,j) is occupied, and none otherwise: V preserves column and is injective. Thus two mixed generators require at most 2k−1 marked vertices, and the same cut formula gives their exact cycle effect with q=B_j A_i. Replacing this by a pair of disjoint switches is invalid. This normal form covers all 2^(2n) allowed orientations without enumerating them, but does not prove that one of these fixed-order products is a full cycle.

The executable also uses the current-state formula: toggling positive row i left-multiplies by V_C H_i^−2 V_C^−1 (and the inverse multiplier for a currently negative row); column toggles similarly use exponent −2 or +2. Hence supports for an evolving row switch depend on current column signs. A group-generation argument allowing arbitrary words in fixed A_i,B_j would not respect this binary orientation constraint.

Sustained diagnostic: steepest strictly decreasing single-switch descent gets trapped at R={0},C=∅, with three cycles, for (n,k)=(9,7),(15,13),(27,25),(33,31). Every single toggle was checked there. A paired toggle of row1 and column2 escapes each to a full tour. Extending the apparent triple gadget by R={0,…,g−2}, C={2,4,…,g−1} FAILS: for (15,11), g=5, it has THREE cycles, and for (21,15), g=7, SEVEN cycles. Full permutations are reproducible from mixed.py. These are exact failures of a proposed construction, not counterexamples to tour existence. The pattern R={0,1},C={2} had g−2 cycles throughout the separate n≤65,g≥3 diagnostic; no all-n proof of that pattern is asserted, and g=3 alone would not settle the target.

Remaining mixed lemma: for every odd n>k≥3 in the residual regimes, select binary I,J such that the displayed fixed-order product has one nk-cycle, or prove a descent/interface induction that preserves this form and always reaches one cycle. No proof that two-switch descent has no traps, or that the triple gadget chains universally, is available. Auxiliary support connectivity does not supply this lemma. Both normal forms are elementary permutation identities subject to strong classical/subsumption objections; neither is a discovery nomination.

## Disposition

HOLD, no PROOF.md. The full ordinary endpoint remains unresolved; no counterexample certifies all orientations. Preserve the cut formula and mixed-support intersection mechanism as research notes, preserve the failed chain, and require a genuinely universal selection or interface lemma before more verification or formalization. No Lean or manuscript work is warranted. Counts remain 9 additional /39 total /next40, controlled solely by root.
