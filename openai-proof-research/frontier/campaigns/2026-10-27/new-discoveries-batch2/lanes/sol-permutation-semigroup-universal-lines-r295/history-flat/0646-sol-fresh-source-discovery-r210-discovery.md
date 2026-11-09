# r210 — four-color caterpillar reconstruction remains unresolved

One attributed target, fresh to the bounded target-specific report screen, was sustained: Bingham–Celano–Commins–Orellana–Pan–Simone, *Principal specializations of the t-chromatic symmetric function*, arXiv:2610.31785v1, Conjecture 6.1, printed p25. Zero full nominations. No PROOF.md, Lean or manuscript. Root alone accepts/counts/stages; administrative snapshot counts are 9 additional / 39 total, next40.

## Literal source and chronology

For EVERY pair T,T' of finite simple undirected caterpillar trees, equality in Z[q,t] of

P_T(q,t)=sum over proper colorings k:V(T)→{0,1,2,3} of q^(sum_v k(v)) t^(number of colors used)

must imply T≅T'. This is ps4(Z_T(x;t)), with x=(1,q,q²,q³,0,…). No bound on order, spine length, leaf multiplicity or positivity of every internal leaf count is permitted. It is not merely the full chromatic-symmetric-function theorem, a three-spine theorem, or an invariant evaluated at numeric q. Conjecture 6.2 sets t=1 and is stronger; it is not a separate fresh slot here. Conjectures 6.3/6.4 are not pursued. For a canonical spine with at least two vertices, a=(a1,…,al) has positive integral entries, endpoints at least2, and ai−1 leaves attached at spine vertex i. Its order is sum ai. Isomorphism is equality up to reversal. One-spine stars and the trivial one/two-vertex cases are handled separately, not discarded.

Actual latest abstract https://arxiv.org/abs/2610.31785 lists only v1, submitted 22 October 2026 18:22:33 UTC. Actual body https://arxiv.org/pdf/2610.31785 identifies v1, with internal date October26. DOI identifier 10.48550/arXiv.2610.31785. No journal version authenticated. Frozen PDF SHA256 e8149d1ea1136ffbfe4120c76e6f4cf87ff2ed81983ca4a2bce91bd4f49fc918. Read introduction, Definitions2.1/2.7/2.9, Section3 definitions and specialization discussion, reconstruction statements/algorithm explanations in Sections4–5, and all Section6. The lengthy coefficient case proofs in the appendices were not fully audited and are not relied on as premises in the reduction below. The two literal ps3 collision pairs in introduction and Section6 are independently checked.

## Closest actual classical proof and applicability

Loebl–Sereni, *Isomorphism of Weighted Trees and Stanley's Conjecture for Caterpillars*, actual latest https://arxiv.org/pdf/1405.4132 is v4, 13 June2018; abstract https://arxiv.org/abs/1405.4132 lists v1 May16 2014, v2 June20 2016, v3 March28 2017, v4 June13 2018. PDF SHA256 a8bea837f9e42103ca916be2990032e62fe98b7df6fbf8af3fa32ac683c60091. Target bibliography gives AIHP D6(3)(2019)357–384; journal body not independently obtained/compared. Read definitions and Theorem2, the shape/partition reconstruction framework in Section3, Section4's two-end inductive reconstruction and its distinguishing partition choices, and Section5's shaped-partition inclusion-exclusion procedure. This is a close actual proof body, not a claim of exhaustive nearest literature.

Their input is the full U polynomial, equivalently for every partition λ of N the count of edge-deletion partitions with component-order multiset λ. Procedure1 removes non-shaped partitions using all smaller shapes and their partition data. Theorem2 grows the two rooted spine ends; if candidate ends are nonisomorphic, induction selects an expression E distinguishing their U coefficients. If rooted ends are isomorphic with different roots, it looks ahead one or two stages and uses shaped counts θ_s(T,[E,1]) to distinguish extensions. Those arbitrary expressions E are inputs, not quantities recovered in that proof from four colors. Consequently its exact all-caterpillar scope does not itself supply the required input-decoding lemma here.

The complete standard specialization bridge is as follows. Expand the indicator that every edge is properly colored as ∏_(uv∈E)(1−1_(k(u)=k(v))). For each A⊆E the equality constraints make the color constant on every connected component C of (V,A). Summing over its independent four choices gives

P_T(q,1)=Σ_(A⊆E)(−1)^|A| ∏_(C component of (V,A)) (1+q^|C|+q^(2|C|)+q^(3|C|)).

For a tree, every connected-partition pattern with r parts has |A|=N−r and is counted in U. Thus the full U polynomial supplies this ordinary specialization exactly. Keeping t requires recording the union of colors across components; a used-color mask supplies it exactly. The bridge runs FROM full partition data TO the specialization. No converse follows. More concretely, if D_t multiplies each monomial by t to the power of its support size, then for N≥5 the nonzero symmetric function f=e5·e1^(N−5) satisfies ps4(D_t f)=0, since every monomial has at least five distinct variables. This proves that a generic linear inverse on symmetric functions is impossible. It is NOT a difference of two caterpillar invariants, so it does not refute the conjecture or rule out a class-specific inverse. No exclusion based on shortness or complete classical subsumption is asserted.

## Sustained exact route and missing universal lemma

For U⊆{0,1,2,3}, put F_c(U)=Σ_(d∈U,d≠c)q^d and define

H_a(U)=Σ_(c1,…,cl∈U, ci≠c_(i+1)) ∏_(i=1..l) q^ci F_ci(U)^(ai−1).

This is an identity for EVERY allowed composition: first assign the spine colors; each leaf chooses any other color independently. It can be evaluated by a transfer vector with l steps and diagonal weights q^c F_c(U)^(ai−1), using the off-diagonal all-ones matrix between steps. It also holds for a one-spine star. For j=1,…,4, define

J_j(a)=Σ_(S⊆{0,1,2,3}, |S|=j) Σ_(U⊆S) (−1)^(j−|U|) H_a(U).

Inclusion-exclusion over omitted colors proves J_j(a)=[t^j]P_(C_a). Each coloring with exact used-color set S contributes once, and all colorings missing any S-color cancel. Thus these four scalar polynomial invariants encode exactly the target. This is a universal ordinary derivation, not a numerical inference.

The exact missing rigidity lemma is: for EVERY two canonical caterpillar compositions a,b (and the star/trivial cases), if J_j(a)=J_j(b) for all j=1,…,4, then b=a or reverse(a), with the corresponding trivial isomorphisms. A sufficient stronger alternative is decoding all U coefficients from the J_j's and then invoking the actual classical Theorem2. Neither lemma is proved. Mere invertibility of individual transfer matrices, nonnegative coefficients, full-U reconstruction or agreement at finitely many q values does not establish scalar-product rigidity.

Some information is uniformly recoverable. For a nontrivial tree with bipartition sizes A,B>0 and N=A+B,

[t²]P_T=Σ_(0≤c<d≤3)(q^(cA+dB)+q^(cB+dA)).

Every connected bipartite graph has exactly two proper assignments to any fixed two-color set: choosing one color at one vertex forces all other colors along paths. This proves the formula including A=B and its multiplicities. Its minimum exponent is min(A,B) and its maximum is 3N−min(A,B), because all coefficients are positive and colors range0..3. Their sum recovers3N, hence the unordered bipartition sizes. Alternatively P_T(1,1)=4·3^(N−1), by coloring a root then its children, recovers N for every tree including N=1. These facts do not order the leaf multiplicities along the spine. They are supporting classical consequences, not nominations.

The known ps3 collision a=(2,1,3,3), b=(3,1,2,3) is resolved by ps4 at [q7 t3], with coefficients114 and110. The Section6 pair (3,4,2,3),(4,2,3,3) is resolved at [q8 t3], coefficients232 and228. They show why merely recycling a three-color decoder is inadequate, not why a four-color decoder exists universally. In fact the coefficient [t3] at ps4 mixes surjective colorings on four different three-color subsets; the ordinary ps3 value is just one of those contributions. No inverse separation of that mixture was proved.

## Exact checks and strongest eligibility objections

checks.py uses integer dynamic programming with state (current spine color, used-color mask, exponent). Leaves retain the spine color in the state; spine steps require a different next color. It exhausts all canonical caterpillars of orders3..11: 286 total, with per-order counts1,2,3,6,10,20,36,72,136. No ps4 collision. Direct enumeration of all vertex colorings independently checks22 caterpillars through7 vertices. Independent spine sums plus subset Möbius inversion check42 through8 vertices. Both source ps3 collisions are verified. Reversal invariance and the total 4·3^(N−1) are controls. These are below the source's reported computational range25, not new evidence claiming expanded coverage. No random or floating arithmetic is used.

The strongest objections are decisive: the universal rigidity/decoding lemma is missing; current complete public registry bodies/heads and chronology are not authenticated; a related historical citation passage already mentioned principal specializations of caterpillars; and actual closest journal-version comparison is incomplete. Target-specific report freshness is narrower than bibliographic first appearance. Generic symmetric-function kernel examples are method obstructions only. Finite checks and classical reconstruction do not solve the literal conjecture. Outcome: unresolved, zero nominations.

## Bounded history and access

history.json refreshes1,580 inherited qualified original/report paths from r207/r208 canonical layers plus immediate top-level reports. Only38 reports need local snapshots; unchanged paths reference explicitly supplied canonical snapshots, independently hash checked. The initial resolver overlooked r208's canonical_copy field and temporarily duplicated files; those redundant lane copies were removed after correcting the resolver. No equality-of-bytes provenance inference was made. Actual r111–113 ORIGINAL paths remain. Corrected older indexes are separately path/hash bound in reference-bindings.json. alias-refresh.json refreshes2,578 inherited reference aliases separately, zero changed, never promoted to original provenance. Administrative ledger/NEXT/prior context are snapshots only, not scientific premises. All requested root205–208 decisions and206/208 SUMMARY/discovery were read;207 was additionally consulted. Newly indexed reports were inspected for dispositions and exact target aliases. This bounded layered screen cannot clear all history or parked intervals.

Exact arXiv/DOI/title and author/statement aliases yield no target resolution in these bounded report layers. Celano hits concern parking-function displacement at r80; the caterpillar hit in sol-steiner-gp-fixed-gap-closure-r3 is an unrelated registry semantic-screen passage. This latter hit prevents claiming that the topic has never appeared in any historical material. The exact current arXiv search for t-chromatic returns the target plus lexical false positives, not a resolution certificate. Maximum-triangle reconnaissance hits screened r193 and was stopped; downloaded bytes retained unused. Feinsilber's full5-page regular-bisection body was read: it proves its d≥5 construction and does not state a fresh quartic conjecture, so no unattributed quartic target was invented. Its public results are reconnaissance, not new nominations or independently audited exclusions.

GitHub API/raw/codeload/diff/patch, ScienceDirect and Google challenge routes remained denied and were not retried. No parked history intervals, proxies, TLS disabling, browser, messages, posts, uploads or MathDB writes. Current registry completeness remains a gap rather than being replaced by cached history. Retrievals used the prescribed guard, byte cap12,000,000 and timeout35s, with threads1 and bytecode disabled; actual timestamps are October30 UTC, despite the session's October29 local calendar label. Source originals were written, hashed, copied and verified before extraction/body reading; final separate verification rechecks them. Sampled RSS does not exclude unsampled transients. Failure details are retained. No shared edits, git or count changes.

finalmanifest.json explicitly excludes itself and verification-receipt.json. The separate guarded verifier checks source/guard original-copy bindings, canonical/index snapshot references independently, exact checker replay and every delivered manifest entry; mutable report drift is reported separately and never converted into a scientific binding.
