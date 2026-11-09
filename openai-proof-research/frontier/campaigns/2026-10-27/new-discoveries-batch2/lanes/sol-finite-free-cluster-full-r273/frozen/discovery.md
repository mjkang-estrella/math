# Mathematical work and exclusions

No discovery credit requested. Fourteen distinct attributed families were screened against actual source bodies. No Lean, manuscript, shared ledger or public state was changed.

## Completed historical endpoint: annihilation

Let d(A)=Σ_(v∈A)deg(v), e(A)=|E(G[A])|, m=|E(G)| and α be the independence number. For every partition V=A⊔B,

    d(A)=m+e(A)−e(B).

An annihilating set satisfies d(A)≤m. Every independent set is annihilating, so h≥α.

**Mechanism A, degree-tail/complement obstruction.** In the source KE/α=3 setup, n=α+μ≤6. If h≥4 choose four vertices A of smallest degrees with d(A)≤m. Since α=3, e(A)≥1. Its complement B has at most two vertices, hence e(B)≤1; the identity forces e(A)=e(B)=1 and therefore n=6. Deleting one endpoint of A's unique edge leaves an independent set S of size3. S is maximum and S can be extended to the annihilating set A, contradicting the literal maximality hypothesis. Thus h=3. This handles all finite orders via the KE size bound; it is not an inference from sampled orders.

**Mechanism B, arbitrary-cover saturation.** More generally suppose τ=n−α≤3 and every maximum independent set is maximal annihilating. If h>α, take ANY annihilating A of sizeα+1. Then B has sizeτ−1≤2, e(A)≥1 and e(A)≤e(B)≤1. Thus A has exactly one edge. Deleting one endpoint produces a maximum independent set contained properly in an annihilating set, contradiction. This proves the general small-vertex-cover lemma without connectivity or matching assumptions. The source endpoint follows from τ=μ≤α=3. This route identifies the exact obstruction directly rather than classifying six-vertex graphs. It is closely related to A and is not claimed as independent novelty.

**Capped exact diagnostic.** check.py enumerates all 33,864 labelled simple graphs on orders3–6, filters connected/α=3/KE, and tests every maximum independent set with exact integer degree sums. The hypothesis holds on 4,350,11760 graphs at orders4,5,6 respectively; all have h=3. No floating-point roots, random sampling or limit inference. This finite check motivated the structural argument; the displayed argument proves the universal endpoint.

**Decisive historical exclusion.** The arXiv2019v3 body still calls this Conj6.1. The actual 2020 journal PDF, DOI10.26493/1855-3974.1950.8bd, Proposition3.1 pp366–367, already proves the full source endpoint. Its n=6 proof uses the same four-lowest/two-highest complementary-edge argument. This is a complete source-method bridge, not an exclusion based merely on proof length. The 2022 follow-up Introduction expressly says the conjecture is true for KE graphs with α≤3 and cites the2020 paper. Therefore no candidate survives; the small-cover formulation is not separately nominated. The 2023/2026 gap-bound papers were inspected as comparisons but are unnecessary to this exclusion. The 2023 v1 Lemma4.1 has a printed ≤ where its proof concerns equality; no reliance on that malformed statement.

## Sustained fresh lead: Leake–Ryder Conjecture2.5

Literal endpoint and quantifiers appear in SCOUTING item11, with ⊞ normalized by 1/n! as in source §1. No proof for all degrees is claimed. The actual source proves largest-root submodularity and two-input majorization, not the interior-index four-tuple assertion. A naive common Hermitian matrix representation cannot transfer the desired inequality: source §2's diagonal example A=B=diag(2,0), C=diag(0,2) gives 6≤4, false. That shortcut is excluded before the mechanisms below.

**Mechanism1: exact two-root geometry.** Translation invariance removes the root means for n=2. Write p=x²−a², q=x²−b², r=x²−c², a,b,c≥0. Their pair convolutions are x²−a²−b² and the triple is x²−a²−b²−c². For j=k=i=1 the stronger l=1 inequality is

    √(a²+b²+c²)+c ≤ √(a²+c²)+√(b²+c²).

Both sides are nonnegative. Their squared difference (right minus left) is twice [√((a²+c²)(b²+c²))−√(c²(a²+b²+c²))], nonnegative because the radicand difference is a²b². For j=2,k=1,i=2, the stronger choice is l=1 and the assertion becomes √(a²+c²)+c≤√(a²+b²+c²)+√(b²+c²), immediate by the two separate monotonicities. The exchanged j,k case is identical; i=2,j=k=1 only weakens the left side. These exhaust admissible n=2 indices; n=1 is equality. Repeated roots and zero variances are included. This is an exact low-degree mechanism, not a universal reduction and not a nomination.

**Mechanism2: derivative flow and the multiple-root obstruction.** Let q_ε=∏_(s=1)^n(x−εu_s), with Σu_s=0, and c=Σu_s²/[2n(n−1)]. For n≥2, coefficient comparison in the defining convolution gives

    f ⊞ q_ε = f − c ε² f'' + O(ε³).

For a simple root λ_t of f, implicit differentiation gives

    λ_t(f⊞q_ε)=λ_t(f)+c ε² f''(λ_t)/f'(λ_t)+O(ε³)
               =λ_t(f)+2c ε² Σ_(s≠t)1/(λ_t−λ_s)+O(ε³).

The coefficient identity is polynomial-exact to the displayed order; the root expansion assumes fixed simple roots. Applied to f=p⊞r and f=r it gives an explicit necessary second-order inequality whenever the ε=0 four-tuple is tight. For the largest-root pattern it recovers a familiar barrier comparison rather than proving interior control. For generic distinct roots most interior patterns have a strictly positive zeroth-order slack, so this perturbation cannot decide their global sign. At repeated roots the denominators diverge and the analytic expansion is invalid. Passing to such collisions by substituting a zero gap is not a proof. This identifies a concrete remaining calculation: obtain a uniform cluster/Puiseux expansion, including root-index assignment, for r with two or more repeated clusters and a second nontrivial factor p. No such estimate was proved here.

These are two different analytic mechanisms beyond the failed matrix shortcut. Neither resolves all n or the universal quantifiers. The n≤2 endpoint is not credited. No expanded numerical root sweep was used.

## Access, prior status, chronology

Source metadata slice was submitted November2018, capped at100 entries; it is not a complete monthly bibliography. Versioned PDFs and API publication/update dates are retained. The 2019→2020→2022 annihilation chronology is substantive: the published proof supersedes the old conjecture label. Taranenko's2018/2020 question is refuted in the2022-submitted/2023-updated primary successor. Live retrieval timestamps are in access.jsonl. Original response bytes were copied and hash-checked before scientific reading; unchanged local originals/copies and reused history are checked again at close. Administrative files are snapshots only; no equality with a moving ledger is demanded.

Current GitHub proof-registry HEAD is unknown, with previously denied API/raw/codeload/diff/patch routes parked without further requests. The pinned fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb is historical only. No new registry clearance is inferred from old hashes. ScienceDirect and Google challenge routes likewise remain parked. Lawful arXiv, Crossref, Springer and the journal's linked PDF were used; no browser/proxy/TLS bypass. The finite-free author query returned irrelevant homonyms and the narrow Horn query returned no entries; these are weak searches, not novelty certificates. A specialist prior-art comparison remains a gate before any significant continuation or nomination.
