# Ordinary manuscript review: MathDB 369163

**Qualified ordinary-paper PASS, with minor corrections listed below.** The main crown theorem, its actual printed lower-bound derivation, every quartic construction, and both low-degree ideal equalities are mathematically correct. No fatal mathematics or unresolved main-proof obligation was found. The manuscript is not yet a clean source-faithful final copy: F01 and F05–F07 in particular should be corrected. These repairs do not change the main theorem or require a new mathematical argument.

This review is solely ordinary mathematics and manuscript/source fidelity. Formal endpoint **PENDING**, Lean/certificate/replay not reviewed; no acceptance recommendation or campaign credit. Supplied count **52/60**, candidate credit **0**, unchanged. The status statements are assessed against frozen evidence, not current active work.

I read all nine pages as extracted mathematical text, checked the corrected PDF extraction byte-for-byte against corrected-paper.txt, and compared the full normalized ordinary proof. The root's completed nine-page visual inspection is relied on; I did not repeat rendering. The corrected generator diff has only the authorized rendering/typographic/cross-reference changes. The author coverage map was not used as a substitute for rederiving proofs. See OBLIGATION-AUDIT.md and the keyed review.json for all 22 independent obligations.

The decisive full-side argument is sound: only pure-opposite-side multigraded components need testing; supports of size at most two give zero contraction after deleting a supported index, and support three at degree at most three forces two nonassociate primitive irreducible minors to divide the component in a polynomial UFD. Their degree-four product cannot divide a nonzero cubic. This works in every field, including characteristic two. It neither assumes factoriality of a determinantal quotient nor infers a degree bound from radicality. All other families were checked on arbitrary multigraded components, including powers and cancellations. The separator equivalence gives exact element colons; distributing colon by an ideal gives (J:P_tau)=intersection of the other distinct primes, and hence the added degree-zero-through-three equalities as printed.

## Actionable findings

### F01 — source/definition drift

p. 2, Definition 2.3. Severity: minor; correct before final paper.

The generic definition restricts d >= 1 although the source takes the least homogeneous degree. For I=P homogeneous prime, f=1 has (I:1)=P and the source invariant is 0. The printed generic definition instead gives 1 in a polynomial ring with a suitable linear element outside P. Crown J is not prime, so its result is unaffected.

Minimal correction: Use d >= 0 (and f nonzero), then retain the crown-specific exclusion of constants in Remark 3.2.

### F02 — mathematical prose typo

p. 2, Theorem 2.4 proof. Severity: minor.

The paired cut T=A union its matched B vertices is V minus {ai,bi,aj,bj}. The text instead says its complements are V minus those four vertices. This reverses the cut and its complement; the displayed Mij ideal is correct.

Minimal correction: Replace whose complements are V minus ... by which are T=V minus ..., or say whose complements are {ai,bi,aj,bj}.

### F03 — proof exposition

p. 2, Theorem 2.4 primality explanation. Severity: minor.

The rank-one explanation describes a single determinantal block, but Mij has two disjoint edge blocks. Using one common pair s,u for both blocks would impose extra minors. The cited general completed-component theorem already supplies primality, so no main-proof dependency is missing.

Minimal correction: Say each block uses independent rank-one parameters, with independent coordinates for isolated vertices; the resulting disjoint-block quotient embeds in one polynomial ring. Or rely explicitly on [1] for primality.

### F04 — mathematical prose typo

p. 5, Proposition 6.1, three-vertex case. Severity: minor.

The sentence says ai and bj belong to Y minus {bi}. The vertex ai is in X. The required containment is nevertheless true because both vertices belong to {ai} union (Y minus {bi}).

Minimal correction: Replace since ai and bj in Y minus {bi} lie in the block with since ai and bj lie in {ai} union (Y minus {bi}).

### F05 — source/claim drift

p. 8, Section 10, source paragraph. Severity: minor; correct before final paper.

The module identity in the actual frozen crown Lemma 5.7 is cited from its reference [2], Proposition 4.2: Cooper, Seceleanu, Tohuaneanu, Pinto and Villarreal, Generalized minimum distance functions and algebraic invariants of Geramita ideals. It is not cited there from manuscript [7] Mohammadi-Sharifan. That latter reference concerns a different colon lineage; the printed attribution is unsupported by the retained passage.

Minimal correction: Say [3, Lemma 5.7] uses the module identity, citing Cooper et al., Proposition 4.2; either add that bibliography entry from the frozen crown reference list or omit the lineage clause. This manuscript proves the identity directly, so no new source retrieval is needed.

### F06 — missing hypothesis in prior-result explanation

p. 8, Section 10, two-component paragraph. Severity: minor source-comparison proof gap; no main-theorem impact.

A connected dominating set of the star component alone need not contain two leaves: {ai} already dominates that star. The actual [4, Definition 4.6/Theorem 4.15] requires A intersect Vi to dominate G[Vi union T], including deleted vertices. The manuscript omits that constraint while asserting the 3+1 computation.

Minimal correction: State the constrained definition. In Q_i, the star-side subset must contain ai to connect/dominate the star, and at least two leaves bj,bk: with only bj, deleted aj is undominated. Two distinct leaves suffice to dominate every deleted al. The isolated bi dominates all deleted al. For Mij each edge requires both endpoints to dominate deleted vertices on both sides. Thus 3+1 and 2+2 are correct.

### F07 — overprecise witness attribution

p. 1,2,6,8,9, Abstract; strategy; Section 8 preamble; Section 10 provenance. Severity: minor.

The blanket description of every displayed witness as an explicit construction of [3, Proposition 5.2] is too precise. That proposition handles P0 by the connected-domination equality, without displaying this monomial. The monomial support {a1,a3,b1,b2} is the connected dominating set in [3, Lemma 5.1], and the monomial construction is supplied by [2, Proposition 3.6]. The Ri witness printed here also uses y instead of the x-only source choice, a harmless coordinate symmetry.

Minimal correction: Describe the nonempty-cut witnesses as the constructions of [3, Proposition 5.2], up to relabeling/coordinate symmetry; attribute P0 to [3, Lemma 5.1] and the connected-domination construction of [2]. None is new.

### F08 — cosmetic/proof-boundary

p. 4,5, Propositions 5.1 and 6.1. Severity: cosmetic.

A proof-ending square appears after only the first paragraph in each proposition although essential cases follow. Proposition 6.1 also uses xaa/aa where a coordinate pair at an X vertex is intended; membership forces positive vertex degree, not specifically positive x exponent.

Minimal correction: Move each square to the actual end of its proof. Say some vertex of X has positive vertex degree. Optionally repair the awkward preimage sentence in Proposition 5.2 by writing sigma(f) satisfies the PX hypothesis, hence sigma(f) in PX and f in PY.

### F09 — source hypothesis precision

p. 8, Section 10, Theorem 3.5 comparison. Severity: minor.

The required radicality in [4, Theorem 3.5] is that of J_G + J_transversal, not radicality of the colon itself. Here (J:P_tau) is an intersection of primes, hence already radical; conflating the two can obscure the actual missing bridge.

Minimal correction: Replace radicality hypothesis on the colon with radicality of J_G + J_transversal, whose identification with the colon is the missing equality step.

## Source and qualification boundaries

The actual frozen crown journal definition, cut classification, Proposition 5.2, Conjecture 5.6 and Lemma 5.7 were checked in relevant passages. Herzog et al. Corollary 2.2 and Section 3 provide the ordinary structural dependency in arbitrary characteristic. The older Liwski journal Definition 2.3, Definition 4.6, Theorems 3.5 and 4.15 identify the precise two-component and constrained-domination scope. The newer v2 H and transversal bounds, and Shen–Zhu Setting 4.1/Theorem 4.12, were checked for applicability. These are primary statement/passage comparisons, not an independent audit of every lemma in those papers. The connected-domination monomial construction was checked in its frozen Proposition 3.6. No new literature was fetched.

Section 10 otherwise preserves the correct bounded distinction: known empty/mixed/source witnesses and complex two-component cases do not establish the full-side lower bound over all fields. The uniform endpoint depends on the newly supplied obstruction; no complete already-known theorem bridge was found in the supplied inspected comparisons. This does not establish worldwide priority. The root qualification supersedes older reports' unread-journal/access HOLDs within its stated limits. Automatic institutional access is not open licensing; HTML date provenance and bounded correction/citing/registry coverage stay qualified. No new source chase or administrative decision was made here.

## Process and integrity

The first command was timeout Python -I -B, set actual affinity to CPUs 0,1, CPU5 seconds and AS512MiB before any instruction read. Subsequent commands used the same affinity/AS limits and CPU at most10 seconds, wall at most20 seconds (stricter than CPU120/wall140/AS6GiB). Shell/timeout wrappers themselves are not claimed to have inherited the Python-only resource caps. All exec returns were synchronous successful exits; the one pdftotext child was timeout-bounded, inherited limits and was joined. There are no background tasks from this review. Early per-command rusage was not measured and is recorded as unavailable, never reconstructed from estimates.

All 155 frozen paths matched before mathematical reading and after review. Only exact manifest entries and applicable instructions were read; no protected active lane was read, globbed, hashed or polled. All writes are in this review lane. No children, Lean, solver, mathematical enumeration/numerical search, git, network/browser, install, contact or publication actions occurred. Hash processing is integrity checking, not semantic reading. See frozen-before.json, frozen-after.json, process-receipts.json, read-inventory.json and output-manifest.json.
