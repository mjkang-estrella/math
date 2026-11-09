# Independent preliminary review — four-attractor conjecture

Decision: **INVEST**, with **HOLD on acceptance/novelty clearance**. SOURCE: PASS for the literal full-domain refutation. MATH: PASS in ordinary finite mathematics. SUBSTANTIVE: favorable, classical-method objection retained but no complete known-result/source bridge established. NOVELTY: bounded HOLD. FORMAL-FEASIBILITY: favorable, unrun. No acceptance or counting action: 9 additional / 39 total / next 40; root alone decides.

## Source scope

I read independently frozen primary bodies, rather than adopting the root's exact-check output. Dvořáková–Hendrychová, *String attractors of Rote sequences*, arXiv:2308.00850v5, §2 p.2, Definitions 1 and 3 p.3, Theorem 8 pp.5–7 and §7 p.15, support precisely the proposed target. The attractor condition covers **every nonempty factor**, with an occurrence inside the finite word containing a selected position. Positions are zero based in this source and review. Minimal means minimum cardinality here, not merely inclusion-minimal.

Definition 3 allows every infinite binary letter directive and every infinite directive over {E,R}. Definition 1 makes E reversal followed by complement, not complement alone. There is no global normalization, recurrence, or aperiodicity hypothesis. The aperiodicity and forbidden adjacent directive conditions in Theorem 15 belong to the standard CS Rote subclass. Theorem 16 is an aperiodicity criterion, not a prerequisite in Definition 3. Theorem 8 concerns the pure-E pseudostandard subclass starting in 0; it cannot be applied to the last R step of this witness. Its three-position bound is consistent with the first four closures here.

Section 7 explicitly conjectures the bound four for pseudopalindromic prefixes w_n of **binary generalized pseudostandard sequences**. It does not restrict this sentence to Rote, Sturmian, pure-E, or Thue–Morse sequences. The candidate is a defining w_5, not just an arbitrary factor or prefix. Thus the counterexample addresses the intended mixed-closure object, not a weakened domain.

The current arXiv landing page retrieved 2026-10-30 still identifies v5 (15 September 2024). The journal's live article page, DOI 10.46298/dmtcs.12385, links the exact v5 PDF; its downloaded bytes have SHA256 7c2b716e0067fa4bbd85640d8c849b93ae87eed59998e1b3e8bdf5a11ecfaacb, matching the frozen scientific source. The journal reference is DMTCS 26:3 (2024), article 2; the current arXiv journal-reference field dates publication 4 November 2024. This correspondence uses the journal's linked body, not metadata as proof. No later correction or universal clearance follows merely from these pages.

## Word construction and infinite admissibility

Let R reverse a word and E reverse and complement it. Starting with ε, append 00101 and close with EEEER:

|step|word after closure|longest fixed suffix before closure|
|---|---|---|
|1|01|0|
|2|0101|2|
|3|0101100101|0|
|4|010110010101100101|4|
|5|010110010101100101101001101010011010|2|

For input s=vx, with x its longest suffix fixed by the chosen antimorphism θ, the shortest closure is sθ(v). To see minimality directly, a shorter θ-palindrome extending s would have length L with |s|≤L<2|s|−|x|. The overlap of s with its reflected copy would give a θ-fixed suffix of s of length 2|s|−L>|x|, a contradiction. Our checker tests every suffix length, including the empty suffix, and verifies every displayed output. The final word w is a palindrome of length 36.

For an explicit admissible infinite extension take Δ=00101(0011)^ω and Θ=EEEER(ER)^ω. Each closure preserves the previous word as a prefix, and appending a letter increases length by at least one. Therefore the nested words define an infinite binary sequence u, satisfying Definition 3, whose w_5 is exactly w. Both letters and both antimorphisms recur infinitely in this extension. Even aperiodicity can be secured: in the tail, each fixed θ_n occurs with both possible following letters δ_(n+1) infinitely often, so no eventual bijection f from Theorem 16 exists. Aperiodicity is unnecessary for the §7 refutation, but this removes that potential objection without silently assuming it. Normalization of a directive, if desired elsewhere, does not remove the intrinsic fact that w is a pseudopalindromic prefix of u; Definition 3 itself does not demand it.

## Independent finite proof

For nonempty f define C(f) as the union of the occupied positions of all its occurrences in w. The source attractor condition is equivalent to Γ∩C(f)≠∅ for every nonempty factor f. In particular it implies this condition for the eleven factors below. Exact starts are included so that the finite occurrence assertions are explicit; testing every start 0≤i≤36−|f| verifies there are no omitted occurrences. Intervals are inclusive.

|f|all starts|C(f)|
|---|---|---|
|001010|5|[5,10]|
|010101|6|[6,11]|
|101011|7|[7,12]|
|001011|13|[13,18]|
|101101|15|[15,20]|
|110100|17|[17,22]|
|110101|23|[23,28]|
|101010|24|[24,29]|
|010100|25|[25,30]|
|1100|3,11|[3,6]∪[11,14]|
|0011|21,29|[21,24]∪[29,32]|

Suppose Γ has at most four positions and is an attractor. Since the universe has 36 positions, extend Γ to exactly four distinct positions. Supersets preserve the attractor property; thus disproving every four-set also disproves sizes zero through three. Put A=[5,12], B=[13,22], C=[23,30]. Rows 1,4,7 force a point in each of these disjoint blocks. If a block has only one selected point, its three six-letter constraints force that point into A₀=[7,10], B₀=[17,18], C₀=[25,28], respectively. With four total points, the only block-count possibilities are (1,1,1), (2,1,1), (1,2,1), (1,1,2). In the first case the fourth point lies **outside A∪B∪C**, and is fully allowed in the argument.

* (1,1,1): the three block points avoid both C(1100) and C(0011). Those two coverages are disjoint, so the one remaining point, wherever it lies outside the blocks, cannot meet both.
* (2,1,1): both A points and the single B₀,C₀ points avoid C(0011).
* (1,1,2): both C points and the single A₀,B₀ points avoid C(1100).
* (1,2,1): the A₀,C₀ points avoid both short-factor coverages. Hence a B point must lie in [13,14] to meet C(1100), and another B point must lie in [21,22] to meet C(0011). Neither B point lies in [15,20], and neither A₀ nor C₀ meets [15,20]. Thus row 5 is missed.

Every case contradicts a necessary occurrence constraint. This is an ordinary universal proof over all possible four positions, not a heuristic optimizer output. It proves γ(w)≥5 and already refutes the full §7 universal bound. The independent `check.py` reconstructs the word, tests all suffixes and starts, and exhausts all binomial(36,4)=58,905 four-sets using the eleven constraints. It also checks Γ={5,10,18,21,28} against every one of the 500 distinct nonempty factors, proving γ(w)≤5. The optional exact optimum assertion is therefore independently verified. No sharp bound for the entire family, asymptotic construction, or minimal counterexample length is asserted or needed.

## Closest primary bodies and strongest objection

**Dolce, WORDS 2023 pp.117–129, DOI 10.1007/978-3-031-33180-0_9.** The previous lane had not read this body. This review obtained the actual 13-page publisher PDF, froze it before extraction, and read Theorem 1, Example 5, the proof in §4 (explicit Step 1, subsequent cases/tables), and §5. Theorem 1 constructs attractors of size at most five for every nonempty finite factor of the infinite Thue–Morse word. Example 5 exhibits a 50-letter factor with minimum five. Its displayed word is neither a palindrome nor an antipalindrome (checked literally), so it is not itself a source pseudopalindromic prefix. The proof transfers canonical-block attractors and moves/adds boundary positions within Thue–Morse factors. It does not prove a size-five lower bound for a mixed-closure defining prefix. A generic factor having γ=5 is insufficient because the source conjecture concerns special prefixes. Dolce's 2023 result predates v5; it is not a later refutation merely because both bounds contain five. His §5 proposes pseudopalindromic closure as a possible approach; it does not supply the needed admissibility bridge.

**Schaeffer–Shallit, arXiv:2012.06840v6, Theorem 2 and its proof pp.2–3.** This is a general first-order decidability/construction theorem for prefixes of a given automatic sequence. The proof encodes equal factors and occurrence crossing and allows repeated indices to express cardinality ≤c. It neither supplies this mixed directive nor asserts four for all generalized pseudostandard sequences. Decidability does not turn a new exact refutation into an already known theorem. Its automatic-sequence results do not provide the missing all-directives bridge.

**Banbara et al., arXiv:2602.16152v3, Theorem 43, Lemmas 41–44 and proof pp.14–16.** They classify all 32 smallest attractors of canonical Thue–Morse words T_n=μ^n(a), n≥6, using projection under halving and short forbidden witnesses. They also treat canonical Fibonacci and period-doubling words. The current landing page gives v1 18 February 2026, v2 9 October, v3 12 October 2026; the body distinguishes the CPM June 2026 preliminary version from its added Thue–Morse classification. No result here quantifies over arbitrary mixed closures.

**Faro–Marino–Pavone, arXiv:2610.10950v1, §§3.1–3.2, 3.7, Lemma 5.1 and Theorem 5.4.** This is the closest substantive-method objection. Their general coverage/hitting-set equivalence and minimal-coverage reduction are precisely the classical machinery underlying the eleven-factor certificate; the review claims no novelty for them. Their sixteen-witness lemma uses disjoint coverages and interval forcing to classify optimal four-sets of canonical Thue–Morse words. That proof architecture is close to this four-case obstruction. Their theorem hypotheses remain t_n=μ^n(a), n≥6. A 36-letter w cannot be one of these power-of-two-length words. More strongly w contains 01010 and hence is not any Thue–Morse factor: μ-words have no triple equal letters (each length-three window includes a mixed μ-pair); a five-letter alternating factor, according to its starting parity, would desubstitute to 000 or 111. Thus Dolce's factor-domain upper theorem also cannot supply this witness by specialization. This elementary exclusion is about the exact w, not a worldwide prior-art claim.

The Faro body gives genuine reason to scrutinize how much scientific contribution remains after adapting known machinery. The generic bridge from attractors to hitting sets is complete and classical; the bridge from a **known theorem to the specific mixed-closure counterexample/source negation** is not established. Under the requested EXCLUDE rule I therefore do not exclude merely for elementary finite geometry, small size, generic decidability, or search ease. The new candidate content is the admissible closure witness and its obstruction to the full published bound. Root must adjudicate substantive credit; this preliminary review is favorable to proceeding to formalization, conditional on bounded novelty work and final review.

Chronology: Dolce 2023; source v1 August 2023, v5 September 2024, journal 2024; Banbara v1 February 2026 and v3 October 2026; Faro v1 7 October 2026. All precede this candidate's local 30 October 2026 artifacts. None of the read exact statements is an identified prior refutation of the source's family and quantifiers. The Banbara body explicitly acknowledges the concurrent Faro classification. No priority between those papers is adjudicated here.

## Novelty limitations and disposition

The live current-source and related-paper pages and the actual closest proof bodies improve the previous packet. They do not replace a current public proof-registry audit. Previously denied GitHub API/raw/codeload/diff/patch, ScienceDirect and Google challenge routes were not retried; inaccessible historical intervals remain parked. No MathDB mutation, git action, shared edit, public posting, browser, or Lean/manuscript run occurred. No failure-search-as-novelty inference is made. Full citing literature, registries, MathSciNet/zbMATH, and worldwide priority remain uncleared. Administrative snapshots show no prior credited attractor-family entry in their bounded object-name scan; this alone proves nothing about external novelty.

Recommendation: INVEST in the literal finite formal endpoint and an independent final review; retain NOVELTY HOLD until root resolves the current registry/access holds or explicitly records their bounded limits under campaign standards. Do not count now. `provenance.md`, `frozen-inputs.json`, `access.jsonl`, `failures.md`, the independent check, final manifest and separate verification receipt provide auditable boundaries.

## Concrete finite Lean plan (no runs now)

1. Use `List Bool` for words; define R as reverse and E as reverse.map Bool.not. Define `IsClosure θ s t` by prefix, θ-fixedness, and least length among all θ-fixed extensions. Prove the overlap/longest-fixed-suffix closure lemma in ordinary Lean. Instantiate its five suffix tables with kernel `decide`/`simp`; prove the literal w is the fifth closure. Do not import Python assertions as axioms.
2. Define directives `Nat → Bool` and `Nat → {R,E}` with the five literal entries and the explicit periodic tails above. Define closure recursion using the proved constructive closure formula (finite longest-suffix search); prove strict length growth and nesting. Define the infinite sequence by the stabilized letter at each index and prove every recursively constructed word prefixes it. This proves the full Definition-3 admissibility bridge, including w_5=w; optional aperiodicity is not part of the endpoint.
3. Define `Occurs w f i := i+f.length≤w.length ∧ w.drop i |>.take f.length = f`. Define `Attractor w Γ` for `Γ : Finset (Fin w.length)` by every nonempty factor f and occurrence i implying existence of an occurrence j and γ∈Γ with j≤γ.val<j+f.length. This explicitly quantifies over all nonempty factors, not just the eleven. Prove equivalence with intersection of finite occurrence coverages and monotonicity in Γ.
4. Prove the eleven exhaustive occurrence-start equalities by kernel-evaluated finite bounded comparisons, with a lemma reducing any occurrence to the finite range. Prove the block pigeonhole and four-case argument above for any Γ.card≤4, or extend to a four-set then use it. Use ordinary `decide`, `simp`, `omega`, and `Finset` reasoning; no `native_decide`, sorry, added axiom, or unsafe evaluation. The geometric route avoids a huge 58,905-case term. The optional upper theorem can use a finite all-substrings characterization, verified by kernel reduction.
5. Define the literal source proposition `∀ Δ Θ n, ∃ Γ, Attractor (prefixWord Δ Θ n) Γ ∧ Γ.card≤4`, with binary Δ and E/R Θ and no extra restriction. Prove its negation by the explicit Δ,Θ,n=5, construction equality, and lower-bound theorem. If phrased intrinsically over every pseudopalindromic prefix of every Definition-3 sequence, use the nesting construction and w=R(w) lemma to derive that negation too. Final root replay must audit allowed axioms (only propext, Classical.choice, Quot.sound) and the endpoint definition. Feasibility is a plan, not a formal certificate.
