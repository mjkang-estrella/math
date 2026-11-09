# Independent review: MathDB 368999

**Disposition: HOLD for qualification; ordinary mathematics PASS. Credit 0; campaign remains 52/60.** This review independently verifies a refutation of the literal stabilizer conjecture under the definitions in both available arXiv versions. It does not clear worldwide priority, the final 2017 predecessor body, or the cited thesis. Root alone adjudicates acceptance. No formal theorem, replay, paper, execution authorization, or self-acceptance is supplied.

## Literal endpoint and source semantics

The assigned JSON and JSONL parse identically. The statement hash is `e6dd3f8b47dfa82c245729d3a10bb9fc213a38f7e3e11fd5b36bc2f4e643bf29`, agreeing with target-provenance.json. That provenance's original corpus chunk was not reopened. MathDB's open status and empty solutions array have no novelty force.

Primary sources: Allocca–Trimmer, [v1](https://arxiv.org/html/2506.19216v1) and [v2](https://arxiv.org/html/2506.19216v2), Sections 1–3, Lemmas 1–2, Theorem 4 proof, Corollary 2, Conjecture 2. Frozen r325 HTML/raw and text were used. Bounded rereads restored the relevant portions after a combined tool response truncated. The raw v2 definition and Conjecture 2 were independently checked against the extracted text. Read offsets and hashes are in reads.json; a requested output range is not a claim that every character survived a truncated display.

* D_n has order 2n; r has order n, not 2n. Thus D_8 below has 16 elements.
* A symmetric generating set excludes the identity, is closed under inverses, and generates the group. It is not required to be irredundant or minimal. The source's ordinary word-length function is minimal, but its W_l is a different object.
* v1 defines W_l through representability by l letters and explicitly asserts W_l=W_(l-1)S. Lemma 2 proves the alternating sum/difference recurrence. v2 expressly permits nonminimal products of l elements. It even discusses appending canceling reflections. Its displayed example contains an apparent dropped f in a subsequent expression; the definition and recurrence do not depend on that typo.
* Therefore W_l consists of all products of exactly l letters, permitting cancellation. It is neither a reduced-word layer, a shortest-distance sphere, an at-most-length ball, nor a first-visit layer. In particular ff=e belongs to W_2. The distinct-generator diagonal terms must not be discarded.
* F(r^i f^k)=i in Z/nZ, W'_l=F(W_l). At even l every word is a rotation; at odd l every word is a reflection. F is injective on either parity class, but not on the whole group.
* The normal form for S is {f,r^a f,r^b f}, obtained by renaming the first reflection. v2 recalls the criterion <r^a><r^b>=<r>. There is no additional all-pairs-generate or pairwise-coprimality requirement.
* Section 2's prime-modulus and seven-distinct-differences conditions qualify Lemma 3 and Corollary 1. Section 3 explicitly returns to arbitrary n. Conjecture 2 follows the arbitrary-n Theorem 4 and Corollary 2. It has no prime-only qualification or odd-l restriction. Taking l=2 is legitimate under either l>=0 or l>0 conventions.
* The stabilizer is the additive translation stabilizer. The source writes {1} for the trivial group in Conjecture 2, while its proof uses {0}. This review interprets the singleton as the identity subgroup. The counterexample has two stabilizer elements, so it disproves both the substantive intended dichotomy and a literal singleton reading; it is not a notation correction.

## Independent ordinary certificate

Use the explicit group G=(Z/8Z) semidirect C_2 with pairs (i,k), k in {0,1}, and multiplication

    (i,k)(j,h)=(i+(-1)^k j, k+h mod 2).

Associativity follows by expanding either triple product to exponent i+(-1)^k j+(-1)^(k+h)t and parity k+h+u. Identity is (0,0); inverses follow from this rule. Let r=(1,0), f=(0,1). Then r has exact order 8, f^2=e, and frf=r^(-1). All 16 pairs are r^i f^k, uniquely. This supplies an actual dihedral group, rather than assuming that a presentation has the claimed order.

Take S={f,rf,r^4f}. Its three elements have distinct exponent/parity pairs (0,1),(1,1),(4,1); all are nonidentity reflections and square to e. S is symmetric. Since (rf)f=r and f is in S, S generates G. The presence of a two-element generating subset does not violate the source's definition. In the predecessor's classification this is case B: <r> and <r^3> are full, <r^4> is proper. Both that classification and the current paper allow this case.

Put A={0,1,4} in Z/8Z. By the pair multiplication rule,

    (r^x f)(r^y f)=r^(x-y).

Every two-letter word in S arises from one and only one ordered pair of letters. Conversely every ordered pair is permitted, including equal letters. Hence W_2 is exactly {r^(x-y):x,y in A} and W'_2=A-A. This proves completeness of the actual source word set; it is not the assertion that a chosen subset of it has a period.

The complete hand table, with rows x and columns y, is:

| x-y | 0 | 1 | 4 |
|---|---|---|---|
| 0 | 0 | 7 | 4 |
| 1 | 1 | 0 | 5 |
| 4 | 4 | 3 | 0 |

Thus W_2={e,r,r^3,r^4,r^5,r^7} and B=W'_2={0,1,3,4,5,7}. These nine entries were reasoned by hand; no mathematical enumeration program was run.

Translation by 4 swaps {0,4}, {1,5}, and {3,7}, proving B+4=B. To establish the entire stabilizer, use complement C={2,6}. A bijective translation preserves B exactly if it preserves C. If C+c=C, then 2+c is either 2 or 6, so c=0 or 4 modulo 8. Both work. Therefore

    Stab(W'_2)={0,4}.

It contains a nonzero element, excludes 1 (also 1 in B but 2 not in B), and has cardinality two rather than eight. It is neither the identity subgroup nor the full cyclic group. This is a complete ordinary refutation of the universally quantified literal MathDB endpoint in the available source versions.

Theorem 4's growth bound is a different endpoint: |W_2|=6 >= min(5,8). Nothing here asserts a refutation of that theorem or of the paper's lambda_1 bound.

The proposed family also checks without computation. For n=2m, m>=4, take S={f,rf,r^m f}. Exactly the same admissibility and multiplication arguments give

    W'_2={0,1,-1,m,m-1,m+1}={0,m}+{0,1,-1}.

The three cosets of H={0,m} represented by 0,1,-1 are distinct because m>=4. Their union has six elements, is nonempty and proper since 2m>=8, and is H-invariant. Full translation invariance of a nonempty set would force that set to equal Z/(2m)Z. Thus its stabilizer is nontrivial and proper. An exact classification of the family's stabilizer is unnecessary and is not claimed. This remains one family and at most one possible credit.

## Version and prior-source chronology

1. Moulton–Steel arXiv:1104.5044v1 is dated 26 April 2011 in the body. The 2025 paper cites the 2012 Journal of Mathematical Biology publication. I read the primary introduction/definitions, Section 2 inequalities and proofs (Lemmas 2–3 and Proposition 4), and Section 3's symmetric-group constructions and Theorem 5 proof. These bound deletion/substitution sensitivity and shortest-path distances. Proposition 4 uses S_N union S_H for a semidirect product; the present S consists entirely of reflections and is not that union. Their bounds do not compute a translation stabilizer of this exact three-letter product set. No full-paper or final-journal-version clearance is claimed.
2. Allocca et al., arXiv:1512.02844: abstract history reports v1 9 December 2015, v2 30 December 2016. The cached actual body is explicitly v2. I read Section 2.2.3 including Lemma 1 and proof, Theorem 4 classification/proof/examples, Section 4.2.3 including both conjectures, Theorem 11, Lemmas 4–5 and proofs, Theorem 12 and its short proof, and the appendix's coprimality/classification discussion. The 2017 final is Discrete Applied Mathematics 221, DOI 10.1016/j.dam.2017.01.002. Page citations differ (33 versus 34 as starting page); no mathematical inference uses that discrepancy.
3. Allocca–Trimmer v1 24 June 2025 and v2 20 September 2025 both contain Conjecture 2. A fresh GET of the current abstract at 2026-11-06T08:37:57Z reports only these versions. Its bytes/hash match r325's abstract. There is no journal-reference field in that fetched metadata. This establishes current arXiv listing fidelity, not the nonexistence of a journal version, erratum, or public answer elsewhere.
4. Aseeri, DOI 10.3934/math.20251199: actual primary PDF text gives received 14 August, revised 8 November, accepted 18 November, published 24 November 2025. I read its ordinary/conjugacy norm distinction, Theorem 1.5, Section 2's relevant lemmas, Definition 2.1 and the full main proof through its even cases, conclusions, references and thesis acknowledgment. Its B_X(k) uses at most k conjugates of letters and inverses, not exactly k letters of S. In the proof's reflection-pair case, Conj(S) is all reflections, which is already a larger alphabet than our S. For our S in D_8 the conjugacy closure contains both reflection conjugacy classes and thus all eight reflections. Its two-conjugate products consequently cover all rotations, whereas our ordinary S^2 has six rotations. This explicitly demonstrates why the conjugacy-diameter theorem is not a resolution of the present word-set stabilizer claim.
5. Aseeri's acknowledgment says results are adapted from Chapter 6 of an Aberdeen PhD thesis. The thesis title, submission date, Chapter 6 body and any additional ordinary-word results were not recovered. The article's conjugacy-only scope does not clear the thesis's potentially broader contents.

## Material HOLDs and lawful access limits

The DOI GET for the 2017 predecessor ended at an Elsevier linking-hub locator page (HTTP 200, 2695 bytes), not a theorem body. It contains a scripted/hidden-input redirect and TDM reservation metadata. I did not execute that flow, submit a form, or infer open access. There is no authenticated textual equality between this final journal body and the read 2016 arXiv v2. **Final-2017 source comparison remains HOLD.** The exact residual is to read the final Section 2 three-reflection classification and Section 4.2.3 constructions/proof bodies, including any changed examples or added periodicity observations.

A normal GET of Aberdeen's public AURA home succeeded; a single public search-page GET for the author returned only an empty DSpace application shell, not results or thesis text. No browser, REST/API route, authentication, consent, access request, or JavaScript challenge was used. **Thesis Chapter 6 remains HOLD.** Its possible ordinary-word/additive-set observations and chronology are the concrete residual, not an allegation that it resolves this conjecture. No blanket demand to read every bibliography entry is imposed.

No inherited denied route was retried. In particular, no GitHub API, live MathDB request, Wiley, ResearchGate, CiteSeer, Togni, or other listed denied route was used. All new network requests were ordinary public GETs. The two unrelated guessed arXiv IDs noted in r325 were excluded; their mathematical contents were not read for this review. No publisher private-access page was treated as redistributable full text.

## Registry, subsumption, novelty, significance: separate decisions

Fresh public GitHub HTML reports current default-branch heads:

* OpenAI/math: 4eaee87548250b2682affda7d05d947c05554bae.
* Vilin97/lean-pool: 01db1d7049cf9668bda1e9e106875ee1278b43e6.
* LeanPool/lean-pool: 906301dff114598197af816aefe25211ff23a6b0.

The repositories were kept distinct. Fresh pinned CONTENTS/projects/candidates bytes match the relevant frozen snapshots. registry-screen.json records bounded ID/source/author/stabilizer text routing. No relevant theorem-body match was identified. The unrelated Morava/Bass–Serre stabilizer snippets do not address this finite cyclic translation question, but their underlying papers were not audited. Index nonhits are not literature absence proofs. r325's completed allowlist reconciliation was read as routing metadata only; its no-hit report for this ID is not an independent exhaustive history audit. No active/protected lane was opened or hashed.

**Subsumption:** no read public theorem has been shown to imply this exact counterexample as an already resolved endpoint. There is an important specific near-bridge: the predecessor Theorem 12 proof lists the rotations obtainable as gss'g^(-1), including 1,r^(+/-a),r^(+/-b),r^(+/-(a-b)) (and r^(+/-1) in its text). For a=1,b=4,n=8, its displayed list specializes to the six rotations above. One can recover W_2 from that observation since g=e is allowed and rotation conjugation in a dihedral group only preserves or inverts exponents; S^2 is inverse-closed. However the theorem's stated endpoint is lambda_2=2, not an intermediate additive translation stabilizer. It does not state the choice b=n/2, the proper periodicity, or a refutation of the later conjecture. I independently proved those additional steps above; I do not treat the bare availability of a product formula as a completed prior public refutation. The missing final journal/thesis comparison could alter this assessment.

**Novelty:** HOLD. There is no worldwide priority claim. Current arXiv survival of the conjecture and the bounded registries are positive context only. Final predecessor/thesis and later-public-resolution risk remain open. A known public resolution or duplicate would earn zero regardless of mathematical correctness.

**Meaningful significance:** provisionally eligible, final qualification HOLD. The candidate negates the actual all-n conjecture using a genuine generating presentation and full word set. It is not a prime-domain change, identity-notation change, helper, or claimed growth-theorem improvement. The nine-entry table's ease, finite size, and likely formalizability are not exclusions. Familiar Kneser theory is not a complete exclusion bridge either. No complete prior-result bridge eliminating the new periodicity observation has been established from the sources actually read. Conversely, I cannot certify final campaign significance before the material source gaps are resolved. Root should assess the explicit Theorem 12 near-bridge above under the same standard as earlier small constructive refutations, rather than presuming eligibility or rejecting solely for shortness. No earlier precedent is claimed to have been fully inspected here.

## Pi recommendation and residual work for root

**Do not execute; no dormant implementation plan written.** Necessary source/prior/significance gates have not all qualified PASS. This review therefore stops before the conditional plan requested in TASK. If root later clears the material sources and adjudicates significance, formal work must still represent the actual dihedral group, all length-exact products, F, and full translation stabilizer, with source/admissibility bridges. A theorem merely about an arbitrary finite subset would be inadequate. No Lean dependency or axiom audit was run here.

Root's residuals are precise: obtain lawful authenticated final-2017 relevant body; locate/read thesis Chapter 6 and establish its date/scope; reconcile any journal correction/later public resolution found through bounded lawful sources; settle significance with the specific near-bridge in view. Only then consider a separately authorized literal formal endpoint and independent extracted replay. Credit remains zero.

## Integrity and resource report

The mandated bootstrap was the first actual command, verbatim. Its first receipt was preserved. Entire standalone TASK was displayed without truncation by bootstrap. frozen-before.json verifies all 105 exact paths before any mathematical input reading; frozen-after.json records the final repeat. All non-target r325 files were integrity-only except explicitly permitted instructions/history/HTTP/inventory metadata; no other target proof body was reopened. All writes stayed in this review lane. No children, Git, Lean, solver, CAS, mathematical program search/enumeration, publication, uploads, messages, browsers, account actions, or dependency writes occurred.

Every local command used timeout (20–120 seconds), Python -I -B, at most two allowed CPUs, CPU limit no greater than 120 seconds and address-space limit no greater than 6 GiB. Bootstrap had tighter limits. review_tool.py logs self CPU, wall and high-water RSS per invocation in resources.jsonl. These are process-self measurements, not sampled process-group/cgroup peaks; group/cgroup telemetry is unavailable. The few initial setup/hash commands and final delivery commands did not persist self-usage samples; their caps and synchronous exit are visible in the tool transcript. This telemetry gap is explicitly not a claim of full sampled enforcement. No child process was launched by Python; all timeout jobs returned exit 0 and were reaped. There is no pending local job.

Initial combined outputs were truncated (frozen manifest display, broad input metadata, combined source output); mathematical source passages used for conclusions were subsequently read in bounded ranges. Full hash verification operated on all 105 inputs regardless of display truncation. A read inventory distinguishes cached proof-body reads from metadata, raw HTML spot checks, retrieved-only artifacts, and unavailable final/thesis bodies. HTTP-RECEIPTS.json preserves exact URLs, UTC, status/final URL, bytes and hashes. source-chronology.json records read depth. MANIFEST.sha256 covers delivered lane artifacts except itself. No formal replay or acceptance is asserted.
