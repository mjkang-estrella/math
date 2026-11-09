# Independent review of MathDB 340110

Reviewer: GPT-6.1 Sol, high/default, personally. No children, provider/model fallback, network, git, installation, publication, account or browser operation. Author files were not edited. Campaign remains **55/60 beyond 39, 94 total; credit 0; acceptance CLOSED**.

**Technical certificate: PASS. Campaign significance: recommend EXCLUDE as routine adaptation. Historical protocol: HOLD for root adjudication. Manuscript reporting: HOLD for the corrections below.** These are separate decisions. The mathematical refutation is valid regardless of the recommended credit exclusion. Root alone decides integration and credit.

## Exact statement and fidelity

Primary: Aliabadi–Soleimany Dizicheh, *A note on matchings in abelian groups*, arXiv:1808.04975v3, 20 February 2020, Preliminary and Conjecture 3.7, pp.1–5. The copied MathDB340110 record and earlier ordinary/qualification reviews are inputs. I read the actual primary definitions, Theorem3.5, Remark3.6, and Conjecture3.7, rather than relying only on those reviews.

For every abelian group G and nonempty finite A,B with equal cardinality, 0 outside B, and A disjoint from A+B, the conjecture asks for a bijection f:A→B such that a+f(a) lies outside A, its decreasing positive-fibre sequence has only ones, and every admissible bijection g with m_g(x)=m_f(x) for **every x in G** equals f. No ambient Fintype, distinctness A≠B, disjointness A∩B, or exclusion of zero from A+B is present.

Matching.lean supplies exactly these objects. Finite subtype equivalences are actual bijections, not a chosen permutation surrogate. multiplicity filters the finite domain subtype; it is defined on all G. support is the image of the sum map. sequence maps multiplicity over the support multiset and sorts decreasing, retaining repetitions for distinct support labels of equal size. Acyclic compares full functions, never only sorted sequences. Standing includes every preliminary hypothesis and the pointwise form of sumset disjointness. The existence conjunction is not encoded into a definition of the answer.

Bridges.positive_iff identifies support with positive fibres. unit_iff_positive removes sorting only at the membership level. unit_iff_injective proves both directions: two arguments in a unit fibre coincide by card≤1; an injective sum map makes every positive fibre a singleton. multiplicity_one/zero prove the corresponding full-function values. finite_set_bridge represents an arbitrary finite Set exactly by its toFinset; membership and subtype maps transport along equality. Classical decidable equality is available on any group, so the instance parameter adds no mathematical hypothesis.

Sequence.sequence_length, sequence_decreasing and sequence_multiset establish the literal sequence specification. unit_iff_replicate gives equality to replicate(support.card,1). source_disjoint_bridge proves the exact equivalence of the last Standing clause and Set disjointness from the existential sumset. Generic definitions are universe polymorphic; Conjecture quantifies over Type. The finite small witness suffices to refute any usual universe version.

To independently close the source feedthrough, I wrote **audit/Literal.lean**. Its checked theorem Independent.literal_refutation negates the universally quantified conjecture with separate preliminary assumptions, literal Set-disjointness and literal repeated-ones list equality. It derives this from refutation through source_disjoint_bridge and unit_iff_replicate, without new assumptions. Receipt 1794108640910639935_audit_Literal.json is exit0 and prints the expanded statement/body and allowed axiom set. Production files were unchanged.

## Independent ordinary proof and controls

Take K=ZMod3, G=K×ZMod2, A=B=K×{1}, H0=K×{0}, t=(1,0). coord identifies K with the actual subtype A. G has six elements and A,H0 each have three. Zero is outside B. All A+B sums have second coordinate zero, and (u,0)=(u,1)+(0,1); hence A+B=H0, disjoint from A. Every subtype equivalence is consequently admissible.

For ANY unit f:A≃A, unit_iff_injective makes s_f(a)=a+f(a) injective. Both second coordinates are zero. Under coord its first coordinate is an injection K→K and hence surjective by finite self-map cardinality. Therefore s_f bijects A onto H0. At every ambient x, its multiplicity is 1 when x.2=0 and 0 otherwise. This is the indicator theorem, including points outside support.

outputTranslation has actual forward addition of t and inverse subtraction of t on A. translate f is its composition after f. Equality translate f=f, evaluated at coord0, would force t=0 by cancellation, contradicting 1≠0 in ZMod3. For every ambient x the defining filtered domain fibres satisfy m_translate(f)(x)=m_f(x−t). Subtraction of t preserves the second coordinate, so the indicator theorem gives equality of the full functions. Both maps are admissible and distinct, contradicting Acyclic f. Thus no unit matching is acyclic; refutation applies the generic conjecture to standing_A.

identity is unit because doubling on K is invertible, with 2·2=1. identity_collision gives an explicit distinct translated matching with the same full function, so the all-unit obstruction is nonvacuous. For every c:K, constantSum c maps (u,1) to (c−u,1), an involutive bijection. Its sum is always (c,0), so its multiplicity is exactly 3 there and 0 everywhere else; its support is that singleton and its actual sequence is [3]. Equal full multiplicity for another g forces a+g(a)=(c,0) at every argument by positivity; cancellation forces g=constantSum c. Hence weak acyclic existence holds, while these maps are not unit. B∪{0} is not a subgroup: (0,1)+(1,1)=(1,0) is neither in B nor zero. Source Theorem3.5 is not contradicted.

All production proof steps above were reviewed in the full five copied sources, including membership, cardinality, inverse, finite-surjectivity and equality-direction details. No matching enumeration, empirical inference or production repair was used.

Three copied negative probes were reproduced sequentially under the strict runner:
- WrongIndicator: exit1 because decide proves the simplified claim 1=0 false.
- WrongUnit: exit1 because decide proves [3]=[1] false.
- WrongAcyclic: exit1 because the supplied proof has type ¬Acyclic identity where Acyclic identity is demanded.
The third is a deliberate semantic type mismatch, not a missing import or unrelated elaboration error. Their full logs are preserved. Ordinary decide on small kernel-reduced primitive facts is used; native_decide is absent.

## Source-only replay, pins and body audit

The source-review receipt records build initially empty. Exactly five fresh builds ran in order Matching, Bridges, Coset, Controls, Sequence, followed by five module-name leanchecker executions, all exit0. No author olean was imported or copied. env.sh uses own build first, then only pinned upstream library paths. Every Lean invocation used -j1 -M3500 -DwarningAsError=true. No second five-build replay was run because nothing changed.

The ten replay receipts have stamps:
1794108498514538850, 1794108502071841349, 1794108507878442752, 1794108513776640236, 1794108516811719322;
1794108524992476476, 1794108526362311043, 1794108527714870647, 1794108529110199371, 1794108530487410734.
Full filenames, argv, true exits, paths, log hashes and resource records are in receipt/ and the terminal manifest.

Independent binary hashes:
- lean: e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550
- leanchecker: ccef1bfe9bfeecea65137d94a69033c1a89f360711f50fa3178e7ba3e696fcbe
Installed mathlib .git/HEAD is d13f23b723b8a846827a245b89c10fc7d3f11612, read as metadata without git commands. env.sh SHA256 is d367f7da95ef4013684225509b7bcf7cd8e339a96a5e154145ddb9af8a90fbb2. Each own postchecker source AND olean hash equals both sealed author-root and author-cleanroom values; exact ten comparisons are in results/forensics.json. This verifies installed metadata and actual executable bytes, not all upstream source truth or a global dirty-tree audit.

audit/Independent.lean adapts the supplied inventory algorithm, whose full code I read: it selects declarations by actual module-origin indices in a nonexporting fresh environment; it traverses constants in both types and values, and inductive constructor links, until the worklist is empty; exhaustion is fatal. This reuse is disclosed, not presented as independently invented audit software. It was rerun on the independently built modules and passed. Additional Python inspection independently checked complete local-name membership, all dependency targets, owner anchors, endpoint closures, axioms and nonempty typed bodies.

Actual recomputed counts: **101 locals; 6036 all-local closure; 5174 refutation closure**. Origins: Matching9, Bridges19, Coset47, Controls18, Sequence8. Every local declaration has a typed expression, actual value and source owner, including generated simp/equation/proof/congruence helpers. Some generated declarations originate in a later importing module: e.g. sumMap.eq_1 is attributed to Coset although its definition owner is Matching. This is expected generation provenance, not an unexplained source substitution. results/process-and-declarations.json supplies corrected cross-module source anchors for every declaration; the initial module-only source-origin table is supplementary and may have null anchors for those generated names.

Full types, full Expr bodies, actual origins and DAG are in audit/independent-inventory.json, not merely a name list. Bodies are automatically traversed in full; I do not claim to have read the many megabytes of expanded Expr text byte by byte. The human inspection covers every source proof and the complete 101-entry owner/dependency inventory. Every local is safe and nonaxiomatic. Every reachable axiom is propext, Classical.choice or Quot.sound. Saved endpoint closures additionally cover sequence, identity, constant-sum, weak-existence and subgroup/disjointness controls. #print axioms outputs agree. No sorry/admit/new axiom/unsafe/native_decide/partial/extern/implementedBy bridge or unvalued local proof was found. Imported tactic metaprograms are not asserted to be globally unsafe-free; they lie outside the audited kernel proof closure.

The old extract.py was read ONLY as evidence, never executed. Its current repaired copy writes generated-build-plan.json rather than PINS. Archive member paths were checked for absolute paths, parent traversal and links; none failed. All five archive production sources hash identically to own sources. The archive contains helpers, audit/manuscript sources and results/generated-build-plan.json, but no production oleans and no restored PINS.json. The generated plan is the historical overwritten-pins content, SHA197c8e26..., not the original pin document. This archive limitation is explicitly distinguished from our independently pinned fresh replay.

## Significance and prior bridges: independent adverse recommendation

**Recommend EXCLUDE from campaign credit as a routine adaptation, while retaining the valid technical refutation.** This recommendation is my independent scientific judgment, not a root acceptance decision and not a claim of an earlier printed exact counterexample.

The concrete complete reduction is:
1. For any admissible self-bijection f of A in an abelian group, f⁻¹ is admissible. Reindex b=f(a); commutativity proves equality of FULL labelled multiplicity for f and f⁻¹.
2. Acyclicity therefore forces f=f⁻¹. This ingredient is explicitly documented in the actual 2022 Aliabadi–Filom 2103.11432v2 discussion of Theorem2.5, reproducing an earlier inverse argument.
3. Unit fibres forbid any nonfixed two-cycle: a≠f(a) and f(f(a))=a give the same sum at the two distinct arguments. Thus every acyclic unit self-matching is identity, with no extra hypothesis.
4. On the present pair, identity and u↦u+1 have sum maps 2u and 2u+1 onto K, with common full indicator on H0. Both are admissible, distinct, and satisfy all standing assumptions. Identity is therefore not acyclic. Combining with step3 excludes ALL units.

This is genuinely complete, not merely a resemblance to the old odd-cardinality argument. The target-specific residue is the elementary identity collision on a finite coset where doubling and translation are bijections. My reason for exclusion is that this direct specialization plus the immediate unit two-cycle observation leaves no substantial additional obstruction theorem beyond the documented inverse mechanism and explicit collision. I am not excluding merely because the group has six elements, because the proof is short, or because Lean verifies it. The all-unit quantifier itself is obtained by the prior involution argument; the stronger direct indicator proof is an alternative presentation, not additional scientific content that defeats that reduction.

The strongest contrary case is substantial: the exact published Conjecture3.7 is refuted under EVERY standing assumption; existence of units and acyclic maps separately is exhibited; the periodic support explains why the strengthening fails despite weak existence. No inspected earlier source prints this precise example. Root's prospective modest-PASS assessment is defensible under a less restrictive credit judgment. I nevertheless recommend exclusion under this campaign's express exclusion of routine prior-lemma adaptations. Root should resolve this disagreement explicitly rather than construing the technical PASS as concurrence on credit.

Other comparisons were independently checked against actual copied relevant bodies:
- Source Remark3.6 exhibits bad unit matchings while reporting eight good unit matchings for that different pair; two bad maps alone do not negate existential Conjecture3.7.
- Theorem3.5 adds B∪{0} subgroup, which fails here.
- Actual 2019 Aliabadi–Janardhanan 1808.01376v3 (6 August2019), Section2 Definition1/Proposition1 and proof: a unique multiplicity monomial prevents determinant cancellation. Specializing one constant-sum variable to1 and others to0 gives a permutation matrix here. The necessary nonzero-determinant condition neither excludes units nor supplies unit existence. The printed word “invertible” is stronger than the nonzero determinant proved over the polynomial ring, but that upstream wording is irrelevant here.
- 2022 prime/doubling examples do not preserve the disjointness hypothesis; its inverse INGREDIENT does apply, as above. Its Sidon existence criterion is weak existence only; this B violates Sidon.
- 2024 2402.08008v3 Lemma2.6/Theorem2.8 use n−3-sized sets at n≥7. Since 2(n−3)>n, A meets x−B for every x, so A+B=G and target disjointness fails. Remark2.9's subgroup construction fails ordinary matchability. The ordinary classification is not a target refutation.
- 2025 SLC91 B91b Lemma2.1/Theorem2.3: ordering sums and filling the first equal-sum layer specializes here to h_c, exhausting A with multiplicity3. It proves weak existence, not a unit sequence.

No network/new prior retrieval was authorized or performed. Current registry heads and targeted searches are inherited dated observations, not new searches or theorem-body clearance. Separately typeset journal finals/corrections and exhaustive literature are outside this bounded review. I identify no concrete unacquired matching theorem as a separate source HOLD. The 94-scope inventory was inspected at title/scope-summary level, with relevant nearby comparisons in the supplied qualification; no accepted certificate or protected production body was opened. This is bounded distinct-scope evidence, not independent rereading of all55 full questions or a re-audit of prior39. No duplicate result or accepted-to-target bridge was identified. Only one possible340110 outcome exists; helpers, controls, inverse argument, witness and optional families earn no separate credits.

## Four-page manuscript QA and exact reporting corrections

The PDF skill was read in full; read-only work required no authoring marker. A fresh capped pdftoppm render at110dpi produced results/review-page-1.png through review-page-4.png. I visually inspected EVERY new page, not the author's supplied PNGs. All four are legible with sound margins/page numbers, no clipping, missing signs, black squares or overlapping text. Mathematical prose agrees with the reviewed proof, including all ambient labels, quantifiers and controls. ASCII notation is plain but readable.

Reporting HOLD, to be corrected by root without modifying historical author artifacts:
- **Page1 opening status paragraph:** “Original bytes require restoration” is now stale. Replace current-status wording with the exact historical failure, root restoration to original SHA, and continuing process/acceptance hold. Do not replace the historical FAIL by PASS.
- **Page4 §7 replay paragraph:** qualify that the archive carries a generated build plan, not restored original PINS. Reproduction needs the separately preserved original pins and actual binary verification. Preserve the historical helper-overwrite event.
- **Page4 §7 final status/receipt references:** distinguish author's verification ledger from this independent review; intake indexed93 before the terminal seal, whereas copied receipts now total94. Historical results and manifest must stay unchanged.
- **Page3 §5 / page4 conclusion-status wording:** incorporate this review's adverse significance recommendation and root's pending adjudication. “Independent review pending” is historical author status, not the current handoff status.
These are reporting/process corrections, not a required production-proof repair. Bibliographic identities and dates of the reviewed preprints agree with the actual copied bodies; the 2019 and 2022 companion filenames must remain distinguished.

## Historical integrity, deviations and review limitations

The original PINS bytes hash to **adfd53bfe65ca8f9711b9d8a3780c0b2a93fdaf2382fdbdb9fb14c3038763167**. Preserved overwritten bytes hash to **197c8e26df0268e9411cabb8d34a9ccc24a5356032d9cb20fa5de54ccf227a37**. The latter is the generated build plan. Root restored the exact original after preserving the failed check, overwritten bytes, old result and old manifest. The sole historical-manifest PINS delta is explained; it must NOT be repaired as though the historical failure never occurred. Before review, all552 frozen bindings matched. The terminal frozen-after supplies the final status separately.

Author receipt examination found94 files (73 exit0,19 exit1,one exit−6,one exit2), not “all checks passed.” The extra terminal-seal receipt explains the difference from the93 indexed at intake. All recorded groups are empty. All79 supplied author logs match their receipt hashes;15 cleanroom receipt logs are not supplied in inputs/author-logs and were not read from forbidden originals. Their detailed output cannot be independently certified from copied logs. Their receipts and the new source-only replay are available. This limit does not undermine our independently reproduced certificate but prevents universal historical-log clearance.

Timestamp/wall intervals show the initial OOM Matching run overlapped an inventory reader, and the later audit overlapped all five checker sessions. Wrapper/negative-child nesting is separately apparent and must not be mislabeled as independent concurrent builds. All overlap pairs are saved. Author's direct reader, /proc-fd visible reader workaround, late source map, initial OOM, extraction-directory assertion, missing PDF dependencies and premature rendering failures remain reported deviations; no failed historical run was erased or converted to success. Green replay cannot retroactively certify strict sequencing.

Own deviations are candidly recorded: after the two exact required commands, I attempted direct runner execution and got shell exit126 (not executable, no runner receipt). The first Python runner inspection used nonexistent writer.py, yielding preserved exit1; actual helper is write_lane.py. It also ran from the inherited workspace cwd; subsequent substantive runner work used this lane. To resolve log-only output I used a capped direct Python tool reader of runner/receipt data outside the runner, then bounded capped reads of preserved own logs. These did not mutate inputs or use /proc-fd escape, but the startup read was outside the requested runner discipline. Native image-view and standalone writer invocations are not covered by runner RSS sampling. Root must assess this review-protocol deviation too; I do not certify unqualified strict compliance.

All own builds, checkers, audits and render runs were sequential and finished before the next substantive run. No background shell job or helper-cap change was used. Process telemetry is sampled, not cgroup accounting; it can miss transient RSS and does not bound model inference, tool transport or native image display. Largest observed completed own runner group RSS before sealing was2641129472 bytes, maximum reaped CPU9.038s. One evidence display was transport-truncated; targeted reads recovered the skill, proof/audit code, manuscript, routing, complete qualification, inverse passage, determinant proof,2024/2025 relevant bodies and declaration digest. No exhaustive primary reread or manual inspection of every expanded expression byte is claimed.

## Persisted handoff and unpaid gates

See review.json; results/forensics.json; results/process-and-declarations.json; results/author-receipt-independent-index.json; audit/Independent.lean and independent-inventory.json; audit/endpoint-closures.json; audit/Literal.lean; all receipt/log files; four new QA PNGs; frozen-before.json, frozen-after.json; SHA256-MANIFEST.json. The terminal seal records every previously completed receipt JSON including bootstrap, input bindings, own hashes and named noncircular self-exclusions.

Paid: literal-source/finite-set/sequence bridges, independent ordinary proof review, five fresh source builds and five kernel checkers, transitive typed-body audit, all mandatory controls and semantic negative failures, pin/binary/source/olean/archive inspection, independent four-page visual QA, explicit independent significance objection.

Unpaid: root decision on recommended significance exclusion, historical author and own reader-protocol deviations, current reporting corrections, and root acceptance. No proof gap or missing library blocks the technical result. No unconditional acceptance or campaign credit is asserted.
