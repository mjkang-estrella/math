# Independent formal and prior review

SOURCE **PASS**. MATH **PASS**. FORMAL **PASS** on independent fresh extraction/replay. SUBSTANTIVE **favorable, conditional on novelty adjudication**. NOVELTY **HOLD**. Recommendation: retain the unconditional source-refutation certificate, proceed to root's remaining qualification gates, and do not accept/count yet. This is a review, not acceptance. Counts remain 9 additional / 39 total / next40; root alone accepts and counts.

## Frozen scope and source correspondence

The complete source-only.zip was frozen before scientific reading, SHA256 `651cb2a32c8be34fa3972599b7da470e9acfd7092634f1ac913595343db897de`. Original-before/copy/original-after equality was established by freeze.py. All archive members were extracted only under this lane. No candidate compiled cache was extracted. The byte-identical archive can be reconstructed using original ZIP metadata (archive-rebuild.json). The original five mathematical files, supplied audit, RUN, helpers, frozen evidence and administrative archive members are preserved byte for byte. IndependentAudit.lean is separate instrumentation, copied from the inspected all-origin audit algorithm; it changes no mathematical formalization. The independent audit receipt is computed from this review's new replay log, not adopted from the worker.

Read ancestor/batch AGENTS.md and both administrative snapshots; both JSON files were fully parsed after an initially truncated display. Administrative files are snapshots only. freeze.json, extracted/frozen-inputs.json and primary-freeze.json identify exact originals, copies and hashes. Immutable historical references are reused, not recursively duplicated.

The actual Dvořáková–Hendrychová body is arXiv:2308.00850v5, *String attractors of Rote sequences*, DOI10.46298/dmtcs.12385. Its archived PDF and journal-linked PDF have SHA256 `7c2b716e0067fa4bbd85640d8c849b93ae87eed59998e1b3e8bdf5a11ecfaacb`. I read its frozen actual text: §2 p.2 attractors; Definition1 and Definition3 p.3; Theorem8 statement and opening pure-E proof p.5; Theorems15–16 p.9; §7 p.15. The frozen journal-page evidence links that same v5 body. This review makes no new live-page claim.

Definition1 makes R reversal and E reversal plus letter exchange. Definition3 permits arbitrary infinite binary directives and arbitrary infinite E/R directives, with shortest closures. No normalization, aperiodicity, both-symbol recurrence, or Rote restriction is imposed there. Theorem15's special directive conditions and aperiodicity concern the standard CS Rote subclass; Theorem16 is a criterion, not a Definition3 premise. Theorem8's pure-E bound cannot cover the last R step here. Section7 conjectures four for pseudopalindromic prefixes of binary generalized pseudostandard sequences, not merely for pure-E or Rote prefixes. A defining w5 refutes it even if the defining chain is a subset of all pseudopalindromic prefixes.

## Independent mathematical inspection

I inspected all five full mathematical modules, including the end of Attractor.lean; no endpoint premise is hidden in an unread auxiliary file.

**Closure.** theta false is reverse, theta true is reverse.map not. The three laws establish length, antimorphism and involution. IsClosure explicitly requires prefix, fixedness and minimum length among every fixed extension. candidate(e,s,k)=s++theta(e,take k s). The full-length candidate is fixed, so Nat.find is justified constructively. extension_determined shows any fixed extension s++q with |q|≤|s| has q=theta(e,take |q| s). Thus least has length at most every such q. When |q|>|s|, least≤|s| bounds the candidate separately; the minimality quantifier does not stop at twice the input length. closure_unique uses minimum lengths in both directions and the reflected-extension identity. There is no imported closure table, Python certificate, or assumed generic-minimality axiom.

**Words.** Five kernel-decided tests certify the least added lengths 1,1,5,7,17, testing every smaller candidate; input lengths minus these give fixed-suffix lengths 0,2,0,4,2. Literal letters are 00101 and antimorphisms EEEER. fifth proves
`prefixWord delta anti 5 = bits "010110010101100101101001101010011010"`.
delta has only entries2,4 true and then zeros; anti is true exactly below4 and then R forever. These tails differ from the preliminary review's optional aperiodic extension, but are lawful for the source. prefix_step and prefix_nested prove nesting; strict_growth and length_ge prove unbounded lengths. infiniteWord chooses the i-th letter from stage i+1. prefixes_infinite compares both stages in their common larger stage, so every finite defining word really prefixes the same infinite sequence. definition3 packages the actual recurrence, infinite-prefix agreement and growth. This is a genuine infinite source object, not a finite-prefix surrogate. No aperiodicity is asserted.

**Attractor.** Occurs(s,f,i) includes both i+|f|≤|s| and take/drop equality. Attractor quantifies every nonempty word with an occurrence, requiring another occurrence crossing p∈g. The eleven constraints are consequences necessary1–necessary11 of that full predicate, not its definition. occurrences1–11 test all i:Fin37, i.e. starts0 through36 inclusive. Their necessary lemmas separately derive j<37 from any arbitrary occurrence's length bound. Thus neither out-of-range starts nor the terminal boundary can be omitted; start36 correctly fails for the positive lengths4 and6.

The nine length-six factors have unique starts 5,6,7,13,15,17,23,24,25, respectively. Their occupied intervals are [5,10],[6,11],[7,12],[13,18],[15,20],[17,22],[23,28],[24,29],[25,30]. Factor1100 has starts3,11 and coverage [3,6]∪[11,14]; factor0011 has starts21,29 and coverage [21,24]∪[29,32]. All indices are zero based. check.py independently reconstructs the closures and these complete occurrence lists, then rejects all58,905 four-subsets using just these necessary constraints. This is corroboration, not a formal premise.

**Geometry and Endpoint.** obstruction quantifies arbitrary a,b,c,d:Nat and only the eleven hit/hitTwo premises; omega proves False. There is no within-block, distinctness, sortedness or exact-four-position premise. coverFour exhausts lists of length≤4 and pads by repetitions, including the empty case using Inhabited. Endpoint converts g.toList membership to this cover; all four naturals may lie anywhere. The finite word is nonempty so Fin w.length is inhabited. no_four therefore excludes every g.card≤4, including smaller cardinalities.

The full endpoints are:

```
SourceClaim := ∀ d t : Nat → Bool, ∀ n : Nat,
  ∃ g : Finset (Fin (prefixWord d t n).length),
    Attractor (prefixWord d t n) g ∧ g.card ≤ 4
source_refuted : ¬ SourceClaim
intrinsic_witness :
  prefixWord delta anti 5 = w ∧ theta false w = w ∧
  (∀ i (hi : i < w.length), w[i] = infiniteWord delta anti i) ∧
  (∀ g : Finset (Fin w.length), Attractor w g → 4 < g.card)
```

No mathematical premise remains on source_refuted or intrinsic_witness. No size-five upper optimum, minimal counterexample length, or uniform replacement bound is claimed or required.

## Fresh replay and declaration audit

Pinned compiler hash is `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`; mathlib revision is `d13f23b723b8a846827a245b89c10fc7d3f11612`. before-pins.log and after-pins.log verify the compiler, manifest and all nine actual package HEADs by filesystem reads, without git operations. The exact package pins are preserved in extracted/pins.json.

Strict serial compilation of Closure, Words, Geometry, Attractor, Endpoint and independent audit passed: -j1 -M2700, warningAsError=true, autoImplicit=false. Per-run logs and guard receipts are in extracted/. Maximum sampled groupRSS was2,123,067,392 bytes (audit); Geometry took10.825s; all six invocations passed below RSS2800MiB CPU210 wall230. No cap was raised. All Python/helper runs used the required external helper_guard.py with AS/groupRSS512MiB CPU210 wall230 and the mandated single-thread/no-bytecode environment. The Lean child alone starts a separate monitored session with no extra AS cap, as explicitly authorized; replay_guard.py restores infinity only for that Lean child, retaining the helper's512MiB cap. This prevents helper AS512 from accidentally constraining the authorized Lean invocation.

The inspected audit selects declarations by env.getModuleIdxFor? against actual module names, never by namespace. The complete fresh IndependentAudit.log prints actual types, module origins, safety and transitive #print axioms for every private/generated/instance declaration. check.py independently parses every block; independent-audit.json records all120: Closure30, Words28, Geometry5, Attractor50, Endpoint7. Every definition is safe; no partial or unsafe declaration survives. Only propext, Classical.choice, Quot.sound occur transitively. No sorry/admit/new axiom/native_decide escape appears. Generated proof declarations are included; historical partial prefixWord helper is absent. Upstream truth is accepted as instructed, not re-audited. Original/copy source pairs and pins were checked before and after replay; final verification checks all archive members again.

## Closest primary bodies and substantive objection

I independently froze and read the needed actual extracted primary bodies, rather than relying only on the preliminary review's conclusions. Exact text digests and immutable paths are in primary-freeze.json. Coverage was targeted: Dolce Theorem1, Example5, proof setup and Step1, conclusion of the remaining cases and §5; Schaeffer–Shallit Theorems1–2 and full first-order proof; Banbara Lemmas41–44, Theorem43 and its proof; Faro coverage definitions/Proposition3.2 proof, Lemma5.1 full interval-forcing argument and Theorem5.4 proof. I do not claim to audit every Dolce table or every comparison-paper appendix.

Dolce (WORDS2023 pp.117–129, DOI10.1007/978-3-031-33180-0_9) proves an upper bound five for all Thue–Morse factors and exhibits a length50 factor requiring five. Its construction transfers and adjusts canonical-block attractors. It does not assert that its example is a mixed-closure defining prefix. More decisively, this w contains01010. A Thue–Morse word under 0→01,1→10 has no triple equal letters; a length-five alternating occurrence at either alignment would force three equal preimage letters. Hence w is not even a Thue–Morse factor, including after complement/reversal. No factor-domain theorem specializes to this exact witness.

Schaeffer–Shallit arXiv:2012.06840v6 Theorem2 gives decidability/construction for prefixes of a specified automatic sequence, allowing repeated attractor positions. This generic machinery supplies neither our mixed directive nor a prior source refutation. Banbara arXiv:2602.16152v3 Theorem43 classifies32 optimal attractors of canonical power-of-two Thue–Morse words for n≥6, with halving and short forbidden factors. Faro–Marino–Pavone arXiv:2610.10950v1 Theorem5.4 has that same canonical scope. A length36 word is not one of these canonical words, and the stronger factor exclusion above defeats the obvious transfer bridge.

Faro's general coverage/hitting-set equivalence and minimal-coverage reduction are classical machinery directly relevant here. Its sixteen-witness interval-forcing method is close to the eleven-factor obstruction. No novelty is claimed for finite hitting sets, interval arithmetic, bounded search, padding or decidability. The candidate contribution is the source-admissible mixed-closure counterexample defeating the published full-domain bound. I found no concrete overlooked theorem-to-source subsumption bridge in the bodies read. Elementary proof size alone does not establish routine known-corollary status. Root must still adjudicate substantive credit against any additional concrete bridge.

Chronology preserved from frozen primary/version evidence: Dolce2023; source v1 2023-08-01, v5 2024-09-15, journal2024 (arXiv reference dates2024-11-04); Banbara v1 2026-02-18/v3 2026-10-12; Faro v1 2026-10-07; local candidate/reviews2026-10-30. All comparison works precede this candidate. No inter-paper priority dispute is adjudicated.

## Remaining gates and access limits

NOVELTY HOLD remains: current public proof registries, inaccessible historical intervals, full citing-literature and possible same-object resolutions are not cleared. No new network request was needed for this finite certificate review. Denied GitHub API/raw/codeload/diff/patch, ScienceDirect and Google challenge routes remain parked, without proxy, TLS disabling, browser bypass or repeated HEAD loops. Failed access gives no novelty evidence. A lawful accessible same-object primary resolution, if located, must be read and compared exactly; generic algorithms alone are insufficient. Root must document bounded registry/citation limits under campaign standards, resolve any actual subsumer, make its substantive-credit decision, and complete the manuscript/final publication packet and required independent/root qualification. No manuscript was edited or audited here.

FAILURES.md preserves this review's archive-rebuild failure and truncated-display limitations; inherited source/formal failures remain in the unchanged archive. No shared/git/public/browser/MathDB/manuscript edit, new mathematical formalization, acceptance or count change occurred. manifest.json excludes itself and verification-receipt.json; a separate guarded verification after final writes checks it, frozen scientific pairs, pins and archive bytes. The receipt, rather than this prose, records the verification result.
