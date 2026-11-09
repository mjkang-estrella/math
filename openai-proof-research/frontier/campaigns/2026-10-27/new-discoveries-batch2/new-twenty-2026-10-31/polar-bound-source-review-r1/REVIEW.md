# Independent qualification review: MathDB 357910

**Recommendation: EXCLUDE from campaign credit as a short modification of a printed source example. Ordinary mathematics PASS. Full source/version/prior clearance HOLD. Do not authorize Pi implementation for credit. Zero credit; count stays 52/60; root alone adjudicates.**

The twelve-vertex graph is a valid ordinary counterexample to the clique bound in Conjecture 49 of both arXiv versions. I independently verified structural nonpolarity, all twelve vertex-deletion partitions, and hereditary minimality; details are in [ordinary-proof-notes.md](ordinary-proof-notes.md). It violates c≤2k−i−1 and the derived order bound, at k=c=i=4. It does not refute the i interval and makes no minimum-order claim. The finite supplied certificate is not checked Lean.

| Gate | Independent verdict |
|---|---|
| Mathematical validity | PASS, ordinary proof and twelve explicit deletion partitions |
| Literal arXiv/MathDB fidelity | PASS for Conjecture 49, k≥3 and the conjunction of bounds |
| Complete source-object comparison | HOLD: missing journal Sections 3–4 and journal figure pixels; proceedings body missing |
| Version gate | HOLD: arXiv v1/v2 inspected; journal retention as Conj.37 is author-reported but not independently established by the frozen excerpt |
| Prior/routine gate | EXCLUDE recommendation: exact printed example → deletion → twin expansion |
| Bounded novelty investigation | HOLD/incomplete, no worldwide-priority claim |
| Campaign significance | EXCLUDE recommendation under printed-ingredient precedents; ordinary refutation remains correct |
| Pi implementation authorization recommendation | DO NOT PROCEED for campaign credit |

## Decisive source-family finding

The source's example immediately after Conjecture 49 at parameter 3 has C={c1,c2}, I={i1,i2,i3}, with C-I edges c1i2,c1i3,c2i1,c2i3. Delete i3. Replace c1,c2 by true-twin pairs {0,1},{2,3}, and i1,i2 by false-twin pairs {8,9},{10,11}; retain S=2K2 as 45,67. This produces **exactly** the candidate. There are no unmentioned edge edits. The independent deterministic edge reconstruction in finite-data-comparison.json confirms equality with all 32 supplied edges.

This is materially stronger than noticing differing degrees in Figure 3. The latter only proves nonisomorphism. The candidate is a short deletion-and-twin expansion of the printed post-conjecture construction. Moreover, the equal C-deletion witness sets I′0=I′1={8,9} and I′2=I′3={10,11} instantiate precisely the missing-C-pair pattern analyzed in the proof of source Theorem 40. All nonpolarity reasoning is the source Lemma 39 proof specialized to that pattern; the additional minimality work consists of the three short deletion cases.

This is an eligibility recommendation under the user’s printed-example modification exclusion, supported by the actual graph mapping. It is not a claim that twin expansion generally preserves minimal obstruction status, that the authors printed this exact counterexample, or that a later public refutation is known. See [source-family-comparison.md](source-family-comparison.md) for explicit comparison with the pseudo-split constructions, Theorem 27 monopolar examples, all three Remark 32 constructions, H_s before Theorem 38, Remark 47 and the figures.

The strongest objection to exclusion is that the printed example has different parameters and does not already violate the bound; the deletion and twin expansion expose a previously unstated failure. That is true. Short counterexamples can be mathematically useful, and shortness alone is not a rejection criterion. Here, however, there is both a concrete printed-object reduction and an already printed proof mechanism, so this meets the narrower source-modification exclusion. The campaign has excluded correct counterexamples for similarly explicit small alterations (350973; 334721) and a cone/gluing/attachment construction (369935). Root’s 350432 ruling separately excludes a correct full polar proof for source-ingredient dependence. I recommend consistent application; root must decide separately.

## Source/read-depth qualifications and strongest remaining objections

Both listed arXiv versions were available in the frozen inputs. Relevant definitions, Section 2 constructions, Sections 3–4 statements/proofs and concluding example were compared in their extracted texts. The supplied full-page Figure 3 and detail pixels were inspected. The P3/complement-P3 convention is checked against the definitions: A is complete multipartite, B is a cluster of at most four cliques; infinity means no bound on A parts. Empty sides do not affect the proof. No source recognition theorem is being used without a semantic argument; ordinary-proof-notes.md proves the needed bridges directly and also checks Lemma 39. The task's 'Prop 27' is labeled Theorem 27 in the arXiv versions.

A significant provenance limitation emerged: **polar-web-retrieval.json contains only rendered lines through L509**, despite its header advertising 1837 total lines. It ends in journal Section 2 Proposition 7. It does not contain the alleged journal Conjecture 37, journal Sections 3–4 or their proofs. The direct polar-author-journal.body is a 403 page. The author lane may have read later rendered passages interactively, but those passages are not present in this frozen retrieval, and I cannot treat its CANDIDATE.md assertions as independent primary evidence. The exact missing journal comparators are listed in source-family-comparison.md, including Section 4 Conjecture 37 plus the following extremal construction, the Section 3 counterpart of Theorem 40's paired-neighborhood proof, and Figure 2 pixels. No full journal inspection is claimed. The published metadata and scattered indexed passages do not fill this gap.

The proceedings article at DOI 10.1016/j.procs.2023.08.228 was identified, but only indexed abstract/references were accessible here. Its actual body remains unread. The closest related works identified in historical polar-review-r1 include arXiv:2104.07852, 2203.04953 and 2210.02497. I read the historical review's body comparisons, not all those primary bodies anew. This is insufficient for a new full citing-work clearance and remains HOLD, rather than an abstract-based PASS. The MathDB references to 1511.09429/2104.07852 do not themselves establish that those bodies contain this H-split conjecture.

The old 350432 target is cograph uniqueness, not the present bound. This graph is connected (C links S and every I vertex) and has induced P4 8–2–0–10: consecutive edges exist and the three nonconsecutive edges do not. Thus the old target is not a direct subsumption. This separation does not exempt the new candidate from the source-ingredient rule.

## Registry and chronology limits

A fresh https://api.github.com/repos/openai/math/commits/HEAD request at 2026-11-05T21:22:31Z returned **403, API rate limit exceeded**. I stopped that host immediately; no Omega or LeanPool API request was then sent, and no alternate API route/account was used to bypass the denial. live-receipts.json retains the exact URL, UTC, status and hash. Consequently the requested independent current-HEAD clearance was not completed.

I independently processed the existing complete relevant cached OpenAI preprints and Algebra/AlgebraicTopology/Combinatorics/Topology subtrees, Omega D5/Problems/Blueprint subtrees, and LeanPool subtree. The truncated OpenAI lean root was not used as completeness evidence. I also screened the actual cached raw LeanPool/projects.yml and candidates README/decisions/discovered/provenance/shortlist and four txt indexes, not just the author summary. Their hashes/read depths appear in read-inventory.json. The graph-polar terms do not identify an exact candidate counterpart in these indexes. Broad 'polar'/'split' matches include geometric duality, number-field splitting and triangle packing; these are not demonstrated proof-body clearances. No new matched exact theorem/proof body was located or fully audited here.

The cached author snapshots report OpenAI 4eaee87548250b2682affda7d05d947c05554bae, Omega 5ea4a91606667fb2800faa9bec1dbd36976a251f and LeanPool 01db1d7049cf9668bda1e9e106875ee1278b43e6. The user supplies a later Omega 622593005d2dd18d37a84559855df25e18fa2c3c. I have not independently verified that later head, its changes or their chronology. Those are bounded historical screens, not all-code clearance or evidence of no public resolution. Search results retained in web-search.json likewise do not establish worldwide novelty or complete citations coverage.

## Integrity, scope and handback

frozen-before.json and frozen-after.json verify all **536** input paths against frozen-inputs.json, with zero mismatches. No frozen input bytes were edited. Review artifacts, receipts and scripts were written only in the assigned review directory; no recursive evidence-tree copy, git, children, Lean, heavy enumeration, publication/upload, external contacts, browser or account action was performed.

The finite check covers one 32-edge graph, the exact twin reduction, and twelve supplied deletion masks, with tiny local triple checks. It does not enumerate 4096 partitions or execute downloaded scripts. Bounded scripts use CPU120, address-space6GiB and two-core affinity; the registry/check scripts used wall140 timeout. Initial short inline reads/hash checks and inspect_sources.py were not all wrapped in the full resource wrapper; no sampled process-group RSS guarantee is claimed. All commands terminated and no background process was launched. One inspect attempt failed on a JSON string/dict assumption, then was corrected; no input was changed.

Root may retain the ordinary refutation as an uncredited observation. On the present standard, further formalization for campaign credit is not recommended. If root overrides the significance recommendation, full missing source/version/prior gates still need separate resolution before Pi implementation; a future Lean endpoint, independent fidelity review, manuscript and final extracted replay would remain mandatory and are not replaced by this review.
