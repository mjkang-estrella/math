# expanded-corpus-r164 research report

One strong computational lead, **333709**, is held for formal completion and independent review. There are **zero accepted solutions**. Of the other 19 reserved records, five are excluded by already printed results and fourteen are parked. results.json has exactly the 20 reserved ID keys, with literal statements, raw/chunk/statement hashes, source receipts, actual review depth, attempts, and remaining gaps.

## Candidate 333709

The proposed refutation is PG(2,5), infection rate 5: there is no inclusion-minimal percolating set whose synchronous percolation time is exactly two rounds. This directly targets source Conjecture 20. It is not a minimum-cardinality reinterpretation. The source's preceding three-round construction does not cover r=5 at q=5.

The exact symmetry-reduced CNF has 1085 variables and 7940 clauses. A noncollinear seed triple is normalized by a projective change of basis. Minimality is represented by arbitrary closed separators after each deletion, so it is not truncated to two-round deletion behavior. CANDIDATE.md gives the full ordinary completeness and normalization arguments.

CaDiCaL emitted a textual LRAT proof of UNSAT. A separate Python RUP implementation verified all 106465 clause additions, culminating in the empty clause. The retained dependency cone has 82646 additions. This is reproducible ordinary computational evidence with an independently checked proof trace, **not a kernel-checked refutation**.

lean/PlaneData.lean defines the literal plane and exact source predicates. Its plane-incidence and explicit three-round-witness diagnostic checks passed strict Lean compilation, a fresh strict rebuild, and module-specific leanchecker, with only propext in their printed axioms. These auxiliary declarations do not prove the target negation. The full semantic bridge, projective normalization, and kernel UNSAT replay remain open formal tasks. The packet is explicitly incomplete; no surrogate theorem is counted as the source theorem.

Main files:

* CANDIDATE.md — mathematical argument, novelty boundary and precise formal gaps.
* outputs/percolation-sym-5-5.cnf — exact normalized input.
* outputs/percolation-5-5.lrat and outputs/percolation-5-5-trim.lrat — full and dependency-trimmed certificates.
* outputs/lrat-check.json and scripts/check_lrat.py — independent RUP check and implementation.
* lean/PlaneData.lean, lean/README.md and Lean-packet.zip — incomplete Lean packet and its honest scope.

## Other mathematical investigations

* **332342:** current source verified n<=13. Residual de Bruijn searches produced fully checked words in 35 of 39 selected position cases at n=14,15,16. Four selected cases remain unresolved, and no nonexistence is claimed. The initial all-zero-prefix prototype was structurally unsuitable; its negative output is not mathematical coverage.
* **337293:** all 74 odd unlabelled trees on 16 vertices were generated canonically by adjoining two leaves; all received checked set-sequential labelings, including ten SAT-rescued cases. This extends a bounded check, not the universal conjecture. The 192 generated trees on 18 vertices were not target labeling tests.
* **337830:** all 1580 sampled cubic graph instances over even orders 4 through 70 received checked colorings. Half were generated as three perfect matchings and checked with two weak plus three strong colors; half were configuration-model simple cubic graphs checked with two weak plus four strong colors. Duplicates/disconnected samples are possible. The later >70-vertex theorem does not settle all reserved scopes.
* **337410:** retained results for 27 multipartite host pairs. Several upper-degree thresholds are unknown. The final host exceeded the approximately 6 GiB group RSS cap and was killed; there was no background restart and no exact Ramsey-table claim.
* **333364:** exhaustive block-count analysis for 112 parameter triples found failures of the proposed augmented strategy, including t=17,f=4,d=10. It does not disprove existence of another discreet strategy. The obstruction is therefore uncredited.
* **334104:** 240 SAT coloring instances on 40 sampled planar graphs of orders 8,12,16,24,32 passed direct semantic checks. No finite obstruction found.
* **333709 positive controls:** two-round minimal witnesses independently checked at (q,r)=(4,4),(5,4),(7,4),(7,5). Initial unsymmetrized SAT runs for some other cases timed out; those are unknown. The decisive q=5,r=5 normalized run returned UNSAT. An explicit three-round minimality-separator certificate is retained as an auxiliary diagnostic.

The five exclusions are 332965 (the cited source's Theorem 2.12), 334705 (proved in its own source), 337517 (Guo–Zhou 2018, with an independent Lin–Huang–Xue proof also located), 334219 (public October 31, 2026 refutation by Kwon–Park–Sano), and 333862 (explicit 2014 full-scope theorem; original r=5 proof body not audited). The other deep structural, analytic, sunflower, colored-Tverberg and Sheehan routes received source-backed dispositions, without pretending a small sample could settle their quantifiers. 333533 was parked with the credited stable-Kneser family warning; its chromatic target was not falsely identified with the credited diameter statement.

## Registry and source coverage

outputs/registry-screen.json records the current /commits/HEAD heads, immutable bytes, queries and hits. Lean Pool head 01db1d7049cf9668bda1e9e106875ee1278b43e6 was screened using LeanPool/projects.yml and every candidates file. Omega head was 6974dba01daa1a25cc74b87a86c191e95fe2c681; complete D5 and Problems subtrees were fetched because the root listing was truncated. OpenAI/math head was 4eaee87548250b2682affda7d05d947c05554bae; its complete preprints subtree was fetched. No exact candidate proof was identified by these bounded screens. This is not all-proof semantic clearance.

GitHub source-ID searches were made for all 20 records, with title/author searches for the investigated leading routes and an expanded author screen for 333709. The final numeric-ID query returned 403 rate-limit exceeded; it was not retried and no further GitHub requests were made. The earlier candidate source-ID/title/author queries succeeded. One author query returned a word-representable-graph repository, not a demonstrated proof of the universal-partial-word target. The dynamic-coloring source-ID query happened after its small diagnostic sweep; no candidate was advanced from that sweep.

All 20 current arXiv abstract/version histories and current PDFs were fetched. Latest bodies were used. This does not mean every historical version, publisher body, citing paper or registry proof was read. Source-access and novelty limits remain material for 333709.

## Resources and verification limits

Numerical/SAT/Lean processes used scripts/limited.py: two-CPU affinity, CPU120s, wall140s, MALLOC_ARENA_MAX=2, and a sampled process-group RSS watchdog at approximately6GiB. One heavy numerical process ran at a time. Lean invocations used -M3500. Full logs and receipts are retained. Sampling is not a transient-peak/cgroup guarantee. The Ramsey run hit the RSS limit. The first auxiliary Lean attempt failed because of a notation/type error and kernel memory consumption while repeatedly computing deletion closures; the revised version uses explicit closed separators and passed. No compiled reduction axiom, sorry, admit, unsafe, native_decide or ofReduceBool was used in the final auxiliary source.

This was a focused pass of roughly half an hour, not the several-hour completed-discovery pipeline described in the brief. It stops with a substantive reproducible candidate and a real formal replay/semantic gap, not a claimed accepted solution. The 82646-step kernel replay was not attempted as one uncapped Lean process. Upstream Std prebuilt oleans are trusted; no full upstream rebuild claim is made. No jobs are intended to remain at handback.

## Write-scope incident

An inline fetch helper accidentally resolved its lane directory to the parent because __file__ was <stdin>. It failed to save a response in the parent's nonexistent sources directory, then appended one HTTP receipt to the parent's existing outputs/http.jsonl. This is an actual violation of the write-only-in-lane rule. No outside file was subsequently edited or removed. The exact timestamp, path and receipt are documented in outputs/compliance-incident.json. All subsequent inline fetches use runpy with the actual script path. No git, child agents, browser tabs, accounts, messages, uploads, ledger or index edits were performed.
