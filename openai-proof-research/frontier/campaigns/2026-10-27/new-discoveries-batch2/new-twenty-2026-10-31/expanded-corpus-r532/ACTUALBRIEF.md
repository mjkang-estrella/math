# ACTUALBRIEF, lane expanded-corpus-r532

Claude Opus 5.5, high effort. No children, no fallback, no Lean, no programs for mathematics. Root alone adjudicates. Credit claimed: 0. Current count unchanged by this lane.

## Outcome

One author-complete ordinary argument with contested significance (344875). No candidate is claimed as qualified.

| ID | Outcome |
|---|---|
| 344875 | Author-complete: printed constant false for every k>=4; exact leading constant for every k. Significance contested. FULLCANDIDATE.md |
| 330067 | Refuted by covering-array limit (and trivially at d=1). Recommend routine, zero |
| 339249 | Clause (1) refuted under G(n,1/2) by routine spectral argument; clause (2) unpaid. Recommend zero |
| 364797 | Source-own public (2409.10129 Theorem 1.8, Remark 2). Zero |
| 330915, 328539, 373109, 365985 | Parked with precise gaps |
| 345483 | Lower half only, parked |
| 345149, 324028, 371954, 354845, 347828, 334450, 328248, 328573, 380420, 368882, 348815 | Parked after the literal only; sources unread. These gaps are not open-status certifications |

Twenty ID-keyed gates with full provenance are in results.json. Derivations and failed mechanisms are in ORDINARY-DERIVATIONS.md.

## 344875 in brief

With l=floor(k/2), u=ceil(k/2), beta_k=(l^l u^u)^{1/k}: for every k>=2, beta_k n^{1/k} - l + 1 <= chi_L(S_n(k)) <= beta_k n^{1/k} + C_k for large n. The printed constant kappa_k = ((k-1)/2) 4^{1/k} exceeds beta_k for every k>=4 (k=4: 2 against 2.1213), and agrees at k=2,3.
Mechanism: a color of depth s can matter to a first-level vertex only at arm positions s and s+1, and a color confined to positions s, s+1 is fully readable from any vertex because the two candidate distances differ in parity.

## Required adversarial report

I tried to find a generic proof, a parameter family containing the target, or a complete source reduction.
* 344875: no outside theorem found. But the lower-bound half is the direct general-k form of the source's Theorem 5.3 count, and the printed constant is exactly the value of that count at a uniform level allocation (my reconstruction). The refutation is, in effect, a better allocation plus a one-paragraph construction, about a page in total. That routine-extension objection is serious and I could not defeat it. The k=4 witness alone resembles the two-term tuning the user declined; the only sensible unit of credit would be the all-k exact-constant theorem.
* 330067: yes, a complete reduction to the classical covering-array limit. Recommend exclusion.
* 339249: yes, a routine spectral argument, and the clause looks like a source slip. Recommend zero.

## Lean needs by main route

* 344875: k=4 suffices for the literal negation, and only the construction half is needed: explicit palm graph, spider distances, a coloring on (b(b-1))^2 arms, one elementary limit with a real fourth root. Finite and feasible with specific imports; DORMANT-SOL-FORMAL-PLAN.md. The all-k theorem roughly doubles it and adds AM-GM.
* 330067: would require formalising the covering-array limit, or at least an o(d^2) log t bound; expensive, and not recommended given the routine finding. The d=1 failure is trivial and carries no credit.
* 339249 clause (1): random-matrix norm and eigenvector bounds in Lean; expensive; not recommended.

## Source and access inventory

Bodies read with pdftotext only. No figures and no visual glyph inspection were done, so printed formulas were read from the text layer.
* 1912.05775v2: whole text extracted; Sections 1 and 5 and Theorem 5.1-5.3 proofs read in full; Sections 2-4 only partly. Listing page shows v1, v2. Final or correction status not established.
* 1503.02380v1: Sections 1-3 passages and Conjectures 5, 8 read.
* 1805.05483: Definition 4.1, Propositions 4.2-4.5, Section 7 end, Conjecture 8.1 read.
* 1408.1940v1: Introduction, Section 2 through Conjecture 2.11 and Lemma 2.13 read.
* 2602.11773: Introduction through Conjecture 2 read.
* 2409.10129v1: Introduction, Theorems 1.7-1.8, Remarks 1-2 read; proofs not audited.
* 1507.04169v2: Introduction through the Conjecture read.
* 1503.08876v1: Theorems 1-2 and related remarks read. Original Gargano-Korner-Vaccaro body unread.
Thirteen assigned source works unread: those of 345149, 324028, 371954, 354845, 347828, 334450, 328248, 328573, 380420, 368882, 345483, 365985, 348815.

GET: 9 charged hops, 9 HTTPS 200 successes (8 PDF, 1 HTML), 0 redirects, 0 unavailable, no new denial. Per-ID charges: 344875 two, 330067 two, 339249 one, 328539 one, 373109 one, 364797 one, 330915 one.
Search: 3 calls, 3 strings, all precharged, every response saved in the very next tool call (search-responses/). Search excerpts are navigation only.
History: all 930 allowlisted paths passed the protected-name filter before open, 0 skipped. No record for any of the twenty IDs. Same-source neighbours are distinct targets (339208, 334451, 334452, 365982, 371953, 345481, 348816). Keyword scans for locating-chromatic, Stanley sequence, covering array, hyperenergetic found only distinct families. I did not compare all 96 accepted scopes one by one, so family non-overlap is bounded to those scans.
Corpus: twenty original lines bound with raw-line hash including trailing newline, statement token hash and decoded statement hash (corpus-bindings.json).

## Procedural disclosures

* All TASK.txt (150995 chars, 11 chunks) and inherited-denials.json (296197 chars, 20 chunks) were read in contiguous chunks of at most 15000 characters before any network use; receipts read-task-* and read-denials-*.
* Bootstrap output exceeded the display limit; the harness saved it to a file that I did not read. TASK was read through the runner instead.
* write_lane.py calls for prose and search responses used an outer timeout of 30 s rather than 140 s; they were direct writer calls, not runner jobs.
* Resource telemetry is the runner's sampled values only; native tool and writer peaks are unknown. No universal process compliance is claimed.
* results.json was patched once before sealing; the change is recorded in its corrections field.
* No failed receipts occurred.
* Sources were cited only for the math above; the search responses list their own result URLs in full.

## Unpaid gates for everything here

Independent proof review, final-source and correction checks, current registry and worldwide prior art, significance adjudication, formal work, paper and acceptance.
