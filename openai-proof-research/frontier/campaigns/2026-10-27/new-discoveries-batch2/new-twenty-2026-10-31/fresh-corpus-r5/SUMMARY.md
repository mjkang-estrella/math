# fresh-corpus-r5 handoff

One full-scope Lean candidate: **MathDB 326640**, the exact complete-bipartite majority out-domination formula, Conjecture 4.10 of Ebadi–Manrique–Jafary–Manora (2013). No acceptance or count edit: **worker credit claimed = 0** pending independent fidelity, novelty and significance reviews. The campaign's existing 1/20 count is unchanged.

The proof is structural for every positive r≤s, retaining the source's DOM≠1 hypothesis. It proves DOM=2 when s≤r+2 and DOM=ceil((s−r)/2) otherwise. The new route uses an extremal opposite-part pair of vertices, then adds uncovered vertices. The all-arcs-toward-the-smaller-part orientation gives sharpness. It is a full infinite-family sharp formula, not a parameter case. Its elementary character is explicitly a significance-review question; no routine-corollary clearance is asserted.

## Deliverables

- `PROOF.md`: exact definitions, complete ordinary proof, Lean bridges, bounded prior-art investigation and access/priority limits.
- `packet/Majority.lean`: complete theorem `Majority.mathdb_326640`, plus orientation representation, exact minimum/maximum semantics, majority threshold and ceiling spelling. No source facts assumed as new axioms.
- `packet/replay.py`, `lake-manifest.json`, `lean-toolchain`, `README.md`: portable source packet; `majority-326640-packet.zip` and `packet-sha256.json`.
- `fresh-extraction/result.json`, `lean.stdout.log`, `lean.stderr.log`, `leanchecker.log`: extracted replay, warnings-as-errors, allowed-axiom audit and separate leanchecker pass.
- `results.json`: **40 entries keyed by MathDB ID**, each with full literal statement, chunk/1-based line/SHA256, actual review depth, compact disposition and zero claimed credit.
- `literal-records.json`: exact extracted corpus records with raw-line SHA256 (including newline).
- `OTHER-ATTEMPTS.md`: sustained mathematical attempts on 326519 and 325921, with decisive remaining obstructions.
- `diagnostics.py`/`diagnostics.json`: reproducible exact GT calculations for two fixed shapes, k=1,…,6. No sweep or finite evidence is used as proof.
- `receipts*.json` and corresponding `.body`/`.txt`: timestamped source and registry receipts, response hashes, access failures. `fetch.py` and `fetch2.py` reproduce the HTTP batches with at most two concurrent requests.
- `input-bindings.json`, `old-note-hits.json`, `reservation-check.json`: input hashes, bounded historical-note search results and r3/r4 disjointness.

## Coverage honesty

All **40/40 full literal statements** were read, not just titles/routing flags. **Three** were selected for sustained mathematical investigation: 325921, 326519, 326640. **Five distinct records** reached exact primary definitions and relevant proof-body reading: those three plus known public results 326662 and 326702. The other **35** remain literal-screen depth; 326562 has related primary evidence from the square-coloring paper but its own full source was not read. No exhaustive primary review or global historical clearance is claimed.

For 325921, v1 Conjecture 16 is the literal projection-fibre statement; v3 changes to cumulative lexicographic counts. The two all-pattern polynomiality assertions are equivalent by the telescoping identities recorded in OTHER-ATTEMPTS.md. General Ehrhart theory only yields quasi-polynomiality; period cancellation remains the decisive gap. The diagnostic values agree with the bridge but prove no polynomiality theorem.

For 326519, the source's attachment suppression introduces a root at floor(x0), losing arbitrary separation. Disjoint products and clique joins also do not amplify the source example's gap. Clique blow-up quotients have potentially large roots but the orbit average sign remains unproved. No formal endpoint is claimed for either unresolved target.

326662 and 326702 are explicitly excluded as old public theorems after reading actual theorem/proof sections. Other problems have compact hold reasons in results.json; open labels and empty solution arrays were not interpreted as novelty.

## Formal verification

Lean **4.34.1**, mathlib **d13f23b723b8a846827a245b89c10fc7d3f11612**. The replayer verified every package's revision metadata without git commands or dependency writes. Fresh copied source compiled with `-j2 -DwarningAsError=true`, exit 0, about 5 seconds. Four #print axioms audits (literal endpoint plus three major semantic bridges) each report only **propext, Classical.choice, Quot.sound**. Separate `leanchecker Majority` exited 0, about 3 seconds. An initial checker invocation lacked `lean` on PATH; this was corrected and is recorded honestly in result.json. No finite checker/oracle or forbidden proof mechanism is used.

Source SHA256: `751ac866bed61eb765969f5ea08e53c582f79431400786e418cfd1278e07d850`.

The extracted replay uses the supplied already-built dependency cache, not a new network build of mathlib. Its output is solely inside this lane.

## Current source and registry scope

Checks occurred 2026-11-01 UTC / 2026-10-31 America/Los_Angeles. Live arXiv primary PDFs were obtained with hashes and read versions: 1311.0479v1, 1310.3792v1, 1307.3999v1 and v3; known-result checks used 1311.1251v2 and 1311.4147v2. Definitions and theorem chronology are discussed in PROOF.md and OTHER-ATTEMPTS.md.

Current Palomar revision **651**, release `ff01fa2bd3240170cedf26fba4b146111e3b132a8c11fe533e5cea0a9fe75287`. Exact queries and broader domination/chromatic queries were compared by actual returned scopes. Empty entries are **not** novelty clearance. Current openai/math head **4eaee87548250b2682affda7d05d947c05554bae**, dated 2026-10-30. The first recursive root tree was truncated; a separate untruncated preprints subtree was fetched and screened. No relevant title was found, but unrelated manuscript bodies were not exhaustively read. MathDB returned **403 once** and was not retried or bypassed. The 1996 orientable-domination paper and complete 2020 domination handbook are unread full-body prior-art limits, and absolute priority is not certified.

Ancestor rules, prior campaign families and current ledger were read. A bounded historical-note scan found no substantive target-specific earlier assessment for the three selected IDs; raw results contain inventory and hash-substring false positives, not clearance. Reservation selection alone does not clear all old work. r3/r4 overlap checks are empty. Parked trace/packing and credited clutter were not pursued. No shared ledgers, git operations, publication, browser tabs or subagents were used.

## Parent's next step

Send the 326640 packet and PROOF.md for separate independent literal-statement/formal review and novelty/significance review, particularly whether an older general orientable-domination theorem subsumes the elementary degree argument. A manuscript and acceptance decision come later; the worker has made neither.
