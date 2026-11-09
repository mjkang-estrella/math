# Fresh corpus r2 — research handback

**Zero accepted discoveries; zero complete Lean endpoints.** All40 reserved literal statements were read, with immutable ID/chunk/line/content hashes. Four targets received primary-statement and relevant proof-body review;36 received literal-only screening. `results.json` is keyed by all40 MathDB IDs and distinguishes these depths. No routing reviewed:false flag was treated as coverage evidence.

The strongest ordinary deduction is a full proof of all three deviation conjectures (323512): [G:H] divides Δ, Δ divides |G|, and Δ=1 iff H=G. Two independent constructions are written in `DEVIATION-PROOF.md`: augmentation plus the characteristic-family Burnside idempotent, and a direct subgroup-lattice Möbius formula with its fixed-point mark calculation. The source's own equation5.15 already contains the substantial classical ingredient. This is held out of discovery credit as a routine-corollary route under the user's standard, with novelty/significance not independently cleared. It is NOT a formal solution: the Burnside/marks/induction semantic bridges are not implemented in Lean. No axiom-based surrogate or arithmetic helper packet is supplied.

323293 is **known**: Minghua Lin arXiv1212.1934v1, dated9Dec2012, explicitly proves the exact determinant bound with sharpness. Its full proof was read and compared to original Conjecture8.3. An independent spectral proof was also worked out and recorded, without claiming it as discovery.

323289 has a decisive **source-fidelity/known-result exclusion**: the original March2012 source itself reports torus capacity12 at n=14. The literal record's a(14) is16. A new formal verification of this already reported counterexample would not earn discovery credit. The proposed divisor-function conjecture was not found in the supplied primary source. No fresh giant finite search was attempted.

Fallback323062 remains **parked**. The original game definition and proofs were read, as were the2019 EJC proof of eventual greedy play and period2k for a single subtraction heap. That primary theorem does not literally settle the fixed-side-heap endpoint. Three approaches were pursued: exact recurrence/finite-state cycles, the greedy-sacrifice/rearrangement proof, and induction on side-heap size. The next decisive lemma is eventual optimality of the greedy main-heap action despite side-heap options. The bounded exact single-process probe (1200 rule pairs, main heap≤256, side heap≤6) gives no persistent tail counterexample but is not a theorem. The bare all-n equality has transient failures, excluded as an endpoint/wording correction because source prose explicitly intends sufficiently large n.

Compact dispositions for the other36 are in `results.json`; this does not assert primary-body review or current-resolution certification for those records. Two of them (323097,323476) explicitly say in their literal statements that their sources prove the assertion, so they are excluded at that review depth.

## Provenance and access

Read applicable ancestor AGENTS, campaign ledger, batch ledger and original prior-campaign context. Old39 families remain excluded. Historical note scans are retained in `old-note-hits.json` and the boundary-filtered `old-note-exact-hits.json`; raw substring hits often match numeric experiment data and hashes. No previous technical investigation of the four selected targets was located in the scanned human notes/result-review files. This bounded search is not a claim that the old repository contains no work on the underlying subject. The old322907 hit is merely an inventory line.

Primary downloads, versions, UTC dates and SHA256 receipts: `source-receipts.json`, `additional-receipts.json`, `cumulative-receipt.json`. PDF header versions: torus1203.6604v1, determinant1203.6812v2, deviation1205.3121v1, scoring1202.4655v1, Lin1212.1934v1. The independent review's current successful openai/math head receipt (4eaee87548250b2682affda7d05d947c05554bae) and Palomar revision651 query receipts were hash-checked and referenced in `reused-registry-receipts.json`. They are not target-specific clearance.

All three target-specific Palomar requests and all four live MathDB page requests returned403. Requests were made once, no denied request was retried, and no access-control bypass or browser tab was used. The Palomar requests were issued in one bounded initial fetch batch. Access failures are recorded honestly in `source-receipts.json` and `live-mathdb-receipts.json`. Primary bodies remained publicly downloadable. Search was used to locate primary literature; keyword absence is not novelty evidence.

## Replay and limitations

Run from this directory:

```
python extract_records.py
python build_results.py
python verify_provenance.py
python deviation_probe.py
python scoring_probe.py
```

`verify_provenance.py` checks every corpus line and chunk hash,40 result bindings and all primary-download hashes. `deviation_probe.py` verifies the exact rational mark construction for every subgroup of S3,A4,S4; this is a sanity check of the general ordinary proof, not a formal proof. `scoring_probe.py` replays the bounded recurrence diagnosis with genuine octal legal-move semantics. Both use a single process and small finite inputs. Logs and machine-readable outputs are included. Fetch scripts are for provenance reproduction and are not part of the offline replay; do not rerun denied registry requests.

Lean4.34.1 executable was checked (commit5045d0056413266e57c625dcd7c365b10e377c52). Existing campaign manifests identify mathlibd13f23b723b8a846827a245b89c10fc7d3f11612, but no Lean packet is claimed or pinned as an implemented solution here. There is consequently no #print axioms or strict extracted Lean replay to pass off as completed. Independent source-fidelity, novelty/significance review and paper production have not been performed by this investigator. All writes stay inside fresh-corpus-r2; no shared ledger, git, publication, child agents or active trace/clutter investigations were touched.
