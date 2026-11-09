from pathlib import Path
import json,subprocess,re
p=Path("/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/cmdrr-five-three-formal-sol-r4")
proof=(p/"inputs/original/original/review/INDEPENDENT-PROOF.md").read_text()
proof=proof[proof.index("## Exact object and normalization"):]
proof=proof.replace("No ordinary proof gap remains in this review; all formal counterparts remain unpaid.","The formal endpoints and validation evidence are described below.")
audit=json.loads((p/"audit/FINAL-AUDIT-SUMMARY.json").read_text())
replay=json.loads((p/"results/REPLAY-R4.json").read_text())
intro="""# Nonexistence of a complete mixed doubles round robin tournament CMDRR(5,3)

MathDB 326555 - source-bound theorem and Lean 4.34.1 certificate

Implementation record, 8 November 2026 UTC. Credit 0. Campaign 55/60 beyond 39 prior results. Independent final review and root acceptance are unpaid.

## Abstract

No CMDRR(5,3) satisfying Berman and Wakeling Definition 1.2 exists. Games are unordered pairs of mixed teams and schedules are arbitrary finite collections of occurrences. Three arbitrary disjoint spouse pairs are allowed; neither rounds nor resolvability is assumed. The essential incidence identity A+B=1+z rules out the undetermined 3+2 cycle type in either single row. Sex-swap correspondence then determines all column cycle types. The signs of the row, column and opposite-team permutations contradict their actual composition relation. The literal universal endpoint is kernel checked, and an empty-build source-only replay with module checkers passed. This is an implementation result awaiting independent scientific and process adjudication, not a new-to-literature or acceptance claim.

## Source statement and conventions

The source is David R. Berman and Ian N. Wakeling, Complete Mixed Doubles Round Robin Tournaments, arXiv:1310.5240v1 (19 October 2013), Definition 1.2 on PDF pages 2-3 and Conjecture 2.4 on page 5; the cached published scan places the definition on printed pages 66-67 and the conjecture on page 69. Exact cached files and source hashes are frozen inputs. The MathDB literal delegates the term to the paper; its gloss of k as games/rounds is inaccurate. Here k means disjoint spouse pairs, exactly as in Definition 1.2.

For n men and n women with k disjoint spouse pairs: spouses never share a game; nonspouse mixed pairs partner once and oppose once; a player with a spouse opposes every same-sex player once; each single repeats opposition twice with some other single and opposes all remaining same-sex players once. A mixed game has two different men and two different women. All multiplicities count occurrences, not ordered displays. The proof below uses labels H={1,2,3} and singles 4,5. The Lean canonical model subtracts one from every label, so spouses are 0,1,2 and singles 3,4. A, B and z are unchanged occurrence counts under this stated bijection.

## Theorem

For arbitrary types M,W with Fintype instances, not ExistsFiveThree M W. Expanded: if both cardinalities are 5, any matching of exactly 3 spouse pairs admits no finite occurrence schedule satisfying Source. The occurrence type is quantified inside the existence proposition. No incidence identity, cycle fact or sign premise is supplied as an additional hypothesis.

"""
validation="""
## Formal source-to-definition and proof map

CMDRRBase defines Game as a Finset of exactly two mixed teams with distinct men and women, Matching as a partial one-to-one spouse relation, Schedule.game on an arbitrary occurrence type, count as filtered cardinality, and Source as the six literal multiplicity clauses. ExistsFiveThree quantifies both cardinalities, the matching with count 3, and a finite occurrence type and schedule. No conclusion is included in a structure field.

CMDRROccurrence proves mixed partnership and opposition uniqueness and derives occurrence injectivity. CMDRRCells constructs the actual incidence-to-cell equivalence and opposite-team involution T. CMDRRRows constructs genuine U and C and proves C(T(x))=U(x). Counts gives 22 allowed partnership cells and 11 occurrences. Transport, SourceTransport, Normalize, Canonical and NormalizationBridge prove synchronized relabeling and canonical_transport for arbitrary five-element player sets.

Repeat, SingleCounts, Cycles, FourOrbit, OrbitCard, RowDomain and SpouseCycles establish the genuine restricted row permutations, forced repeated single pair and spouse-row four-cycles. Degree and RowDegree prove complementary internal directed-edge counts by bijective degree balance. Incidence and ZeroA preserve actual two-cycle occurrences and define exactly A, B and z as used in the proof.

IncidenceSums partitions actual occurrences. RowOccurrences proves a bijection from actual row edges to occurrences containing the chosen man, preserving both female endpoints. GameIncidences proves the per-game spouse-man incidence formula. WeightedOccurrences performs Fubini and obtains the single-female incidence sum plus z = 2+A. FemalePairs uses the three unordered pairs in H, spouse avoidance, and occurrence multiplicities to obtain the married-female incidence sum plus B = 3. CentralIdentity proves A+B=1+z without a single-row type premise.

SingleElimination proves preservation of the single-female subset by an oriented two-cycle, the full occurrence partition, B+z=2, the odd-integer contradiction and the arbitrary-orientation bridge. FiveOrbit uses cardinal complements and injectivity to exclude 3+2 and 4+1 decompositions, proving the full five-cycle. This is not an enumeration of permutations or schedules.

Transpose proves the canonical sex-swap source and the explicit swapped U/original C correspondence, including column_cell_correspondence on the actual column domain. ColumnCycles records spouse-column four-cycles and single-column five-cycles. RowSigns proves row signs from actual single-cycle support, and extends each row by the identity on a forbidden wife cell. The disjoint row product has sign -1. Signs bridges the extension to the original 22 cells, applies the entire row argument to the swapped Source for C, obtains signT=-1 from the fixed-point-free involution, and proves the contradiction.

Nonexistence contains canonical_noSource, noSource_five_three and universalExistsFiveThree_negation. The arbitrary endpoint depends transitively on canonical_transport and on the actual Source, A, B, z, central incidence identity, elimination, five-cycle and permutation-sign declarations. The audit explicitly checks their membership in the endpoint closure. ColumnCycles is an explicit additional record of the column classifications; the endpoint sign chain uses the same swapped row classification through canonical_swap_source.

## Validation and reproducibility

Lean is 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52, with mathlib revision d13f23b723b8a846827a245b89c10fc7d3f11612. PINS.json is immutable; actual version, executable hashes and package metadata were checked. Every compile uses -j1 -M3500 -DwarningAsError=true. Permitted transitive axioms are exactly propext, Classical.choice and Quot.sound. No added axiom, sorry, admit, unsafe, native_decide, unchecked certificate or schedule search is used.

CMDRRAuditFinal enumerates the entire imported environment with module origins and body presence, selects production declarations by actual originating modules (including private/generated declarations), traverses types and opaque bodies into an origin-labelled dependency DAG, and prints 15 individual exact endpoint closures and axiom unions. It rejects any disallowed production axiom. This machine audit is not an independent human proof review.

The full replay copied every current Lean source into extracted-r4/src and asserted an empty extracted-r4/build. LEAN_PATH included only that build and pinned upstream packages. Each source compiled strictly in dependency order, then each module passed leanchecker by module name. Original and extracted source hashes were equal before compilation and after every checker completed. No old author or legacy olean was used as a replay input. REPLAY-R4.json and separate true-exit receipts preserve the evidence.

Controls construct the source-valid two-game strict MMDRR(2), test both the one-time mixed partnership and twice repeated single opposition, unordered team symmetry, distinct occurrences, duplicate-partnership detection and a forbidden-spouse violation. Clean isolated copies of Source and this positive object compile without any author modules. Changing repeated same-sex multiplicity from 2 to 1 or mixed partnership multiplicity from 1 to 2 rejects the same positive object with the intended false-proposition diagnostic. The first negative attempts also had a missing sum_boole import and are retained as contaminated failures, not counted as clean controls; corrected identical imports make the unmutated control pass and both semantic mutations fail.

Small explicit control objects, three unordered female pairs, fixed integer/sign calculations and structural four/five-point orbit arguments are kernel-proved. They are not an enumeration of candidate tournament schedules. No mathematical Python, solver, CAS, numerical experiment, new network access or child delegation was used.

## Scientific and process limits

The ordinary proof was independently reviewed in the copied prior source-review record. No independent final source-to-Lean, deep-body, proof or manuscript review has occurred for this completed certificate. Root acceptance and process adjudication remain separate and unpaid. Credit remains 0; the shared campaign ledger remains 55/60 beyond 39 prior. No files outside the exclusive lane were authored and no ledger or git operation was performed.

The bounded prior review did not identify an authenticated applicable prior theorem in the inspected source bodies. The Berman-Smith 2013 companion body returned HTTP403 and remains unread; prior registry-body coverage is limited. These facts do not establish worldwide novelty. No new access or alternate retrieval is claimed in this continuation.

The historical r3 process breach remains UNRESOLVED and UNACCEPTED: an initial workspace-root recursive inventory may have traversed protected metadata; its interrupted run lacks a normal runner receipt and normal group-reap evidence. No protected body bytes were reported read. Later hashes and completed receipts do not cure that missing evidence. The r4 immutable runner changes cwd to its own lane before child dispatch; that prospective repair is not a retroactive waiver.

All r4 exec commands explicitly used the assigned absolute workdir. Substantive reads, Lean execution, audits and rendering used the immutable runner. The root prospectively authorized standalone documentary display of explicitly named own saved logs with timeout20, CPU10 seconds, address-space512MiB and affinity at most2, installed before file reads. Displays are capped at16KiB and tracked with offsets and exits. These displays did not run through the compiler runner and have no sampled group or native UI telemetry. One mistyped own-log timestamp caused FileNotFoundError; no external path was accessed. A wrong lane-relative PDF-marker path returned MODULE_NOT_FOUND; the corrected installed absolute marker succeeded once before current-lane PDF authoring. ReportLab was absent; groff PDF-device and MS-macro attempts failed. Installed plain roff/PostScript generation succeeded, and a pending-line footer issue was fixed after visual inspection. These failures and the rendering retry on an invalid PDF are retained. The initial direct runner-helper display and the first failed visibility handback are preserved in the process inventory.

Runner caps are CPU120 seconds per process, address space12GiB, at most2 CPUs, sampled groupRSS guard6GiB, devguard130 seconds and wall140 seconds, with arena2 and own temporary/cache paths. Completed receipts record true exits and reaping notes; sampling is not a perfect cgroup claim. No blanket procedural PASS or independent acceptance is asserted.

## References and retained evidence

[1] Berman and Wakeling, Complete Mixed Doubles Round Robin Tournaments, arXiv:1310.5240v1, Definition1.2 and Conjecture2.4, cached original and published scan in inputs/original/original/author/sources.

[2] MathDB326555 exact literal: inputs/original/original/author/literal326555.jsonl. Source-bound interpretation and independent ordinary proof: inputs/original/original/review/REVIEW.md and INDEPENDENT-PROOF.md.

[3] Current source certificate: src/CMDRRNonexistence.lean and its imported modules. Full body audit: src/CMDRRAuditFinal.lean, audit/FINAL-AUDIT-SUMMARY.json and audit/ENDPOINT-CLOSURES.json. Replay: results/REPLAY-R4.json. Exact receipts, hashes and process limitations are retained in results/326555.json, CHECKPOINT.md and the terminal manifest.
"""
stats="\nAudit totals: "+str(audit["whole_environment_declarations"])+" environment declarations; "+str(audit["production_declarations"])+" production declarations; "+str(audit["reachable_body_nodes"])+" reachable body/type nodes; "+str(len(audit["endpoint_closure_counts"]))+" exact closures. Full replay: "+str(len(replay["order"]))+" source modules. Universal endpoint closure: "+str(audit["endpoint_closure_counts"]["CMDRR.universalExistsFiveThree_negation"])+" declarations.\n"
text=intro+proof+validation+stats
trans={"→":"->","≠":"!=","≥":">=","≤":"<=","∧":" and ","∀":"for all ","∃":"there exists ","¬":"not ","ℕ":"N","ℤ":"Z","×":" x ","−":"-","–":"-","—":"-","’":"'","‘":"'","“":'"',"”":'"'}
for a,b in trans.items():text=text.replace(a,b)
text=text.encode("ascii","replace").decode()
subprocess.run(["python3","-I","-B",str(p/"write_lane.py"),"manuscript/PAPER.md"],input=text,text=True,check=True)
lines=[".po 0.65i",".ll 7.1i",".pl 11i",".ps 11",".vs 14",
".de TOP",".sp 0.5i","..",".wh 0 TOP",".de FOOT",".ev 1",
".tl 'CMDRR(5,3) - MathDB326555 - credit 0''%'",
".ev","'bp","..",".wh -0.5i FOOT"]
for block in text.split("\n\n"):
    block=block.strip()
    if not block: continue
    if block.startswith("# "):
        lines += [".sp 1v",".ps 17",".vs 21",".ft B",block[2:],".br",".ft R",".ps 11",".vs 14",".sp 1v"]
    elif block.startswith("## "):
        lines += [".sp 1v",".ne 5v",".ft B",".ps 13",block[3:],".br",".ft R",".ps 11",".sp 0.5v"]
    else:
        lines += ([".ne 7v"] if block.startswith("CMDRRAuditFinal enumerates") else [])
        lines += [".sp 0.65v",block.replace("\\","\\e"),".br"]
ms="\n".join(lines)+"\n"
subprocess.run(["python3","-I","-B",str(p/"write_lane.py"),"manuscript/PAPER.roff"],input=ms,text=True,check=True)
out=p/"output/pdf/cmdrr-five-three.pdf"
out.parent.mkdir(parents=True,exist_ok=True)
with (p/"output/pdf/cmdrr-five-three.ps").open("wb") as f:
    subprocess.run(["groff","-Tps",str(p/"manuscript/PAPER.roff")],stdout=f,check=True)
subprocess.run(["ps2pdf",str(p/"output/pdf/cmdrr-five-three.ps"),str(out)],check=True)
print("CREATED",out)
