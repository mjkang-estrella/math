from pathlib import Path
import hashlib,json,subprocess
p=Path("/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/cmdrr-five-three-formal-sol-r4")
def sha(f):
    h=hashlib.sha256()
    with f.open("rb") as r:
        for b in iter(lambda:r.read(65536),b""):h.update(b)
    return h.hexdigest()
def write(n,s):subprocess.run(["python3","-I","-B",str(p/"write_lane.py"),n],input=s,text=True,check=True)
receipts=[]
for f in sorted((p/"receipt").iterdir()):
    if f.suffix==".json":
        d=json.loads(f.read_text())
        assert d.get("group_members_left",[])==[],f
        if "log" in d:
            q=Path(d["log"]); assert q.resolve().is_relative_to(p/"logs")
            assert sha(q)==d["log_sha256"],f
        receipts.append(dict(path=str(f.relative_to(p)),sha256=sha(f),**d))
replay=json.loads((p/"results/REPLAY-R4.json").read_text())
for m in replay["order"]:
    assert sha(p/"src"/(m+".lean"))==replay["sources_after_checkers"][m]
    assert sha(p/"extracted-r4/src"/(m+".lean"))==replay["sources_after_checkers"][m]
    assert sha(p/"extracted-r4/build"/(m+".olean"))==replay["oleans_after_checkers"][m]
for m in json.loads((p/"SOURCE-BASELINE-ORDER.json").read_text())["order"]:
    assert sha(p/"src"/(m+".lean"))==sha(p/"inputs/baseline-src"/(m+".lean"))
audit=json.loads((p/"audit/FINAL-AUDIT-SUMMARY.json").read_text())
positive=[r for r in receipts if r["label"]=="isolated-NegativeOriginal"][-1]
neg1=[r for r in receipts if r["label"]=="isolated-NegativeRepeat"][-1]
neg2=[r for r in receipts if r["label"]=="isolated-NegativePartner"][-1]
assert [positive["exit"],neg1["exit"],neg2["exit"]]==[0,1,1]
for r in [neg1,neg2]:
    s=Path(r["log"]).read_text()
    assert "is false" in s and "unknownIdentifier" not in s
for m in replay["order"]:
    for phase in ["strict","checker"]:
        rr=[r for r in receipts if r["label"]=="replay_"+phase+"_"+m][-1]
        assert rr["exit"]==0
modules=[]
for m in replay["order"]:
    rr=[r for r in receipts if r["label"]=="lean_"+m][-1]
    assert rr["exit"]==0
    assert rr["source_sha256"]==sha(p/"src"/(m+".lean"))
    modules.append(dict(module=m,source_sha256=sha(p/"src"/(m+".lean")),
        working_olean_sha256=sha(p/"build"/(m+".olean")),
        replay_olean_sha256=replay["oleans_after_checkers"][m],
        latest_strict_receipt=rr["path"],latest_strict_exit=rr["exit"]))
qa=dict(pdf="output/pdf/cmdrr-five-three.pdf",pdf_sha256=sha(p/"output/pdf/cmdrr-five-three.pdf"),
pages=[dict(page=i,path="output/pdf/paper-"+str(i)+".png",
sha256=sha(p/"output/pdf"/("paper-"+str(i)+".png")),visually_inspected=True,
finding="legible, no clipped text, no overlap; final page-break/footer revision inspected")
for i in range(1,7)],source_definition_pages=[2,3],
scope="Direct view_image documentary displays, no native UI or sampled group telemetry; six latest paper pages actually inspected. Earlier footer issue repaired and every latest page reinspected.")
write("audit/VISUAL-QA.json",json.dumps(qa,indent=1)+"\n")
source_map={
"literal":"inputs/original/original/author/literal326555.jsonl",
"Definition1.2":"CMDRR.Game; CMDRR.Matching; CMDRR.Schedule; CMDRR.Source",
"unordered_occurrences":"CMDRR.Source.partnership_unique; occurrence_eq; game_injective; cellsEquiv",
"canonical_labels":"CMDRR.Matching.canonical_labels; CMDRR.Source.canonical_transport",
"actual_A_B_z":"CMDRR.A; CMDRR.B; CMDRR.z in unchanged CMDRRZeroA",
"row_occurrence_bijection":"CMDRR.Source.row_internal_occurrences",
"weighted_single_games":"CMDRR.Source.female_single_weighted",
"weighted_married_games":"CMDRR.Source.married_women_weighted",
"central_identity":"CMDRR.Source.central_incidence_identity",
"single_two_cycle":"CMDRR.Source.B_add_z_of_single_twoCycle; no_single_twoCycle; single_row_five",
"swapped_columns":"CMDRR.Source.swapped_U_is_C; column_cell_correspondence; spouse_column_four; single_column_five",
"signs":"CMDRR.Source.U_sign; C_sign; T_sign; canonical_sign_contradiction",
"canonical_endpoint":"CMDRR.canonical_noSource",
"arbitrary_source_endpoint":"CMDRR.noSource_five_three",
"literal_universal_endpoint":"CMDRR.universalExistsFiveThree_negation",
"endpoint_scope":"Arbitrary finite occurrence type; arbitrary five-element male/female types; exactly three disjoint spouse pairs; no rounds, Latin or resolvability assumption",
"closure_presence":"audit_summary.py asserts required actual definitions and bridges in universal endpoint closure"
}
write("results/SOURCE-DEFINITION-MAP.json",json.dumps(source_map,indent=1)+"\n")
status=dict(mathdb_id=326555,status="FULL_ENDPOINT_REPLAYED_UNACCEPTED",credit=0,campaign=55,target=60,previous=39,
mathematical_unpaid_lemmas=[],modules=modules,receipts=receipts,audit=audit,replay=replay,visual_qa=qa,
controls=dict(positive=positive["path"],negative_repeat=neg1["path"],negative_partner=neg2["path"],
scope="Source-only isolated copies, unchanged positive object, only semantic multiplicity mutations; contaminated initial failures retained"),
unpaid=["Independent final source-to-Lean/proof/body/manuscript review","Root scientific acceptance and process adjudication","Unresolved historical r3 metadata-traversal/missing-reap breach"],
prior_limits="Unread Berman-Smith2013 companion HTTP403; bounded registry-body coverage; no worldwide novelty claim or new network",
process_limits=["Standalone documentary display exception: timeout20 CPU10 AS512MiB affinity<=2 before reads; named own logs only; no sampled group/native UI telemetry; not compiler-runner execution",
"Initial direct cat runner.py helper read was outside immutable capped runner; disclosed, not retroactively cleared",
"Actual package-manifest mathlib pin was read after first baseline compile but before full empty-build replay; binary hashes/version and PINS were read before baseline. No procedural PASS inferred",
"One mistyped own-log display path failed1; exact failed command recorded in process inventory",
"PDF relative marker path failed1; corrected installed absolute marker succeeded once before current-lane PDF authoring",
"ReportLab unavailable, groff PDF device/MS macros unavailable; plain roff/PS succeeded; invalid render and footer repair preserved",
"Audit-summary parser first recorded closure counts1 by reading only first lines; corrected multiline parsing yields exact closure arrays and verifies required bridges",
"Function orchestration TypeError before write-final-audit did not dispatch a shell command; all later runner receipts preserved"],
technical_acceptance=False)
write("results/326555.json",json.dumps(status,indent=1)+"\n")
write("CHECKPOINT.md","""# Full literal endpoint replayed; unaccepted, credit 0

CMDRRNonexistence.lean strictly proves canonical_noSource, noSource_five_three, and universalExistsFiveThree_negation. No mathematical lemmas remain unpaid. Actual A+B=1+z, B+z=2, arbitrary two-cycle elimination, full row/column cycles and U/C/T sign contradiction are in the transitive endpoint chain.

All 39 current Lean sources compiled and passed module checkers in a source-only extraction from an asserted empty build, with original/extracted source equality and post-checker hashes. The final audit enumerated 271358 environment declarations, 444 production declarations and 9733 reachable body/type nodes. Universal endpoint closure has 9562 declarations; every audited axiom union is the permitted trio. Fifteen exact closures are preserved.

Positive source controls and clean isolated semantic negative controls passed their expected outcomes. A six-page paper was generated after exactly one successful absolute-path PDF marker and all six final rendered pages were visually inspected. Source Definition1.2 final-scan pages66-67 were also inspected.

Exact source/olean/receipt/log hashes, exits, maps, audits, controls, replay and visual QA are in results/326555.json and associated files. The terminal manifest covers remaining terminal receipts separately, with exact self-exclusions.

Independent final source-to-Lean/proof/deep-body/manuscript review, root acceptance and process adjudication remain unpaid. The historical r3 traversal/missing-reap breach remains UNRESOLVED/UNACCEPTED. Current r4 direct-helper-read, late package-pin metadata read, standalone own-log display exception and all failed attempts are disclosed in results and process inventory. No blanket procedural PASS is asserted. Berman-Smith2013body403 and bounded prior limits remain; no worldwide novelty claim.

Credit0. Campaign55/60 beyond39. No ledger or git changes, network or children.
""")
write("SUMMARY.md","""Full source-bound nonexistence endpoint is kernel checked and source-only replayed. See CHECKPOINT.md, results/326555.json, src/CMDRRNonexistence.lean and output/pdf/cmdrr-five-three.pdf. No mathematical lemmas remain unpaid. Independent final review and root acceptance/process adjudication remain unpaid; historical r3 breach unresolved/unaccepted. Credit0, campaign55/60 beyond39.
""")
print("FINAL_STATE",status["status"],len(modules),"UNPAID",status["unpaid"])
