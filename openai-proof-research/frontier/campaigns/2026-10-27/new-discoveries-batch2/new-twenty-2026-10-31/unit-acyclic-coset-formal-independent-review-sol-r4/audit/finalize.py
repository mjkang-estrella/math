from pathlib import Path
import json,hashlib,collections
p=Path(__file__).resolve().parent.parent
def sha(q): return hashlib.sha256(q.read_bytes()).hexdigest()
def load(n): return json.loads((p/n).read_text())
def save(n,v): (p/n).write_text(json.dumps(v,indent=2))
rs=[]
for q in sorted((p/"receipt").glob("*.json")):
 r=json.loads(q.read_text()); assert r["group_members_left"]==[]
 assert sha(Path(r["log"]))==r["log_sha256"]
 rs.append({"path":str(q.relative_to(p)),"sha256":sha(q),"label":r["label"],"exit":r["exit"],"log":str(Path(r["log"]).relative_to(p)),"log_sha256":r["log_sha256"],"stamp":r["stamp"],"wall_ms":r["wall_ms"],"env":r["env"],"cwd":r["cwd"]})
# This is a snapshot before this program's own receipt; the terminal manifest includes it.
save("results/own-receipt-index.json",rs)
f=load("results/forensics.json"); pr=load("results/process-and-declarations.json")
keyed={"mathdb_id":340110,"review_complete":True,"acceptance":"CLOSED; root only","credit":0,"accepted_new":55,"target_new":60,"previous":39,"total":94,"reviewer":"GPT-6.1 Sol high/default personally; no children/fallback",
"gates":{"literal_source_fidelity":"PASS","ordinary_proof":"PASS","finite_set_and_classical_equality":"PASS","sorted_sequence_fibre_injective_bridges":"PASS","literal_refutation_feedthrough":"PASS: audit/Literal.lean",
"standing_hypotheses":"PASS","all_unit_full_labelled_translation":"PASS","identity_and_constant_sum_controls":"PASS","semantic_negative_probes":"PASS: three expected exits1",
"source_only_replay":"PASS: five builds plus five module kernel checkers; empty build initially","pins_and_binaries":"PASS independently hashed; installed revision metadata verified","all_local_typed_body_DAG_axioms":"PASS: 101/6036/5174; allowed axioms only",
"archive_path_and_source_hashes":"PASS with reporting qualification: generated plan is not original PINS",
"manuscript_visual_QA":"PASS: all four newly rendered pages inspected","manuscript_reporting":"HOLD: exact corrections FINAL-REVIEW.md",
"historical_author_protocol":"HOLD: pins overwrite/reader/overlap/late map; root adjudicates",
"own_protocol":"HOLD for root assessment: shell126, failed inspection, startup direct capped reader and inherited cwd",
"prior_body_comparisons":"PASS bounded nonmatches; inverse method does apply",
"scientific_significance":"RECOMMEND EXCLUDE: routine complete inverse-lemma adaptation, contrary structural significance case documented",
"root_acceptance":"UNPAID"},
"formal_endpoint":"UnitCoset.refutation : not UnitCoset.Conjecture","independent_literal_endpoint":"Independent.literal_refutation",
"counts":f["audit"],"binary_checks":f["binaries"],"mathlib_revision":f["mathlib_revision"],
"source_postchecker_hashes":f["postchecker_hashes"],"author_receipts":pr["author_unique_count"],"author_exits":pr["author_exit_counts"],
"author_log_limit":{"available":79,"matching":79,"not_supplied_cleanroom_logs":15},
"source_inventory_limits":"Every production source and 101 owner/dependency entries inspected; full type/body Expr automatically traversed, not manually read byte by byte. No exhaustive literature, upstream truth or all94 certificate audit.",
"paper_errata":[{"location":"p1 opening paragraph","correction":"Original pins restored exactly; historical FAIL and process hold remain"},{"location":"p4 section7 replay","correction":"Archive generated plan is not restored original PINS; supply separate pins"},{"location":"p4 verification ledger","correction":"94 copied receipts including later terminal seal, not intake93; never alter old results"},{"location":"p3 section5/current status","correction":"Independent adverse significance recommendation and root adjudication now available"}],
"process_pins":{"original_sha256":f["pins_original_sha256"],"overwritten_sha256":f["pins_overwritten_sha256"],"historical_manifest_expected_delta":["PINS.json"],"breach_waived":False},
"resource_limits":"runner affinity<=2 CPU120 AS12GiB sampledRSS6GiB devguard130 wall140 arena2; native/tool/reader/writer limits candid in report",
"unexpected_failures":[{"action":"execute runner.py directly","exit":126,"runner_receipt":None,"reason":"permission denied before runner started"},{"receipt":"receipt/1794108459656597626_inspect.json","exit":1,"reason":"nonexistent writer.py after own-lane listing/runner print; preserved"}],
"receipt_snapshot":"results/own-receipt-index.json; terminal manifest includes all completed receipts",
"unpaid":["Root scientific credit adjudication (exclusion recommended)","Root author and review protocol adjudication","Current manuscript reporting corrections","Root acceptance"],
"final_report":"FINAL-REVIEW.md"}
save("review.json",keyed)
save("results/page-QA.json",{"dpi":110,"render_receipt":"receipt/1794108573509050738_pdf-render.json","pages":[{"page":i,"png":"results/review-page-"+str(i)+".png","sha256":sha(p/("results/review-page-"+str(i)+".png")),"visually_inspected":True,"layout":"readable; no clipping/overlap/missing signs"} for i in range(1,5)],"reporting_errata":keyed["paper_errata"]})
print("Persisted review.json, FINAL-REVIEW.md verified:",(p/"FINAL-REVIEW.md").stat().st_size,"bytes; all completed sampled groups empty.")
