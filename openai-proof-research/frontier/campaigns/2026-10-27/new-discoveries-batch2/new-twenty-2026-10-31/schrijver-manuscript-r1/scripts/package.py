from pathlib import Path
import json,hashlib,zipfile,datetime
L=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(n,d):(L/n).write_text(json.dumps(d,indent=2)+'\n')
before=json.loads((L/'inputs-before.json').read_text())
after={p:{'sha256':sha(Path(p)),'bytes':Path(p).stat().st_size} for p in before}
write('inputs-after.json',after);assert before==after
write('frozen-integrity.json',{'unchanged':True,'files':len(before),'exceptions':'Initial read-only report access preceded this binding; see operations.json.'})
root=L.parent/'schrijver-parent-final-r1/replay-result.json'
# A newly arrived result needs separate review, never silently overwrite a pending statement.
assert not root.exists(),'Root replay appeared: inspect and revise the pending snapshot before packaging.'
write('root-status.json',{'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'replay_result_present':False,'root_replay':'pending','registry_refresh_copied':True,'accepted_credit':0})
write('raw-record-provenance.json',{'mathdb_id':352827,'original_chunk':'mathdb-normalized-chunk-0008.jsonl','one_based_line':2143,'immediate_read_only_input':'../expanded-corpus-r122/raw/352827.jsonl','output':'mathdb-352827.raw.jsonl','sha256':sha(L/'mathdb-352827.raw.jsonl')})
write('results.json',{'lane':'schrijver-manuscript-r1','mathdb_id':352827,'status':'DRAFT_FOR_ROOT_REVIEW','self_accepted':False,'accepted_credit':0,'root_decides':True,'paper':{'pdf':'paper.pdf','source':'paper.md','pages':7,'all_pages_rendered_and_visually_inspected':True},'endpoint':'Schrijver.mathdb_352827 : ¬ SchrijverUnitGap','source_packet':{'path':'schrijver-source-r5.zip','byte_identical_to_r5':True,'sha256':sha(L/'schrijver-source-r5.zip'),'modules':474},'checks':{'safe_extraction':True,'packet_manifest':True,'independent_ordinary_certificates':True,'frozen_inputs_unchanged':True,'visual_qa':True},'lean_tools_run_here':False,'root_replay':'pending','journal_body_read':False,'priority_claim':False,'gate_E_map':'gate-E-map.json','procedural_exceptions':'operations.json','running_jobs':False})
(L/'SUMMARY.md').write_text("""# MathDB 352827 - manuscript handback

DRAFT for root review; zero accepted credit; no self-acceptance. The seven-page paper is paper.pdf, editable source paper.md. It refutes the literal arXiv v2 unit-gap conjecture at k=12,r=3. The proof distinguishes Lean's sufficient bounds (8 below and 6 above) from independently checked exact diameters; includes the explicit distance-eight pair, rotation/BFS upper bound, k=13 corroboration, complete formal correspondence, search limits, correction-only Theorem 6 remark, audits, access qualifications and bibliography. gate-E-map.json maps all fidelity requirements to the paper.

The proof packet schrijver-source-r5.zip is byte-identical to r5, SHA-256 685b78855d145dae95ba175796528739f8a9ee5ea54fb621fc78b5ccdc763d1b, with 474 Lean modules. Safe extraction and source-manifest verification passed without running Lean, lake or leanchecker. Independent ordinary checks passed for all five certificate graphs. Every final PDF page was rendered and visually inspected; qa/receipt.json binds the inspected PDF and images.

Root replay is pending: schrijver-parent-final-r1/replay-result.json is absent at packaging. The parent registry-refresh receipt is copied with its path-screen limitations. The DAM journal body remains unread; no priority or worldwide novelty claim is made. Root alone decides acceptance. The source Theorem 6 correction receives no separate credit.

Both ZIPs, manifests, raw MathDB line, source copies, access receipts, PROOF.md, REPRODUCE.md, before/after hashes and resource/QA receipts are provided. All frozen input hashes are unchanged. Initial read-only access before complete caps/hash binding and a repaired script-authoring quoting failure are candidly recorded in operations.json. No child agents, external actions, git, shared edits or forbidden proof tools were used. No jobs remain running.
""")
# Include final evidence, not environment caches, redundant extraction or intermediate rasterizations.
excluded={'DOSSIER-MANIFEST.json','schrijver-full-dossier.zip','DELIVERY-SHA256.json','package-validation.json'}
paths=[]
for p in sorted(L.rglob('*')):
 if not p.is_file():continue
 rel=p.relative_to(L)
 if rel.parts[0] in {'tmp','proof-packet-safe'} or '__pycache__' in rel.parts:continue
 if str(rel) in excluded:continue
 if rel.parts[0]=='qa' and rel.name.startswith('page-'):continue
 paths.append(p)
manifest={str(p.relative_to(L)):{'sha256':sha(p),'bytes':p.stat().st_size} for p in paths}
write('DOSSIER-MANIFEST.json',manifest)
with zipfile.ZipFile(L/'schrijver-full-dossier.zip','w',zipfile.ZIP_DEFLATED,compresslevel=6) as z:
 for p in paths+[L/'DOSSIER-MANIFEST.json']:z.write(p,str(p.relative_to(L)))
with zipfile.ZipFile(L/'schrijver-full-dossier.zip') as z:
 assert z.testzip() is None
 assert set(z.namelist())==set(manifest)|{'DOSSIER-MANIFEST.json'}
 for n,d in manifest.items():assert hashlib.sha256(z.read(n)).hexdigest()==d['sha256']
write('package-validation.json',{'pass':True,'files_in_manifest':len(manifest),'zip_crc':True,'all_member_hashes_verified':True,'source_packet_inside_dossier_identical':True})
write('DELIVERY-SHA256.json',{n:sha(L/n) for n in ['paper.pdf','paper.md','schrijver-source-r5.zip','schrijver-full-dossier.zip','DOSSIER-MANIFEST.json','package-validation.json','inputs-before.json','inputs-after.json']})
print(json.dumps({'manifest_files':len(manifest),'dossier_bytes':(L/'schrijver-full-dossier.zip').stat().st_size,'frozen_inputs_unchanged':len(before),'root_replay':'pending'}))
