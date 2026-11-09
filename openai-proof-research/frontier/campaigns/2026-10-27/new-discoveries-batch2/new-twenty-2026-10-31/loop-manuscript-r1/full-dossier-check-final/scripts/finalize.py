"""Finalize the local draft only after the authoritative extracted replay passes."""
from pathlib import Path
import json,hashlib,zipfile,datetime
D=Path(__file__).resolve().parents[1];P=D.parent
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def put(n,x): (D/n).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
r=json.loads((D/'fresh-replay/replay-receipts/replay.json').read_text());assert r['status']=='PASS'
# Reconcile every frozen input, including all files of both frozen directories.
roots=[P/'expanded-corpus-r76',P/'loop-review-r1',P/'loop-root-adjudication-r1.json',P/'loop-parent-r1/registry-refresh.json']
after={str(p.relative_to(P)):h(p) for root in roots for p in (sorted(root.rglob('*')) if root.is_dir() else [root]) if p.is_file()}
before=json.loads((D/'frozen-before.json').read_text());assert before==after
put('frozen-after.json',after)
put('receipts/frozen-integrity.json',{'status':'PASS','unchanged':True,'files':len(after),'before_sha256':h(D/'frozen-before.json'),'after_sha256':h(D/'frozen-after.json')})
assert (D/'formal/Loop.lean').read_bytes()==(P/'expanded-corpus-r76/formal/Loop.lean').read_bytes()
qa=json.loads((D/'qa/receipt.json').read_text());assert qa['status']=='PASS' and qa['pdf_sha256']==h(D/'paper.pdf')
with zipfile.ZipFile(D/'source-only.zip') as z:
 assert not any(n.endswith('.olean') for n in z.namelist())
 for n,digest in json.loads(z.read('source-manifest.json')).items():
  assert hashlib.sha256(z.read(n)).hexdigest()==digest
  assert h(D/n)==digest
  assert h(D/'fresh-replay'/n)==digest
assert not list((D/'fresh-replay').rglob('*.olean'))
log=(D/'fresh-replay/replay-receipts/build-AllAudit.log').read_text()
put('declaration-audit.json',{'status':'PASS','author_module':'Loop','author_declarations':28,'reviewer_module':'ReviewAudit','reviewer_declarations':2,'all_declarations_audited':30,'unsafe':False,'added_axioms':False,'allowed_transitive_axioms':['propext','Classical.choice','Quot.sound'],'log':'fresh-replay/replay-receipts/build-AllAudit.log','log_sha256':h(D/'fresh-replay/replay-receipts/build-AllAudit.log')})
runs=r['runs']
result={'status':'DRAFT','verification':'PASS','mathdb_id':380362,'accepted_credit':0,'acceptance_authority':'root alone','campaign_count':'9/20 beyond 39 unchanged','claim':'Counterexample to Conjecture 11.2 in the accessible manuscript: Moufang loops on a common set of order 16, distance 64 < 96, inequivalent associators','paper_pages':6,'paper':'paper.pdf','source':'paper-source.md','ordinary_proof':'PROOF.md','source_archive':'source-only.zip','full_archive':'full-dossier.zip','source_archive_sha256':h(D/'source-only.zip'),'literal_Loop_sha256':h(D/'formal/Loop.lean'),'literal_module_unchanged':True,'frozen_input_files':len(after),'frozen_inputs_unchanged':True,'strict_j1_warningAsError':True,'leanchecker':'PASS (Loop, ReviewAudit, AllAudit)','full_declaration_audit':30,'negative_controls_rejected':5,'fresh_replay':'fresh-replay/replay-receipts/replay.json','pdf_qa':'qa/receipt.json','systemd_MemoryMax_6G_all_calls':all(t['MemoryMax_6G'] for t in runs),'max_call_wall_seconds':max(t['wall_seconds'] for t in runs),'max_sampled_private_RSS_bytes':max(t['private_RSS_peak'] for t in runs),'max_sampled_total_VmRSS_bytes':max(t['total_VmRSS_peak'] for t in runs),'all_caps_untriggered':all(t['cap_reason'] is None for t in runs),'limitations':['The loop and code-loop construction are classical; no priority claim.','Associator equivalence is not explicitly defined generally in the source; image cardinality defeats all bijective readings described in the paper.','Typeset journal text not compared; arXiv posting postdates the journal.','Bounded literature/registry evidence; no new live search claimed.','Cached upstream oleans trusted; not a full dependency rebuild.','Private RSS sampled, not instantaneous peak measurement.'],'no_running_replay_jobs':True}
put('results.json',result)
(D/'SUMMARY.md').write_text('''# MathDB 380362 — DRAFT, zero accepted credit

Delivered a six-page AI-assisted manuscript with exact definitions, source context, explicit division, a hand-checkable polarization proof of the source Moufang identity, determinant associator, image-cardinality inequivalence and exact distance 64 < 96. The code loop is classical. No priority claim is made.

The final source-only ZIP was safely extracted into fresh-replay/. Strict Lean 4.34.1 builds (-j1 -DwarningAsError=true), leanchecker on all three built modules, the complete 30-declaration audit (28 literal author plus 2 reviewer), and five negative controls PASS. Only propext, Classical.choice and Quot.sound occur. Loop.lean is byte-identical to the frozen author source. Each call used the requested caps; systemd MemoryMax=6G was available. No replay jobs remain. Receipts and pins are included.

Every final PDF page was rendered and visually inspected; QA PASS. The first rendering's heading formatting was corrected. A preliminary replay passed the positive proof and kernel checks but exposed a case-sensitive error-message harness assertion; the final fresh archive replay fixes that harness check and passes. The original failure receipts are preserved and do not represent a mathematical proof failure.

All 402 frozen input files were hash-bound before and after, unchanged. Source-only and full-dossier ZIPs, manifests, archive hashes, PROOF.md, REPRODUCE.md, source copies, retrieval receipts, raw MathDB record and hash, independent diagnostic, reviewer supplement and root adjudication are supplied. Source manifest and full dossier manifest exclude themselves; ZIP digests are external.

Limitations: the accessible source does not define general associator equivalence explicitly; constancy versus nonconstancy removes the ambiguity for this witness. The typeset journal version was not compared, the January 2007 arXiv posting postdates the 2006 journal, literature clearance is bounded, and cached dependency oleans are trusted. The historical review HOLD and root's later qualified adjudication are both preserved. This lane performs no acceptance.

Campaign remains 9/20 beyond the unchanged 39. Accepted credit for this lane: zero. Root alone accepts.
''')
# Only deliverable files and receipts; omit duplicate preliminary source extractions and Python caches.
files=[]
for p in sorted(D.rglob('*')):
 if not p.is_file():continue
 n=str(p.relative_to(D))
 if n in ['full-dossier.zip','dossier-manifest.json','archive-hashes.json','full-dossier-verification.json']:continue
 if '__pycache__' in p.parts or n.startswith(('fresh-extraction/','full-dossier-check/','full-dossier-check-final/')):continue
 if n in ['receipts/finalize.log','receipts/finalize.json']:continue
 if n.startswith('preliminary-replay/') and '/replay-receipts/' not in n:continue
 if n=='scripts/make_replay.py':continue
 files.append(p)
manifest={str(p.relative_to(D)):h(p) for p in files}
put('dossier-manifest.json',manifest)
with zipfile.ZipFile(D/'full-dossier.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in files+[D/'dossier-manifest.json']:z.write(p,str(p.relative_to(D)))
with zipfile.ZipFile(D/'full-dossier.zip') as z:
 assert z.testzip() is None
 m=json.loads(z.read('dossier-manifest.json'))
 for n,digest in m.items():assert hashlib.sha256(z.read(n)).hexdigest()==digest
 assert not any(n.endswith('.olean') for n in z.namelist())
put('full-dossier-verification.json',{'status':'PASS','members':len(m)+1,'all_internal_hashes_match':True,'no_oleans':True,'source_archive_sha256':h(D/'source-only.zip'),'full_archive_sha256':h(D/'full-dossier.zip')})
put('archive-hashes.json',{n:h(D/n) for n in ['source-only.zip','full-dossier.zip']})
print('FINAL PASS',len(m)+1,'full-dossier members')
