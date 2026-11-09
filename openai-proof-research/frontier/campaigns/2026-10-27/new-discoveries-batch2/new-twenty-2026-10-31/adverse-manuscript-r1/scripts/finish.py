from pathlib import Path
import json,hashlib,zipfile,datetime,os
R=Path(__file__).resolve().parents[1];P=R.parent
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,x):(R/p).write_text(json.dumps(x,indent=2)+'\n')
b=json.loads((R/'receipts/frozen-before.json').read_text());a={p:h(P/p) for p in b};assert a==b
write('receipts/frozen-after.json',a)
write('receipts/frozen-comparison.json',{'status':'PASS','files':len(a),'unchanged':True,'before_sha256':h(R/'receipts/frozen-before.json'),'after_sha256':h(R/'receipts/frozen-after.json')})
mods={}
for p in (P/'adverse-formal-r2/formal').glob('*.lean'):
 assert h(p)==h(R/'formal'/p.name);mods[p.name]=h(p)
assert h(R/'formal/Reviewer.lean')==h(P/'adverse-review-r1/extracted/formal/Reviewer.lean')
write('receipts/module-identity.json',{'status':'PASS','original_13_proof_modules_plus_unchanged_audit':mods,'reviewer_authored':{'Reviewer.lean':h(R/'formal/Reviewer.lean')},'new_audit_infrastructure_only':['DossierAudit.lean']})
# Record the positive proof-source screen separately from negative-control inputs.
import re
proofs=[p for p in (R/'formal').glob('*.lean') if p.stem not in ['Audit','DossierAudit']]
for p in proofs:assert not re.search(r'\b(sorry|admit|axiom|unsafe|partial|native_decide|ofReduceBool|implemented_by|extern)\b',p.read_text()),p
write('receipts/positive-source-screen.json',{'status':'PASS','proof_files':len(proofs),'scope':'13 original proof modules plus reviewer; generated negative controls are expected rejected inputs'})
raw=R/'inputs/raw/381433.jsonl' ;assert len(raw.read_bytes().splitlines())==1
write('receipts/mathdb-raw.json',{'mathdb_id':381433,'sha256':h(raw),'byte_length':raw.stat().st_size,'exact_copy':True,'origin':'expanded-corpus-r101/raw/381433.jsonl'})
report=json.loads((R/'fresh-replay/receipts/replay.json').read_text());assert report['strict_fresh_replay']=='pass'
calls=[json.loads(p.read_text()) for p in (R/'fresh-replay/receipts').glob('*.json') if p.name not in ['negative-controls.json','replay.json']]
assert all(c['termination'] is None and c['seconds']<140 and c['peak_sampled_total_rss_bytes']<=6*1024**3 for c in calls)
resources={'status':'PASS','bounded_calls':len(calls),'peak_sampled_total_rss_bytes':max(c['peak_sampled_total_rss_bytes'] for c in calls),'max_wall_seconds':max(c['seconds'] for c in calls),'all_termination_null':True,'at_most_cpus':2,'cpu_limit_seconds':120,'wall_limit_seconds':140,'MALLOC_ARENA_MAX':'2','sampling_seconds':0.1,'rss_limit_bytes':6*1024**3}
write('receipts/resource-summary.json',resources)
lean=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
write('receipts/pins.json',{'lean_version':'4.34.1','lean_commit':'5045d0056413266e57c625dcd7c365b10e377c52','lean_binary_sha256':h(lean),'mathlib_commit':'d13f23b723b8a846827a245b89c10fc7d3f11612','mathlib_identity_basis':'inherited independent-review dependencies.json (preserved); not a fresh git query or dependency rebuild'})
# Copy provenance map for evidence material and explicit historical receipt scope.
write('INPUT-COPY-MANIFEST.json',{str(p.relative_to(R)):h(p) for p in (R/'inputs').rglob('*') if p.is_file()})
write('receipts/final-replay-binding.json',{'status':'PASS','source_zip_sha256':h(R/'adverse-381433-manuscript-source.zip'),'source_manifest_sha256':h(R/'SOURCE-MANIFEST.json'),'extracted_source_manifest_sha256':h(R/'fresh-replay/SOURCE-MANIFEST.json'),'replay_receipt_sha256':h(R/'fresh-replay/receipts/replay.json'),'pdf_sha256':h(R/'paper/adverse-latin6-draft.pdf')})
# Exclude this verification process and its foreground tool ancestry.
ancestors=set();pid=os.getpid()
while pid>1 and pid not in ancestors:
 ancestors.add(pid)
 try:pid=int(next(l for l in Path(f'/proc/{pid}/status').read_text().splitlines() if l.startswith('PPid:')).split()[1])
 except (OSError,StopIteration):break
remaining=[]
for proc in Path('/proc').glob('[0-9]*'):
 try:
  if int(proc.name) in ancestors:continue
  cwd=(proc/'cwd').resolve()
  if cwd==R or R in cwd.parents:remaining.append(int(proc.name))
 except OSError:pass
assert not remaining,remaining
write('receipts/process-cleanup.json',{'status':'PASS','task_owned_processes_remaining':remaining,'foreground_verification_ancestry_excluded':True})
results={'mathdb_id' :381433,'status':'DRAFT_READY_FOR_ROOT_REVIEW','accepted_credit':0,'campaign_context':'15/20 beyond 39; root alone accepts','mathematics':{'graph':'cyclic Latin square graph of order 6','vertices':36,'degree':15,'alpha':5,'upsilon':6,'least_eigenvalue':-3,'adverse':True,'Q_graph':False,'noncomplete_variant_refuted':True},'strict_fresh_replay':'PASS','proof_modules':13,'reviewer_modules':1,'audited_declarations':167,'negative_controls':7,'axioms_allowed':['propext','Classical.choice','Quot.sound'],'byte_identity':'PASS','frozen_files':len(a),'frozen_inputs_unchanged':True,'pdf_pages':6,'all_pdf_pages_visually_inspected':True,'resources':resources,'limits':['Luz 2020 body unread; abstract-level description only','No priority claim','No new live prior-art or current registry content clearance','Inherited final-version and inaccessible-source gaps persist','Cached dependency libraries trusted; no dependency rebuild','RSS sampled, not instantaneous'],'source_zip':'adverse-381433-manuscript-source.zip','full_zip':'adverse-381433-manuscript-full-dossier.zip','background_jobs_remaining':False}
write('results.json',results)
(R/'SUMMARY.md').write_text(f'''# MathDB 381433: draft manuscript and Lean dossier

The six-page AI-assisted DRAFT proves that the cyclic Latin square graph of
order 6 is adverse and non-Q: alpha = 5, upsilon = 6 and least eigenvalue = -3,
with both latter invariants unchanged after every open-neighbourhood deletion.
It also covers the noncomplete variant. No priority claim is made. Accepted
credit is zero; root alone performs final replay, manuscript review and acceptance.
Campaign context remains 15/20 beyond the historical 39.

The 13 original proof modules and original Audit.lean are byte-identical to
adverse-formal-r2. Reviewer.lean is hash-identical and explicitly reviewer-authored.
The FINAL source-only ZIP was safely extracted afresh and fully replayed: strict
-j1 -DwarningAsError=true builds, leanchecker for all 14 proof modules plus audit,
a full 167-declaration audit, and seven expected negative controls all PASS.
Only propext, Classical.choice and Quot.sound are permitted transitive axioms.
See fresh-replay/receipts/replay.json and logs/full-audit.log.gz within that tree.
The earlier completed preliminary replay is superseded by the final-archive replay.

All {len(a)} frozen bindings remain unchanged. The exact raw MathDB line is in
inputs/raw/381433.jsonl with its own hash receipt. Every final PDF page was rendered
and visually inspected; six PNGs and receipts/pdf-qa.json are retained. Every Lean
call had a sampled total process-group RSS watchdog, two-CPU affinity, CPU 120 s,
wall 140 s and MALLOC_ARENA_MAX=2. Peak sampled RSS was
{resources['peak_sampled_total_rss_bytes']} bytes; longest call was
{resources['max_wall_seconds']:.2f} seconds. All limits passed.

Deliverables: paper/adverse-latin6-draft.pdf and paper/manuscript.py; PROOF.md;
STATEMENT-CORRESPONDENCE.md; REPRODUCE.md; results.json; both manuscript ZIPs;
MODULE-HASHES.json, SOURCE-MANIFEST.json, INPUT-COPY-MANIFEST.json,
DOSSIER-MANIFEST.json and archive-hashes.json; receipts/, qa/, frozen source copies,
historical review/access receipts and the fresh extracted replay sources and logs.
The full ZIP excludes compiled artifacts, temporary PDF dependencies and the superseded preliminary replay.
DOSSIER-MANIFEST covers payload files; archive hashes are a separate sidecar to avoid self-reference.

Luz 2020 remains explicitly unread. Its abstract-level description and same-issue
context do not clear subsumption. Other inherited access/final-version/current
registry gaps remain; no fresh literature search or novelty clearance is claimed.
The source bibliography identifies the versions and passages actually read.
Cached dependency oleans are trusted and RSS monitoring is sampled.

All writes stayed in this lane. No children, git, shared-ledger edits, browser,
publication, uploads, accounts or external messages were used. No task-owned
background jobs remain. Historical copied receipts retain their original claims
and private-RSS terminology; this lane's final replay uses total VmRSS.
''')
# Exclude temporary dependency installs, preliminary replay, compiled binaries, and archive recursion.
files=[]
for p in R.rglob('*'):
 if not p.is_file():continue
 rel=p.relative_to(R)
 if rel.parts[0] in ['tmp','preliminary-replay'] or p.name in ['DOSSIER-MANIFEST.json','archive-hashes.json','adverse-381433-manuscript-full-dossier.zip']:continue
 if any(s in p.name for s in ['.olean','.ilean']) or '__pycache__' in rel.parts:continue
 files.append(p)
write('DOSSIER-MANIFEST.json',{str(p.relative_to(R)):h(p) for p in sorted(files)})
files.append(R/'DOSSIER-MANIFEST.json')
z=R/'adverse-381433-manuscript-full-dossier.zip'
with zipfile.ZipFile(z,'w',zipfile.ZIP_DEFLATED) as f:
 for p in sorted(files):f.write(p,p.relative_to(R))
with zipfile.ZipFile(z) as f:
 assert f.testzip() is None
 for name,digest in json.loads((R/'DOSSIER-MANIFEST.json').read_text()).items():assert hashlib.sha256(f.read(name)).hexdigest()==digest
write('archive-hashes.json',{p.name:{'sha256':h(p),'bytes':p.stat().st_size} for p in [R/'adverse-381433-manuscript-source.zip',z]})
print(json.dumps(results,indent=2));print('Full dossier zip verified against manifest')
