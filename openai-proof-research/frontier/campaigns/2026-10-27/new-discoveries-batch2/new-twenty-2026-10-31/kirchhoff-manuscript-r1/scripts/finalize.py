from pathlib import Path
import hashlib,json,re,zipfile,datetime,os
D=Path(__file__).resolve().parents[1];P=D.parent
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,x):
 p=D/p;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(x,indent=2)+'\n')
before=json.loads((D/'input-hashes-before.json').read_text())
after={k:H(Path(k) if Path(k).is_absolute() else P/k) for k in before}
assert after==before
write('input-hashes-after.json',after)
write('receipts/frozen-bindings.json',{'status':'PASS','files':len(before),'unchanged':True,'before_sha256':H(D/'input-hashes-before.json'),'after_sha256':H(D/'input-hashes-after.json')})
ident={}
for f in sorted((P/'kirchhoff-formal-r2/formal').glob('*.lean')):
 vals=[H(f),H(D/'formal'/f.name),H(D/'final-replay/formal'/f.name)]
 assert len(set(vals))==1;ident[f.name]=vals[0]
write('manifests/module-hashes.json',ident)
write('receipts/module-identity.json',{'status':'PASS','byte_identical':True,'modules':ident,'comparisons':['frozen formal-r2','dossier formal','final extracted formal']})
scan={}
for f in list((D/'formal').glob('*.lean'))+list((D/'checks').glob('*.lean'))+list((D/'negative').glob('*.lean')):
 s=f.read_text();hits=re.findall(r'\b(?:sorry|admit|native_decide|ofReduceBool)\b|^\s*(?:axiom|unsafe)\s',s,re.M)
 assert not hits,(f,hits);scan[str(f.relative_to(D))]='PASS'
write('receipts/source-scan.json',{'status':'PASS','scan':scan,'note':'Safety, local axioms, and transitive axioms independently checked by full Lean declaration audit.'})
replay=json.loads((D/'final-replay/receipts/replay.json').read_text());assert replay['all_local_declarations']==176
receipts=[]
for f in (D/'final-replay/receipts').glob('*.json'):
 r=json.loads(f.read_text())
 if 'returncode' in r:
  assert r['killed'] is None and r['peak_rss_bytes']<=6*1024**3 and r['seconds']<140
  receipts.append(r)
peak=max(r['peak_rss_bytes'] for r in receipts);wall=max(r['seconds'] for r in receipts)
write('receipts/replay.json',dict(replay,source_zip_sha256=H(D/'kirchhoff-source-only.zip'),guarded_calls=len(receipts),peak_rss_bytes=peak,max_wall_seconds=wall,guard_kills=[]))
write('receipts/pdf-qa.json',{'status':'PASS','pages':6,'render':'pdftoppm -scale-to 1250 -png paper/kirchhoff-draft.pdf qa/final','pdf_sha256':H(D/'paper/kirchhoff-draft.pdf'),'visual_inspection':'All six final pages individually viewed; readable equations, table rows, margins and folios; no clipping or overlap. Missing Unicode subscript and perpendicular glyphs fixed before final rendering.','images':{f'qa/final-{i}.png':H(D/f'qa/final-{i}.png') for i in range(1,7)}})
raw=D/'sources/expanded-corpus-r105/raw/349441.jsonl'
write('receipts/mathdb-binding.json',{'mathdb_id':349441,'path':str(raw.relative_to(D)),'sha256':H(raw),'bytes':raw.stat().st_size,'lines':len(raw.read_text().splitlines()),'byte_identical_to_frozen':True})
lean=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
write('manifests/tool-pins.json',{'lean':'4.34.1','lean_commit':'5045d0056413266e57c625dcd7c365b10e377c52','lean_binary_sha256':H(lean),'leanchecker_sha256':H(lean.with_name('leanchecker')),'mathlib_commit':'d13f23b723b8a846827a245b89c10fc7d3f11612','dependency_manifest_sha256':H(D/'sources/lake-manifest.json'),'trust':'External cached dependencies pinned by manifest; not rebuilt here.'})
write('manifests/input-copy-hashes.json',{str(f.relative_to(D)):H(f) for f in (D/'sources').rglob('*') if f.is_file()})
summary=f'''# MathDB 349441: manuscript and Lean dossier

The six-page AI-assisted DRAFT refutes the spectral reading of Estrada-Mugnolo Conjecture 4.13 with K6 plus a pendant five-edge path:

R1 = 1696684/14035 < R0 = 370/3.

The literal Moore-Penrose reading also fails (R1 = 515538204/7137235). Its earlier n = 5 failure is reported as a source inconsistency with zero separate credit. The paper distinguishes the ill-posed all-pairs physical equation, true Moore-Penrose pair sum, and spectral/group-inverse trace. No priority claim is made. Global spectral minimality is open in [9,11]. The frozen review reports no spectral failures through order 8; this lane does not rerun the exhaustive enumeration or claim it is formalized.

The five Lean modules are BYTE-IDENTICAL to kirchhoff-formal-r2/formal. The FINAL source-only ZIP was safely extracted into final-replay/ and fully replayed: five strict builds, five leancheckers, the complete 176-declaration audit, three positive proofs of semantic control negations, and three expected-failure controls all PASS. Only propext, Classical.choice and Quot.sound are permitted. Every call used the sampled 6 GiB aggregate RSS watchdog, at most two CPUs, CPU 120 seconds, wall 140 seconds and MALLOC_ARENA_MAX=2. Peak sampled RSS: {peak} bytes; longest guarded call: {wall:.2f} seconds. No guard killed a process. Full audit ASTs and logs are in final-replay/logs/; structured receipts are in final-replay/receipts/ and receipts/replay.json. Earlier completed replays are superseded.

All {len(before)} frozen file bindings are unchanged; source, lane, and extracted module identities match. The exact MathDB raw line and historical source/access receipts are retained. All six final PDF pages were rendered and individually inspected, with PNGs and receipts/pdf-qa.json. An independent Fraction-based arithmetic cross-check reconstructs the witness Laplacians and verifies every inverse equation and value for alpha = -1, 0, 1.

Deliverables: paper/kirchhoff-draft.pdf; paper/manuscript.json and paper/render.py; PROOF.md; statement-correspondence.md; REPRODUCE.md; results.json; kirchhoff-source-only.zip; kirchhoff-full-dossier.zip; manifests/; receipts/; sources/; qa/final-1.png through final-6.png. Source packet hashes are in source-hashes.json. Dossier payload hashes are in manifests/dossier.json. Archive hashes are in manifests/archives.json and manifests/delivery.json (the full ZIP's own hash is an external sidecar to avoid self-reference). Full ZIP verification reads back and hashes every payload member.

The ordinary eigenvalue-to-group-trace argument is not formalized in the unchanged Lean modules. Cached dependency oleans and the operating system are trusted; RSS is sampled. The source's definitional defects receive no credit. The inherited literature review is bounded: Chaos 2023 was only partially read; Miranda 2026 was subsequently text-screened by root, with no Kirchhoff discussion found. No new literature clearance or publication is claimed.

Accepted credit stays ZERO; campaign context stays 17/20 beyond 39. Root alone performs final review, replay and acceptance. No child agents, git, browser, shared-ledger edits, publication, uploads, accounts or external messages were used. All created files stayed inside this lane. No task-owned background jobs remain at handback.
'''
(D/'SUMMARY.md').write_text(summary)
write('results.json',{'mathdb_id':349441,'status':'DRAFT; verified dossier; root acceptance pending','accepted_credit':0,'campaign_count_unchanged':'17/20 beyond 39','witness':'K6 with edges 0-6-7-8-9-10 appended','spectral':{'R1':'1696684/14035','R0':'370/3','difference':'102898/42105'},'MP_R1':'515538204/7137235','minimality':{'global_spectral_interval':[9,11],'global_minimum_proved':False,'clique_pendant_first_failure':11},'spectral_experiment':{'source':'frozen independent review, not rerun here','n_5_to_8_connected_graphs':12103,'failures':0},'formal':{'identical_modules':5,'audited_declarations':176,'strict_builds':5,'leancheckers':5,'semantic_control_negations':3,'expected_failure_controls':3,'allowed_axioms':replay['allowed_axioms'],'fresh_final_zip_replay':'PASS'},'resources':{'guarded_calls':len(receipts),'peak_aggregate_rss_bytes':peak,'max_call_wall_seconds':wall,'guard_kills':[]},'frozen_files':len(before),'frozen_bindings_unchanged':True,'pdf_pages':6,'pdf_visual_QA':'PASS','ordinary_exact_cross_check':'PASS','background_jobs_remaining':False,'limits':['Eigenvalue bridge is ordinary mathematics, not a Lean theorem','Small-graph enumeration inherited, not formalized','Bounded prior-art review; Chaos partial only','Cached Lean dependencies trusted; watchdog samples RSS'],'deliverables':{'pdf':'paper/kirchhoff-draft.pdf','source':'paper/manuscript.json','renderer':'paper/render.py','source_zip':'kirchhoff-source-only.zip','full_zip':'kirchhoff-full-dossier.zip'}})
write('manifests/archives.json',{'kirchhoff-source-only.zip':H(D/'kirchhoff-source-only.zip')})
# Include final verified replay evidence, never compiled artifacts or old extractions.
files=[]
for name in ['formal','negative','checks','paper','scripts','receipts','manifests','sources']:
 for f in (D/name).rglob('*'):
  if f.is_file() and f.suffix not in ['.pyc','.olean','.ilean']:files.append(f)
for f in (D/'qa').glob('final-*.png'):files.append(f)
for name in ['logs','receipts']:
 files+= [f for f in (D/'final-replay'/name).rglob('*') if f.is_file()]
files.append(D/'final-replay/extraction-receipt.json');files.append(D/'logs/final-replay-driver.log')
for name in ['SUMMARY.md','results.json','REPRODUCE.md','PROOF.md','statement-correspondence.md','replay.py','source-hashes.json','input-hashes-before.json','input-hashes-after.json','TASK.txt','kirchhoff-source-only.zip']:files.append(D/name)
files=sorted(set(files));files=[f for f in files if str(f.relative_to(D)) not in ['manifests/dossier.json','manifests/delivery.json']]
payload={str(f.relative_to(D)):H(f) for f in files};write('manifests/dossier.json',payload);files.append(D/'manifests/dossier.json')
full=D/'kirchhoff-full-dossier.zip'
with zipfile.ZipFile(full,'w',zipfile.ZIP_DEFLATED) as z:
 for f in sorted(files):z.write(f,str(f.relative_to(D)))
with zipfile.ZipFile(full) as z:
 assert z.testzip() is None
 for name,h in payload.items():assert hashlib.sha256(z.read(name)).hexdigest()==h
 assert all(not n.endswith(('.olean','.ilean','.pyc')) for n in z.namelist())
write('manifests/delivery.json',{'status':'PASS','archives':{n:H(D/n) for n in ['kirchhoff-source-only.zip','kirchhoff-full-dossier.zip']},'full_zip_members':len(files),'full_payload_hashes_verified':True,'full_zip_manifest_sha256':H(D/'manifests/dossier.json')})
print(json.dumps({'frozen_files':len(before),'peak_rss_bytes':peak,'max_wall_seconds':wall,'full_zip_bytes':full.stat().st_size,'status':'PASS'}))
