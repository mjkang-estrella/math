from pathlib import Path
import json,hashlib,datetime
D=Path(__file__).parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
j=json.loads((D/'freeze-before.json').read_text());after={}
for label,s in j.items():
 originals=[];copies=[]
 for f in s['files']:
  p=f['path'];h=f['sha256'];assert sha(Path(s['source'])/p)==h,('original',label,p);assert sha(D/'inputs'/label/p)==h,('copy',label,p);originals.append(p);copies.append(p)
 after[label]={'count':len(originals),'originals_unchanged':True,'copies_match':True,'manifest_sha256':s['manifest_sha256']}
(D/'freeze-after.json').write_text(json.dumps(after,indent=2))
assert sha(D/'helper_guard.py')=='825ee0d48177cd12354cdbf36fd36b61f0503ff3241356a7bf638ee0bc49fa45'
reg={}
for name in ['omega','openai']:
 h=json.loads((D/'live'/f'{name}-head.json').read_text());reg[name]={'sha':h['sha'],'commit_date':h['commit']['committer']['date'],'response_sha256':sha(D/'live'/f'{name}-head.json')}
delta=json.loads((D/'live/omega-delta.json').read_text());reg['omega_delta']={'base':'9aef67a59dec08d1ff04a18a3d23560525ab023d','ahead':delta['ahead_by'],'behind':delta['behind_by'],'total_commits':delta['total_commits'],'net_files':len(delta['files']),'paths':[x['filename'] for x in delta['files']],'limitation':'net comparison and selected actual bodies; not exhaustive merge-history or baseline semantic census'}
(D/'CURRENT-REGISTRIES.json').write_text(json.dumps(reg,indent=2))
prov={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'role':'solo targeted review r2','candidate':'sol-fresh-source-discovery-r97','frozen_candidate':59,'frozen_preliminary':98,'math':'PASS retained, full proof read','accepted_manuscript_scope':'PASS retained','published_version':'HOLD: two actual author accepted bodies, date-only extracted-text difference; no VoR','substantive':'FAIL: explicit old-body compatible-triple bridge from Ruankong et al Theorem5.4 proof plus Fuchs-Wang Example2.5; complete common-law smoothing bridge','bounded_novelty':'Positive earlier mathematical subsumption found; exact prior printed Chatterjee endpoint and worldwide priority not asserted','recommendation':'EXCLUDE discovery credit; no Lean/paper','credit':0,'counts':{'additional':8,'total':38},'guard_sha256':sha(D/'helper_guard.py'),'guard_limits':{'AS_MiB':512,'groupRSS_MiB':512,'CPU_seconds':210,'wall_seconds':230,'nominal_sample_ms':40,'BLAS_threads':1},'originals_unchanged':True,'review_sha256':sha(D/'review.md'),'source_evidence':'http-receipts.json and passage-receipts.json','resolved':['coauthor accepted manuscript comparison','earlier compatible triple','common-law checkerboard/positive-distance smoothing','dated public heads and selected actual delta bodies'],'remaining':['CGK actual final published body','exhaustive baseline and bibliography semantic coverage'],'no_worldwide_priority_claim':True}
(D/'provenance.json').write_text(json.dumps(prov,indent=2))
# Hash all artifacts except the manifest itself and final log (the guard writes that after this helper exits).
files={str(p.relative_to(D)):sha(p) for p in sorted(D.rglob('*')) if p.is_file() and p.name not in ['evidence-manifest.json','finalize.log']}
(D/'evidence-manifest.json').write_text(json.dumps({'files':files,'excluded':['evidence-manifest.json','finalize.log']},indent=2))
print(json.dumps({'freeze':after,'evidence_files_hashed':len(files),'review_sha256':sha(D/'review.md'),'verdict':'EXCLUDE substantive routine-corollary; VoR HOLD; credit0'},indent=2))
