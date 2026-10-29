from pathlib import Path
import json,hashlib,datetime
out=Path(__file__).parent;h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
fr=json.loads((out/'input-freeze.json').read_text());rows=[]
for r in fr['files']:
 p=Path(r['source']);q=Path(r['copy']);cur=h(p) if p.exists() else None
 rows.append({'source':str(p),'frozen_sha256':h(q),'current_sha256':cur,'unchanged':cur==r['sha256_before'],'freeze_equal':r['sha256_before']==r['sha256_copy']==r['sha256_after']})
(out/'input-after.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':rows},indent=2))
arts=[{'path':str(p.relative_to(out)),'sha256':h(p),'bytes':p.stat().st_size} for p in sorted(out.rglob('*')) if p.is_file() and p.name not in ['provenance.json','finalize.log']]
(out/'provenance.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'recommendation':'EXCLUDE (substance); priority HOLD','freeze_all_equal':all(r['freeze_equal'] for r in rows),'all_originals_unchanged':all(r['unchanged'] for r in rows),'resource_caps':{'AS_MiB':512,'group_RSS_MiB':512,'CPU_seconds':210,'wall_seconds':230,'BLAS_threads':1},'artifacts':arts},indent=2))
print(json.dumps({'files':len(arts),'freeze_equal':all(r['freeze_equal'] for r in rows),'changed_originals':[r['source'] for r in rows if not r['unchanged']]}))
