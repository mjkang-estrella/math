from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
b=json.loads((L/'source-bindings.json').read_text())['bindings']
for x in b:
 if x['kind']=='administrative snapshot':assert h(Path(x['copy']))==x['sha256']
 else:assert h(Path(x['path']))==x['sha256'],x['path']
cache=json.loads((L/'cached-body-screen.json').read_text())
for x in cache:assert h(Path(x['path']))==x['sha256']
primary=[]
for name in ['2610.19965v1','2606.18234v5','2306.09033v2']:
 for ext in ['pdf','txt']:
  p=L.parent/'sol-wide-discrete-algebraic-certificates-r277/sources'/(name+'.'+ext)
  primary.append({'path':str(p),'sha256':h(p),'url':'https://arxiv.org/pdf/'+name})
provenance={'status':'HOLD; no endpoint or novelty certification','at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'counts':{'additional':9,'total':39,'next':40,'authority':'root only'},'primary':primary,'source_freeze':'source-bindings.json','cache_screen':'cached-body-screen.json','cached_tex_bodies':len(cache),'current_registry_head':'UNKNOWN; denied routes not retried','registry_pinned_commit':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','live_primary_access':'access.jsonl','historical_intervals':'parked; no exhaustive priority claim','guard':{'path':str(L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'),'AS_bytes':512*1024**2,'group_RSS_bytes':512*1024**2,'CPU_seconds':210,'wall_seconds':230,'environment':{'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1','PYTHONDONTWRITEBYTECODE':'1'}},'preserved_failures':'failures.md','external_mutations':False,'children':False,'scientific_sources_unchanged_after':True}
(L/'provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
manifest={str(p.relative_to(L)):{'sha256':h(p),'bytes':p.stat().st_size} for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['MANIFEST.json','verification-receipt.json']}
(L/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('Manifest written:',len(manifest),'files; sources and cached bodies unchanged.')
