import sys,json,hashlib,datetime
from pathlib import Path
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2,ensure_ascii=False)+'\n')
def entry(p):return dict(path=str(p.relative_to(L)),bytes=p.stat().st_size,sha256=sha(p))
if sys.argv[1]=='create':
 guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
 http=[json.loads(s) for s in (L/'http.jsonl').read_text().splitlines()]
 history=json.loads((L/'history-receipt.json').read_text())
 retained=[]
 for r,names in [('133',['history-receipt.json','retained-r111-r113-science.json']),('137',['history-receipt.json']),('140',['history-expanded.json','registry-delta-receipt.json','registry-relevant-tree-delta.json'])]:
  for name in names:
   p=L.parent/('sol-fresh-source-discovery-r'+r)/name
   retained.append(dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size))
 save('provenance.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),decision='zero nominees',counts_inherited=dict(additional=9,total=39,next=40),http=http,retained=retained,guard=dict(path=str(guard),sha256=sha(guard),AS_bytes=512*1024**2,groupRSS_bytes=512*1024**2,CPU_seconds=210,wall_seconds=230,nominal_sample_ms=40,limit='Sampled RSS; unobserved transients not excluded'),history=dict(bodies=len(history['aliases']),paths=sum(map(len,history['aliases'].values())),reopened=len(history['reopened']),selected_hits=history['hits']['selected'],original_r111_r113=[p for ps in history['aliases'].values() for p in ps if any('/sol-fresh-source-discovery-r'+str(i)+'/' in p for i in [111,112,113])]),registry=dict(omega_fixed='a19a578cd06b57a4ea4d287cb0df92f9085117ae',openai_fixed='7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a',new_HEAD_queries=0,prior_compare_files_capped=300,prior_direct_tree_scope='Blueprint/Library/Problems Markdown and README only',new_tree_scope=['Library','Problems','docs'],semantic_clearance=False),access_limits=['No world-priority certification','No exhaustive author or citation corpus','No full registry-body coverage','No source visual PDF audit','No source-code or binary history scan'],search_queries=['probability conjecture 2025 log-concavity counterexample','conjecture 2026 complete monotonicity','2610.37066 proof solution extension','Improved Brunn Minkowski convolution bodies','Javier Martin Goni publications 2026 convolution'],search_limit='Web search result bodies not exported as primary evidence; search absence is not novelty clearance.',public_mutations=False))
 files=[p for p in L.rglob('*') if p.is_file() and p.name not in {'scientific-freeze.json','finalmanifest.json','manifest-verification.json'}]
 scientific=[entry(p) for p in sorted(files) if not p.name.startswith('context-') and p.name!='context-reading.json' and p.name!='history-receipt.json' and 'reopened' not in p.parts]
 save('scientific-freeze.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),entries=scientific,exclusions='Mutable context snapshots, whole-history receipt and copied originals are bound by finalmanifest separately; source science and diagnostics frozen here.'))
 files.append(L/'scientific-freeze.json')
 save('finalmanifest.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),entries=[entry(p) for p in sorted(files)],excludes=['finalmanifest.json','manifest-verification.json'],self_reference='External receipt binds manifest hash.'))
 print('manifest entries',len(files),'scientific entries',len(scientific))
elif sys.argv[1]=='verify':
 j=json.loads((L/'finalmanifest.json').read_text());fail=[]
 for x in j['entries']:
  p=L/x['path']
  if not p.is_file() or sha(p)!=x['sha256'] or p.stat().st_size!=x['bytes']:fail.append(x['path'])
 bound={x['path'] for x in j['entries']}|set(j['excludes'])
 extra=[str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and str(p.relative_to(L)) not in bound]
 for h in [json.loads(s) for s in (L/'http.jsonl').read_text().splitlines()]:
  if 'sha256' in h:assert sha(L/'sources'/h['name'])==h['sha256']
 r=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS' if not fail and not extra else 'FAIL',manifest_sha256=sha(L/'finalmanifest.json'),entries=len(j['entries']),failures=fail,unbound_files=extra)
 save('manifest-verification.json',r);print(json.dumps(r));assert r['status']=='PASS'
