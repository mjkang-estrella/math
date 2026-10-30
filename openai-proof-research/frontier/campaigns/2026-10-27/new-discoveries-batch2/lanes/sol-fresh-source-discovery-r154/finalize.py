import sys,json,hashlib,datetime
from pathlib import Path
L=Path(__file__).resolve().parent;R=L.parents[5]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
mode=sys.argv[1]
if mode=='freeze':
 d=json.loads((L/'history-delta.json').read_bytes());base=R/d['base'];assert sha(base)==d['base_sha256']
 refs=[base,L.parent/'sol-fresh-source-discovery-r151/provenance.json',L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']
 for x in json.loads((L/'registry-paths.json').read_bytes()):refs.append(R/x['path'])
 for x in json.loads((L/'registry-scoped.json').read_bytes()):refs.append(R/x['path'])
 refs.extend([R/'AGENTS.md',L.parents[1]/'AGENTS.md'])
 http=[json.loads(x) for x in (L/'http.jsonl').read_text().splitlines()]
 for x in http:
  if 'sha256' in x:assert sha(L/'sources'/x['name'])==x['sha256']
 first=json.loads((L/'sources/firstproof-head.json').read_bytes())
 save('provenance.json',dict(created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='UNRESOLVED; zero qualifying outcomes',selected_source=dict(authors=['Aleksa Milojević','Benny Sudakov'],title='On the Probability a Weighted Bernoulli Sum Exceeds Its Mean',id='2606.30287v1',claim='Conjecture 1',source_date_utc='2026-06-29T13:28:12Z',scope='all finite positive probability vectors; all real p in [0,1/3]'),http=http,context=[dict(path='context-'+n,sha256=sha(L/('context-'+n))) for n in ['ledger.json','prior-campaign-context.json','NEXT.md']],external_reuse=[dict(path=str(p.relative_to(R)),sha256=sha(p)) for p in refs],omega_fixed='490f6bccbf445ab8e111a16b0b8670a5dd7c9a9c',openai_fixed='7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a',registry_gaps=['aa026-to-a19a capped300','a19a-to-490f capped300','scoped paths and baseline do not clear all changed mathematical bodies','no worldwide priority or exhaustive semantic claim'],firstproof=dict(commit=first['sha'],committer_date=first['commit']['committer']['date'],tree_truncated=json.loads((L/'sources/firstproof-tree.json').read_bytes())['truncated'],proof_scope='Read actual public partial p=2/k/reciprocal/coloring/closure/coalescence/cyclic bodies; full p<=1/3 gap retained'),web_read_only_leads=['https://arxiv.org/abs/2606.30287','https://math.stackexchange.com/questions/265163/convex-combinations-of-low-probability-bernoulli-variables','https://alea.impa.br/articles/v20/20-07.pdf','https://1stproof.org/assets/docs/report.pdf'],web_limits='Bounded title/author/claim searches on 2026-10-30 UTC; no exhaustive citing database sweep; MSE tool text has no archived primary bytes',runtime=dict(guard=str(refs[2].relative_to(R)),guard_sha256=sha(refs[2]),address_space_bytes=512*1024*1024,sampled_group_rss_bytes=512*1024*1024,cpu_seconds=210,wall_seconds=230,nominal_sample_ms=40,thread_env=['OPENBLAS_NUM_THREADS=1','OMP_NUM_THREADS=1','PYTHONDONTWRITEBYTECODE=1'],sampling_qualification='subinterval RSS spikes may be missed'),no_proof=True,no_lean=True,no_paper=True,external_actions=False))
 exclude={'context-NEXT.md','scientific-freeze.json','finalmanifest.json','manifest-verification.json','finalize.log'}
 science=[dict(path=str(p.relative_to(L)),sha256=sha(p),bytes=p.stat().st_size) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in exclude]
 save('scientific-freeze.json',dict(entries=science,excludes=['mutable context-NEXT.md','manifest/verification/self and finalizer runtime log'],universal_proof=False))
 manifest=[dict(path=str(p.relative_to(L)),sha256=sha(p),bytes=p.stat().st_size) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in {'context-NEXT.md','finalmanifest.json','manifest-verification.json','finalize.log'}]
 save('finalmanifest.json',dict(entries=manifest,excluded_mutable=['context-NEXT.md','manifest-verification.json','finalize.log','finalmanifest.json']))
elif mode=='verify':
 for name in ['finalmanifest.json','scientific-freeze.json']:
  j=json.loads((L/name).read_bytes())
  for r in j['entries']:
   p=L/r['path'];assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],r
 p=json.loads((L/'provenance.json').read_bytes())
 for r in p['external_reuse']:assert sha(R/r['path'])==r['sha256'],r
 assert not (L/'PROOF.md').exists()
 save('manifest-verification.json',dict(status='PASS',verified_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=sha(L/'finalmanifest.json'),scientific_freeze_sha256=sha(L/'scientific-freeze.json'),manifest_entries=len(json.loads((L/'finalmanifest.json').read_bytes())['entries']),scientific_entries=len(json.loads((L/'scientific-freeze.json').read_bytes())['entries']),external_references='PASS',mutable_NEXT_excluded=True))
 print((L/'manifest-verification.json').read_text())
