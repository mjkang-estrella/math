import json,hashlib,datetime
from pathlib import Path
L=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2,ensure_ascii=False)+'\n')
def item(p):
 b=p.read_bytes();return dict(path=str(p.relative_to(L)),bytes=len(b),sha256=sha(b))
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
p=L/'history-receipt.json';j=json.loads(p.read_bytes())
if 'records' in j:
 originals=[dict(path=f,sha256=h,bytes=z) for f,h,z in j['records'] if any('/sol-fresh-source-discovery-r'+str(i)+'/' in f for i in [111,112,113])]
 refs=[]
 for rel in ['sol-fresh-source-discovery-r157/history-receipt.json','sol-fresh-source-discovery-r158/history-delta.json','sol-fresh-source-discovery-r159/history-receipt.json','sol-fresh-source-discovery-r161/history-delta.json']:
  q=L.parent/rel;refs.append(dict(path=str(q),sha256=sha(q.read_bytes()),bytes=q.stat().st_size))
 save('history-receipt.json',dict(utc=now,full_body_count=j['full_body_count'],pattern=j['pattern'],hits=j['hits'],temporary_full_index_sha256=sha(p.read_bytes()),qualified_index_references=refs,original_r111_r113=originals,changed_originals='history-delta.json',qualification=j['qualification'],cleanup='Unchanged full inventory removed after full-body queries; reference hashes and changed originals retained.'))
g=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
assert sha(g.read_bytes())=='825ee0d48177cd12354cdbf36fd36b61f0503ff3241356a7bf638ee0bc49fa45'
http=[json.loads(s) for s in (L/'http.jsonl').read_text().splitlines()]
save('provenance.json',dict(utc=now,lane=L.name,credit=0,counts=dict(additional=9,total=39,next=40),selected='Širola2402.14163v2 full introduction Conjecture; both kinds, all n>1',disposition='Complete classical bridge; proposed exclusion, root review pending',guard=dict(path=str(g),sha256=sha(g.read_bytes()),AS_MiB=512,groupRSS_MiB=512,CPU_seconds=210,wall_seconds=230,nominal_sample_ms=40,limitations='Sampled process group; unsampled peaks possible; never raised caps',environment=dict(OPENBLAS_NUM_THREADS=1,OMP_NUM_THREADS=1,PYTHONDONTWRITEBYTECODE=1)),primary=[item(L/'sources'/r['name']) for r in http if 'sha256' in r],http=http,history='history-receipt.json + history-delta.json + alias-audit.json',registry='registry-screen.json + registry-delta-audit.json; old two300-path gaps retained',checks=json.loads((L/'checks.json').read_bytes()),failures_and_limits=['initial context cat truncation corrected by structured full parse','missing r159/history-delta read; actual receipt reused','initial path hash lexical false matches corrected','long source-read output truncation, bounded rereads','No local raw search-response bytes; primary HTTP bytes retained','No journal version identified for Širola; no worldwide absence claim'],public_mutations=False,git=False,children=False,independent_review=False,Lean=False,manuscript=False))
# Preserve initial registry pass correction through prose, freeze corrected screen.
science=[p for p in L.rglob('*') if p.is_file() and p.name not in {'scientific-freeze.json','finalmanifest.json','verification.json','provenance.json'}]
save('scientific-freeze.json',dict(utc=now,role='Uncredited proof and research evidence; no acceptance',entries=[item(p) for p in sorted(science)]))
payload=[p for p in L.rglob('*') if p.is_file() and p.name not in {'finalmanifest.json','verification.json'}]
save('finalmanifest.json',dict(utc=now,entries=[item(p) for p in sorted(payload)]))
verified={}
for n in ['scientific-freeze.json','finalmanifest.json']:
 j=json.loads((L/n).read_bytes())
 for r in j['entries']:
  p=L/r['path'];assert p.stat().st_size==r['bytes'] and sha(p.read_bytes())==r['sha256'],str(p)
 verified[n]=dict(entries=len(j['entries']),sha256=sha((L/n).read_bytes()),status='PASS')
save('verification.json',dict(utc=now,verified=verified,manifest_exclusions=['finalmanifest.json (self)','verification.json (verification receipt)'],guard_sha256=sha(g.read_bytes())))
print(json.dumps(verified))
