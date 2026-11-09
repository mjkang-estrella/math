from pathlib import Path
import json,hashlib,sys
L=Path(__file__).resolve().parent; B=L.parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def J(p):return json.loads(Path(p).read_text())
def valid(p,r):
 b=Path(p).read_bytes();assert sha(b)==r['sha256'],str(p)
 if 'size' in r or 'bytes' in r:assert len(b)==r.get('size',r.get('bytes')),str(p)
 return b
m=J(L/'manifest.json'); listed={r['path'] for r in m['files']}
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()}-{'manifest.json','final-receipt.json'}
assert actual==listed,('payload membership mismatch',actual^listed)
for r in m['files']:valid(L/r['path'],r)
fr=J(L/'frozen_inputs.json');assert fr==J(L/'bindings.json');assert len(fr)==len({r['path'] for r in fr})
for r in fr:valid(r['path'],r)
refs={r['path'] for r in fr};required=set()
def add(p):required.add(str(Path(p)))
def upstream_manifest(name):
 d=B/name; add(d/'manifest.json');m=J(d/'manifest.json');rows=m if isinstance(m,list) else m['files']
 for r in rows:add(d/r['path']);valid(d/r['path'],r)
 return rows
def direct_bindings(name):
 for r in J(B/name/'bindings.json'):
  for k in ['original','copy']:
   if k not in r:continue
   p=Path(r[k]);p=p if p.is_absolute() else B/name/p;add(p);valid(p,r)
intake=B/'root-mathdb-breadth-intake-r457'
upstream_manifest(intake.name);direct_bindings(intake.name)
inv=B/'pi-mathdb-full-corpus-inventory-r301';add(inv/'manifest.json');vm=J(inv/'manifest.json');ch=[r for r in vm['files'] if r['path'].startswith('corpus/') and r['path'].endswith('.jsonl')];assert len(ch)==20
assert {p.name for p in (inv/'corpus').glob('*.jsonl')}=={Path(r['path']).name for r in ch}
for r in ch:add(inv/r['path']);valid(inv/r['path'],r)
for name in ['root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:upstream_manifest(name);direct_bindings(name)
for p in [B.parent/'ledger.json',B.parent/'prior-campaign-context.json',B.parents[4]/'sources/upstream.json',B.parents[4]/'sources/CONTENTS.md',B.parents[4]/'AGENTS.md',B.parent/'AGENTS.md',B/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']:
 if p.exists():add(p)
assert refs==required,('frozen input membership mismatch',refs^required)
r=J(intake/'reserved-ids.json');ids=r['ids'];q=J(intake/'queue.json');cov=J(intake/'coverage-delta.json');assert len(cov)==2833
assert len(ids)==len(set(ids))==50 and set(ids)=={x['mathdb_id'] for x in q};assert r['lane']==L.name
assert not set(ids)&set(r['other_active_reservations']);assert not set(ids)&set(map(int,cov));assert not set(ids)&{372627,372628,368940,404067,364119}
def idset(o):
 s=set()
 if isinstance(o,dict):
  for k,v in o.items():
   if k in ['mathdb_id','mathdb_ids','problem_ids']:s.update([v] if isinstance(v,int) else v if isinstance(v,list) else [])
   else:s.update(idset(v))
 elif isinstance(o,list):
  for v in o:s.update(idset(v))
 return s
for name in ['accepted-exclusions.json','historical-dispositions.json']:assert not set(ids)&idset(J(B/'root-mathdb-accepted-exclusions-r304'/name))
D=J(L/'dispositions.json');A=J(L/'assigned-records.json');assert len(D)==len(A)==50
assert {x['mathdb_id'] for x in D}==set(ids) and len({x['mathdb_id'] for x in D})==50
originals={}
for cr in ch:
 p=inv/cr['path']
 for n,line in enumerate(p.open(encoding='utf-8'),1):
  x=json.loads(line)
  if x.get('mathdb_id') in ids:
   i=x['mathdb_id'];assert i not in originals;originals[i]=(x,p,n,sha(line.encode('utf-8')))
assert set(originals)==set(ids)
for a in A:
 x,p,n,h=originals[a['record']['mathdb_id']];assert a['record']==x and a['original_chunk']==str(p) and a['original_line']==n and a['raw_line_sha256']==h
for d in D:
 x,p,n,h=originals[d['mathdb_id']];assert d['literal_statement']==x['statement'];assert d['statement_utf8_sha256']==sha(x['statement'].encode('utf-8'));assert d['canonical_record_sha256']==sha(json.dumps(x,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf-8'));assert d['original_chunk']==str(p) and d['original_line']==n and d['raw_line_sha256']==h;assert d['discovery_credit']==0
assert J(L/'proposals.json')==[]
sources=J(L/'sources.json');assert {r['source_url'] for r in sources}=={x[0]['source_url'] for x in originals.values()} and len(sources)==48
source_paths=set()
for r in sources:
 p=Path(r['path']);valid(p,r);t=p.with_suffix('.txt');assert sha(t.read_bytes())==r['text_sha256'];source_paths.update([str(p.relative_to(L)),str(t.relative_to(L))]);assert r['utc'] and r['version']
assert source_paths=={str(p.relative_to(L)) for p in (L/'sources').iterdir() if p.is_file()}
for r in J(L/'read-primary-passages.json'):
 lines=Path(r['path']).read_text().split('\n');s='\n'.join(f'{i}: {lines[i-1]}' for i in range(r['start_line'],r['end_line']+1));assert s==r['passage']
receipt=L/'final-receipt.json'
if receipt.exists():assert J(receipt)['manifest_sha256']==sha((L/'manifest.json').read_bytes()) and J(receipt)['integrity']=='PASS'
print(json.dumps({'integrity':'PASS','statements':50,'chunks':20,'flat_input_files':len(fr),'payload_files':len(listed),'primary_sources':48,'proposals':0,'mathematical_novelty_pass':False,'reported_coverage_baseline':2833,'potential_root_reconciled_coverage':2883,'counts':'9 additional / 39 total / next 40'}))
