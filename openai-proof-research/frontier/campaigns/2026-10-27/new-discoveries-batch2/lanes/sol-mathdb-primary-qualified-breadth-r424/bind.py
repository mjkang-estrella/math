from pathlib import Path
import hashlib,json
L=Path('frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes').resolve(); O=L/'sol-mathdb-primary-qualified-breadth-r424'; rows={}; checks=[]
def bind(p,expected=None):
 p=Path(p).resolve(); b=p.read_bytes(); h=hashlib.sha256(b).hexdigest(); r={'original':str(p),'sha256':h,'size':len(b)}
 if expected:
  assert h==expected['sha256'],str(p)
  assert expected.get('size',expected.get('bytes')) in (None,len(b)),str(p)
 rows[str(p)]=r
 return b
def manifest(name):
 p=L/name/'manifest.json'; m=json.loads(bind(p))
 for r in (m if isinstance(m,list) else m['files']): bind(p.parent/r['path'],r)
 checks.append(name)
 return m
m=manifest('root-mathdb-breadth-intake-r423')
for r in json.loads((L/'root-mathdb-breadth-intake-r423/bindings.json').read_text()): bind(r['original'],r)
m=manifest('pi-mathdb-full-corpus-inventory-r301')
assert len([r for r in m['files'] if r['path'].startswith('corpus/')])==20
for name in ['root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
 manifest(name)
for p in [Path('AGENTS.md'),Path('sources/upstream.json'),Path('sources/CONTENTS.md'),L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']:bind(p)
r=json.loads((L/'root-mathdb-breadth-intake-r423/reserved-ids.json').read_text()); q=json.loads((L/'root-mathdb-breadth-intake-r423/queue.json').read_text()); c=json.loads((L/'root-mathdb-breadth-intake-r423/coverage-delta.json').read_text())
assert len(c)==1983
assert len(r['ids'])==50 and set(r['ids'])=={x['mathdb_id'] for x in q}
assert not set(r['ids']) & (set(map(int,c))|set(r['other_active_reservations'])|{372627,372628,368940,404067,364119})
(O/'bindings.json').write_text(json.dumps(list(rows.values()),indent=2)+'\n')
(O/'preflight.json').write_text(json.dumps({'verified_manifests':checks,'original_bindings':len(rows),'corpus_chunks':20,'baseline':1983,'assigned':50,'status':'PASS'},indent=2)+'\n')
records=[]; locations=[]
for p in sorted((L/'pi-mathdb-full-corpus-inventory-r301/corpus').glob('*.jsonl')):
 for n,line in enumerate(p.open(),1):
  a=json.loads(line)
  if a['mathdb_id'] in r['ids']:
   records.append(a);locations.append({'mathdb_id':a['mathdb_id'],'original':str(p),'line':n,'canonical_sha256':hashlib.sha256(json.dumps(a,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode()).hexdigest(),'statement_sha256':hashlib.sha256(a['statement'].encode()).hexdigest()})
assert len(records)==50
(O/'records.json').write_text(json.dumps(records,indent=2,ensure_ascii=False)+'\n');(O/'record-locations.json').write_text(json.dumps(locations,indent=2)+'\n')
print('PASS',len(rows))
