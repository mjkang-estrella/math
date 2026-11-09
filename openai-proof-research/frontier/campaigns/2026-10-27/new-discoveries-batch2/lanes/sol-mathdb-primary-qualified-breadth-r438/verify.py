from pathlib import Path
import hashlib,json,datetime,sys
R=Path(__file__).resolve().parent;L=R.parent
EXCLUDE={'manifest.json','final-receipt.json'}
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def load(p):return json.loads(p.read_text())
def check(p,h,s=None):
 assert p.is_file(),str(p)
 assert s is None or p.stat().st_size==s,('size',str(p))
 assert digest(p)==h,('sha256',str(p))
def canonical(x):return hashlib.sha256(json.dumps(x,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode()).hexdigest()
# Independently recompute every original hash/size, not upstream receipts.
bindings=load(R/'bindings.json');assert len(bindings)==len({e['path'] for e in bindings})
for e in bindings:check(Path(e['path']),e['sha256'],e['size'])
manifest=load(R/'manifest.json')['files'];assert len(manifest)==len({e['path'] for e in manifest})
actual={str(p.relative_to(R)) for p in R.rglob('*') if p.is_file()}
assert actual-EXCLUDE=={e['path'] for e in manifest},('payload_set',actual-EXCLUDE ^ {e['path'] for e in manifest})
for e in manifest:check(R/e['path'],e['sha256'],e['size'])
for name in ['root-mathdb-breadth-intake-r437','pi-mathdb-full-corpus-inventory-r301','root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
 base=L/name;d=load(base/'manifest.json');entries=d['files']+d.get('frozen_inputs',[]) if isinstance(d,dict) else d
 for e in entries:check(base/e['path'],e['sha256'],e.get('size',e.get('bytes')))
 assert {str(p.relative_to(base)) for p in base.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'}=={e['path'] for e in entries}
 if name=='root-mathdb-breadth-intake-r437':
  for e in load(base/'bindings.json'):check(Path(e['original']),e['sha256'],e.get('size',e.get('bytes')))
I=L/'root-mathdb-breadth-intake-r437';res=load(I/'reserved-ids.json');ids=set(map(str,res['ids']));other=set(map(str,res['other_active_reservations']))
assert res['lane']==R.name and len(res['ids'])==len(ids)==50 and len(other)==50 and not ids&other
assert other==set(map(str,load(L/'root-mathdb-breadth-intake-r435/reserved-ids.json')['ids']))
assert set(map(str,[x['mathdb_id'] for x in load(I/'queue.json')]))==ids
baseline=load(I/'coverage-delta.json');assert len(baseline)==2333 and not ids&set(baseline)
assert not ids&{'372627','372628','368940','404067','364119'}
assert load(L/'root-mathdb-cayley-review-intake-r363/disposition.json')['mathdb_id']==364119
C=L/'pi-mathdb-full-corpus-inventory-r301';chunks=[e for e in load(C/'manifest.json')['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20
found={}
for e in chunks:
 check(C/e['path'],e['sha256'],e['bytes'])
 with (C/e['path']).open() as f:
  for line in f:
   x=json.loads(line);n=str(x['mathdb_id'])
   if n in ids:assert n not in found;found[n]=x
assert set(found)==ids
rows=load(R/'dispositions.json');assert len(rows)==50 and {str(x['mathdb_id']) for x in rows}==ids
assert canonical(load(R/'assigned-records.json'))==canonical(list(found.values()))
for row in rows:
 x=found[str(row['mathdb_id'])];assert row['literal_statement']==x['statement']
 assert row['literal_statement_sha256']==hashlib.sha256(x['statement'].encode()).hexdigest()
 assert row['canonical_record_sha256']==canonical(x)
 assert row['accepted_credit']==0 and row['registry_level'].startswith('HOLD:')
 assert all(row[k] for k in ['scope','reason','primary_level','proof_level','certificate_size','formal_dependencies'])
for e in load(R/'sourcebytes.json'):check(R/e['path'],e['sha256'],e['size'])
for e in load(R/'excerpts.json'):
 lines=(R/e['path']).read_text().splitlines();t='\n'.join(lines[e['start_line']-1:e['end_line']]);assert t==e['text'] and hashlib.sha256(t.encode()).hexdigest()==e['sha256'];assert str(e['mathdb_id']) in ids
assert load(R/'proposals.json')==[]
assert load(R/'administrative-check.json')['counts_unchanged']=={'additional':9,'total':39,'next':40}
receipt={'status':'PASS','verified_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'assignment_count':50,'baseline_reported_count':2333,'other_active_reservations':50,'original_chunks':20,'flat_original_bindings':len(bindings),'payload_files':len(manifest),'manifest_sha256':digest(R/'manifest.json'),'credit':0,'proposals':0,'current_registry':'HOLD','mathematical_or_novelty_certification':False}
(R/'final-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
