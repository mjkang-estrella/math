"""Independent read-only verifier. Run only through the prescribed helper guard."""
from pathlib import Path
import json,hashlib,sys
P=Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r705';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),f'size: {p}';assert h(b)==e['sha256'],f'hash: {p}'
def exact(root,m):
 names=[e['path'] for e in m['files']];assert len(names)==len(set(names))
 assert {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])==set(names),'extra/missing file'
 for e in m['files']:check(root/e['path'],e)
m=j(P/'manifest.json');assert set(m['excluded_exact_paths'])=={'manifest.json','final-verification-receipt.json'}
if '--negative-hash' in sys.argv:m['files'][0]['sha256']='0'*64
if '--negative-size' in sys.argv:m['files'][0]['size']+=1
if '--negative-extra' in sys.argv:m['files']=m['files'][1:]
exact(P,m)
for e in j(P/'flat-bindings.json'):check(Path(e['path']),e)
exact(I,j(I/'manifest.json'))
for e in j(I/'bindings.json'):
 for k in ['original','copy']:check(Path(e[k]),e)
cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
cov=j(I/'coverage-delta.json');assert len(cov)==8533
active=j(I/'active-breadth-reservations.json');seen=set();assert len(active)==3
for r in active:
 ids=set(r['ids']);assert len(ids)==50 and not ids&seen and not ids&set(map(int,cov)) and not ids&set(r['protected_ids']);seen|=ids
assert len(seen)==150
for r in active:assert set(r['other_active_reservations'])==seen-set(r['ids'])
res=j(I/'reserved-ids-r706.json');ids=set(res['ids']);assert ids=={r['mathdb_id'] for r in j(I/'queue-r706.json')} and len(ids)==50
assert next(r for r in active if r['lane']==P.name)['ids']==res['ids']
assert any(r['lane'].endswith('r704') for r in active)
assert any(r['lane'].endswith('r628') and r['status']=='rate_limit_held_not_reconciled' for r in active)
found={}
for e in chunks:
 for n,line in enumerate((C/e['path']).open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:
   assert r['mathdb_id'] not in found;found[r['mathdb_id']]=(e['path'],n,r)
assert set(found)==ids
ls=j(P/'literal-records.json');ds=j(P/'dispositions.json');assert len(ls)==len(ds)==50 and {d['mathdb_id'] for d in ds}==ids
assert len({d['mathdb_id'] for d in ls})==50
for x in ls:
 ck,n,r=found[x['mathdb_id']];assert x['record']==r and x['chunk']==ck and x['line']==n
 assert x['canonical_record_sha256']==h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
 assert x['statement_sha256']==h(r['statement'].encode())
for d in ds:
 ck,n,r=found[d['mathdb_id']];assert d['chunk']==ck and d['line']==n and d['statement_utf8']==r['statement']
 assert d['statement_sha256']==h(r['statement'].encode())
 assert d['canonical_record_sha256']==h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
 assert d['classification'] in {'complete','definition-dependent','scope-ambiguous','incomplete'} and d['classification_reason'] and d['technical_assessment'] and d['quantifier_scope']
 assert d['accepted_credit']==0 and d['replacement'] is False and d['current_registry_cleared'] is False
assert j(P/'proposals.json')==[]
for r in j(P/'source-provenance.json'):
 if 'failure' in r:continue
 check(P/(r['version']+'.pdf'),{'size':r['pdf_size'],'sha256':r['pdf_sha256']})
 check(P/(r['version']+'.txt'),{'size':r['text_size'],'sha256':r['text_sha256']})
if (P/'final-verification-receipt.json').exists():
 receipt=j(P/'final-verification-receipt.json');check(P/'manifest.json',receipt['manifest'])
print(json.dumps({'integrity':'PASS','literal_records':50,'original_chunks':20,'frozen_inputs':8,'baseline':8533,'reservation_disjointness':True,'exact_payload_files':len(m['files']),'math_or_novelty_pass':False}))
