from pathlib import Path
import hashlib,json,datetime
D=Path(__file__).resolve().parent; L=D.parent; B=L.parent; I=L/'root-mathdb-breadth-intake-r491'; C=L/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def sig(p):
 b=p.read_bytes();return {'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
refs=[]
def bind(p,kind,expect=None):
 s=sig(p)
 if expect:assert s=={'size':expect.get('size',expect.get('bytes')),'sha256':expect['sha256']},str(p)
 refs.append({'path':str(p),'kind':kind,**s})
# Administrative bindings precede any semantic reads.
for n in ['DECISION.md','adjudications.json','coverage-delta.json','reserved-ids.json','queue.json','manifest.json','bindings.json']:bind(I/n,'intake')
for n in ['ledger.json','prior-campaign-context.json']:bind(B/n,'administrative')
for p in [L/'root-mathdb-accepted-exclusions-r304'/'accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304'/'historical-dispositions.json'] :bind(p,'history')
for p in L.glob('*r363/DECISION.md'):bind(p,'Cayley-adjudication')
bind(C/'manifest.json','corpus-manifest')
m=load(I/'manifest.json'); excluded=set(m['excluded_exact_paths']); actual={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-excluded
assert actual=={x['path'] for x in m['files']}
for x in m['files']:bind(I/x['path'],'intake-manifest-payload',x)
for x in load(I/'bindings.json'):
 for k in ['original','copy']:bind(Path(x[k]),'direct-'+k,x)
cm=load(C/'manifest.json'); chunks=[x for x in cm['files'] if x['path'].startswith('corpus/mathdb-normalized-chunk-')]
assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for x in chunks+cm['frozen_inputs']:bind(C/x['path'],'corpus-chunk' if x in chunks else 'corpus-frozen-input',x)
r=load(I/'reserved-ids.json');q=load(I/'queue.json');ids=r['ids'];assert len(ids)==len(set(ids))==50 and set(ids)=={x['mathdb_id'] for x in q};assert len(r['other_active_reservations'])==len(set(r['other_active_reservations']))==100;assert not set(ids)&set(r['other_active_reservations']);assert not set(ids)&{372627,372628,368940,404067,364119}
(D/'flat-bindings.json').write_text(json.dumps(refs,indent=2)+'\n')
(D/'freeze-receipt.json').write_text(json.dumps({'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'references':len(refs),'chunks':20,'frozen_inputs':8,'intake_exact_manifest':True,'direct_bindings':True,'upstream_verifiers_executed':False},indent=2)+'\n')
print('PASS',len(refs),'flat references; 20 chunks + 8 frozen inputs')
