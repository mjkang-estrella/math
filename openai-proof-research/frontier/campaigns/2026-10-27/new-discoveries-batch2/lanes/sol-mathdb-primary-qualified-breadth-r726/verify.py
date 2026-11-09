"""Independent read-only verifier. Never imports/runs upstream code or writes receipts."""
import pathlib,json,hashlib,sys
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r725';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),('size',str(p));assert h(b)==e['sha256'],('hash',str(p))
def exact(root,m,negative=None):
 es=[dict(e) for e in m['files']];names={e['path'] for e in es};assert len(names)==len(es)
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])
 if negative=='extra':actual.add('injected-unlisted-payload')
 assert actual==names,('exact-file-set',actual^names)
 if negative=='hash':es[0]['sha256']='0'*64
 if negative=='size':es[0]['size']=es[0].get('size',es[0].get('bytes'))+1
 for e in es:check(root/e['path'],e)
def main():
 negative=sys.argv[1].split('=',1)[1] if len(sys.argv)>1 else None
 assert negative in [None,'hash','size','extra']
 exact(P,j(P/'manifest.json'),negative)
 for e in j(P/'flat-bindings.json'):check(pathlib.Path(e['path']),e)
 exact(I,j(I/'manifest.json'))
 for e in j(I/'bindings.json'):
  check(pathlib.Path(e['original']),e);check(pathlib.Path(e['copy']),e)
 cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 cov=j(I/'coverage-delta.json');assert len(cov)==9033
 active=j(I/'active-breadth-reservations.json');assert len(active)==3
 seen=set()
 for a in active:
  ids=set(a['ids']);assert len(ids)==50 and not ids&seen and not ids&set(map(int,cov)) and not ids&set(a['protected_ids']);seen|=ids
 for a in active:assert set(a['other_active_reservations'])==seen-set(a['ids'])
 res=j(I/'reserved-ids-r726.json');ids=set(res['ids']);assert len(ids)==50 and res['coverage_baseline']==9033 and res['active_hypothesis_ids']==[]
 assert ids=={r['mathdb_id'] for r in j(I/'queue-r726.json')}
 own=next(a for a in active if a['lane']==P.name)
 for k in ['ids','protected_ids','coverage_baseline','active_hypothesis_ids','lane','status']:assert own[k]==res[k]
 ds=j(P/'dispositions.json');assert len(ds)==50 and {d['mathdb_id'] for d in ds}==ids
 literals=j(P/'literal-records.json');assert len(literals)==50
 found={}
 for e in chunks:
  with (C/e['path']).open() as f:
   for n,line in enumerate(f,1):
    r=json.loads(line)
    if r['mathdb_id'] in ids:
     assert r['mathdb_id'] not in found;found[r['mathdb_id']]=(e['path'],n,r)
 assert len(found)==50
 for x in literals:
  p,n,r=found[x['record']['mathdb_id']];assert x=={'corpus_path':p,'corpus_line':n,'record':r}
 for d in ds:
  p,n,r=found[d['mathdb_id']];assert d['corpus_path']==p and d['corpus_line']==n and d['statement']==r['statement']
  assert d['canonical_record_sha256']==h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
  assert d['statement_utf8_sha256']==h(r['statement'].encode())
  assert d['classification'] in ['complete','definition-dependent','scope-ambiguous','incomplete'] and d['classification_reason'] and d['quantifier_scope'] and d['technical_assessment']
  assert d['complete_mathematical_statement_reviewed']==(d['classification']=='complete') and d['accepted_credit']==0 and not d['current_registry_cleared']
 assert j(P/'proposals.json')==[]
 for e in j(P/'source-provenance.json'):
  if 'path' in e:check(P/e['path'],e)
 for e in j(P/'derivative-bindings.json'):check(P/e['path'],e)
 print(json.dumps({'integrity':'PASS','literal_records':50,'original_chunks':20,'frozen_inputs':8,'reservation_sets':3,'baseline':9033,'credit':0,'scientific_acceptance':False}))
if __name__=='__main__':
 try:main()
 except Exception as e:print('MISMATCH '+repr(e),file=sys.stderr);sys.exit(1)
