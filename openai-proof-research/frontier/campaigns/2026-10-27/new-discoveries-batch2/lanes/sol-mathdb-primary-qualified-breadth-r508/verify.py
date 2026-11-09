#!/usr/bin/env python3
"""Independent read-only integrity verifier. Run through the fixed helper guard."""
import pathlib,json,hashlib,sys
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-banzhaf-retirement-intake-r503';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def check_bytes(b,e):
 if len(b)!=e.get('size',e.get('bytes')):raise ValueError('size mismatch')
 if h(b)!=e['sha256']:raise ValueError('hash mismatch')
def check(p,e):
 try:check_bytes(p.read_bytes(),e)
 except Exception as err:raise ValueError(str(p)+': '+str(err)) from err
def exact(root,m,extra=()):
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}|set(extra)
 expected={e['path'] for e in m['files']}
 if len(expected)!=len(m['files']) or actual-set(m['excluded_exact_paths'])!=expected:raise ValueError('exact payload set mismatch: '+str(root))
 for e in m['files']:check(root/e['path'],e)
def rejected(f):
 try:f()
 except ValueError:return True
 raise ValueError('negative test was accepted')
def verify():
 exact(P,j(P/'manifest.json'))
 for e in j(P/'initial-bindings.json'):check(pathlib.Path(e['path']),e)
 for e in j(P/'flat-bindings.json'):check(pathlib.Path(e['path']),e)
 exact(I,j(I/'manifest.json'))
 pairs=j(I/'bindings.json')
 for e in pairs:
  for key in ['original','copy']:check(pathlib.Path(e[key]),e)
 cm=j(I/'frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json');check(C/'manifest.json',{'size':(I/'frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json').stat().st_size,'sha256':h((I/'frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json').read_bytes())})
 chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:
  p=pathlib.Path(e['path']);check(p if p.is_absolute() else C/p,e)
 cov=j(I/'coverage-delta.json');assert len(cov)==3733
 rs=j(I/'active-breadth-reservations.json');allids=[]
 for r in rs:
  ids=set(r['ids']);assert len(ids)==50 and not ids&set(map(int,cov)) and not ids&set(r['protected_ids']) and not ids&set(r['active_hypothesis_ids']);allids+=r['ids']
 assert len(allids)==len(set(allids))==150
 for r in rs:assert set(r['other_active_reservations'])==set(allids)-set(r['ids'])
 mine=j(I/'reserved-ids-r508.json');assert mine in rs;ids=set(mine['ids']);assert {r['mathdb_id'] for r in j(I/'queue-r508.json')}==ids
 ds=j(P/'dispositions.json');ss=j(P/'statements.json');assert len(ds)==len(ss)==50 and {d['ID'] for d in ds}=={s['ID'] for s in ss}==ids
 found={}
 for e in chunks:
  p=C/e['path']
  for n,line in enumerate(p.open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in ids:
    assert r['mathdb_id'] not in found;found[r['mathdb_id']]=(p,n,r)
 for d in ds+ss:
  p,n,r=found[d['ID']];assert d['chunk']==str(p.resolve()) and d['line']==n and d['literal']==r['statement']
  assert d['statement_utf8_sha256']==h(r['statement'].encode('utf8'))
  assert d['canonical_record_sha256']==h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf8'))
  if 'record' in d:assert d['record']==r
  else:assert d['accepted_credit']==0 and not d['prior_cleared'] and d['individual_assessment']
 proposals=j(P/'proposals.json');assert proposals==[]
 for s in j(P/'source-provenance.json'):
  if 'pdf_path' in s:check(pathlib.Path(s['pdf_path']),{'size':s['pdf_size'],'sha256':s['pdf_sha256']})
  if 'text_path' in s:check(pathlib.Path(s['text_path']),{'size':s['text_size'],'sha256':s['text_sha256']})
 b=b'ab';e={'size':2,'sha256':h(b)}
 tests={'hash':rejected(lambda:check_bytes(b'ac',e)),'size':rejected(lambda:check_bytes(b'abc',e)),'extra_file':rejected(lambda:exact(P,j(P/'manifest.json'),['unexpected-negative-control.txt']))}
 return dict(integrity='PASS',scientific_acceptance=False,math_or_novelty_pass=False,statements=50,proposals=0,corpus_chunks=20,frozen_inputs=8,original_copy_pairs=len(pairs),baseline_reported_literal_reviews=3733,disjoint_reserved_ids=150,mismatch_rejection_tests=tests,manifest={'sha256':h((P/'manifest.json').read_bytes()),'size':(P/'manifest.json').stat().st_size})
if __name__=='__main__':
 try:print(json.dumps(verify(),sort_keys=True))
 except Exception as e:print(json.dumps({'integrity':'FAIL','error':str(e)}));sys.exit(1)
