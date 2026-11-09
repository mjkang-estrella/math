#!/usr/bin/env python3
"""Independent read-only verifier. Run ONLY under the fixed helper_guard.py."""
from pathlib import Path
import json,hashlib,sys,copy,subprocess
O=Path(__file__).resolve().parent;L=O.parent;I=L/'root-mathdb-banzhaf-retirement-intake-r503';R=L/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(Path(p).read_text())
def digest(p):
 b=Path(p).read_bytes();return len(b),hashlib.sha256(b).hexdigest()
def check(p,e):assert digest(p)==(e.get('size',e.get('bytes')),e['sha256']),str(p)
def payload(root,m,extra=None):
 expected={e['path'] for e in m['files']};actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])
 if extra:actual.add(extra)
 assert actual==expected,('file set',actual^expected)
 for e in m['files']:check(root/e['path'],e)
def run():
 m=load(O/'manifest.json');assert m['excluded_exact_paths']==['manifest.json','final-verification-receipt.json']
 case=next((a.split('=',1)[1] for a in sys.argv if a.startswith('--negative-case=')),None)
 if case=='hash':m['files'][0]['sha256']='0'*64
 if case=='size':m['files'][0]['size']+=1
 payload(O,m,'__injected_extra__' if case=='extra-file' else None)
 for f in ['initial-bindings.json','flat-bindings.json','corpus-bindings.json','source-bindings.json','derivative-bindings.json']:
  for e in load(O/f):
   if 'path' in e:check(e['path'],e)
 intake=load(I/'manifest.json');payload(I,intake)
 for e in load(I/'bindings.json'):
  check(e['original'],e);check(e['copy'],e)
 rm=load(R/'manifest.json');assert any(e['original']==str(R/'manifest.json') and digest(R/'manifest.json')==(e['size'],e['sha256']) for e in load(I/'bindings.json'))
 chunks=[e for e in rm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(rm['frozen_inputs'])==8
 for e in chunks+rm['frozen_inputs']:check(R/e['path'],e)
 cov=load(I/'coverage-delta.json');assert len(cov)==3733
 seen=set();rs=load(I/'active-breadth-reservations.json')
 assert len(rs)==3
 for q in rs:
  ids=set(q['ids']);assert len(ids)==50 and not ids&seen and not ids&set(map(int,cov)) and not ids&set(q['protected_ids']);seen|=ids
 own=load(I/'reserved-ids-r506.json');ids=set(own['ids']);assert own==next(q for q in rs if q['lane']==O.name)
 assert ids=={r['mathdb_id'] for r in load(I/'queue-r506.json')}
 d=load(O/'dispositions.json');assert len(d)==50 and {r['mathdb_id'] for r in d}==ids
 recs={};loc={}
 for e in chunks:
  p=R/e['path']
  with p.open() as f:
   for n,line in enumerate(f,1):
    r=json.loads(line);i=r['mathdb_id']
    if i in ids:
     assert i not in recs;recs[i]=r;loc[i]=(str(p),n)
 assert set(recs)==ids
 for e in d:
  i=e['mathdb_id'];r=recs[i];s=r['statement'];assert (e['corpus_chunk'],e['corpus_line'])==loc[i]
  assert e['statement']==s and e['statement_utf8_sha256']==hashlib.sha256(s.encode('utf8')).hexdigest()
  assert e['canonical_record_sha256']==hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()
 a=load(O/'assigned-records.json');assert len(a)==50
 for e in a:assert e['record']==recs[e['record']['mathdb_id']] and (e['chunk'],e['line'])==loc[e['record']['mathdb_id']]
 assert len(load(O/'proposals.json'))<=3
 return m
try:
 m=run();negative=[]
 if '--negative-tests' in sys.argv:
  for name in ['hash','size','extra-file']:
   p=subprocess.run([sys.executable,'-B',str(O/'verify.py'),'--negative-case='+name],capture_output=True,text=True)
   assert p.returncode!=0 and 'FAIL:' in p.stderr,('negative accepted',name)
   negative.append({'case':name,'exit':p.returncode,'stderr':p.stderr.strip()})
 print(json.dumps({'integrity':'PASS','literal_reviews':50,'original_chunks':20,'frozen_inputs':8,'direct_pairs':len(load(I/'bindings.json')),'baseline':3733,'negative_rejections':negative,'math_or_novelty_pass':False}))
except Exception as e:
 print('FAIL: '+repr(e),file=sys.stderr);sys.exit(1)
