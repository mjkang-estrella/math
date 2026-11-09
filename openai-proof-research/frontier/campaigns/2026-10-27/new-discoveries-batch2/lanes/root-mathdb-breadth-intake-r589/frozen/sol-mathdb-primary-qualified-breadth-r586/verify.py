#!/usr/bin/env python3
"""Independent read-only verifier. Does not execute intake or producer code."""
from pathlib import Path
import json,hashlib,sys
D=Path(__file__).resolve().parent;L=D.parent
EX={'manifest.json','final-verification-receipt.json'}
def load(p):return json.loads(p.read_text())
def chk(p,x):
 b=p.read_bytes();assert len(b)==x.get('size',x.get('bytes')),f'size mismatch: {p}';assert hashlib.sha256(b).hexdigest()==x['sha256'],f'hash mismatch: {p}'
def payload(root,m):
 assert set(m['excluded_exact_paths'])==EX
 files=m['files'];names=[x['path'] for x in files];assert len(names)==len(set(names))
 assert all(not Path(n).is_absolute() and '..' not in Path(n).parts for n in names)
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}-EX
 assert actual==set(names),f'exact payload mismatch extra={actual-set(names)} missing={set(names)-actual}'
 for x in files:chk(root/x['path'],x)
def verify():
 m=load(D/'manifest.json')
 if len(sys.argv)==3 and sys.argv[1]=='--negative':
  target=next(x for x in m['files'] if x['path']=='SUMMARY.md')
  if sys.argv[2]=='hash':target['sha256']='0'*64
  elif sys.argv[2]=='size':target['size']+=1
  else:assert sys.argv[2]=='extra'
 payload(D,m)
 refs=load(D/'flat-bindings.json');assert len(refs)==len({x['path'] for x in refs})
 for x in refs:chk(Path(x['path']),x)
 for n in [585,587]:
  I=L/f'root-mathdb-breadth-intake-r{n}';im=load(I/'manifest.json');expected={x['path'] for x in im['files']};assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(im['excluded_exact_paths'])==expected
  for x in im['files']:chk(I/x['path'],x)
  for x in load(I/'bindings.json'):
   chk(Path(x['original']),x);chk(Path(x['copy']),x);assert Path(x['original']).read_bytes()==Path(x['copy']).read_bytes()
 R=L/'pi-mathdb-full-corpus-inventory-r301';inv=load(R/'manifest.json');chunks=[x for x in inv['files'] if x['path'].startswith('corpus/')];assert len(chunks)==20 and len(inv['frozen_inputs'])==8
 for x in chunks+inv['frozen_inputs']:chk(R/x['path'],x)
 r=load(L/'root-mathdb-breadth-intake-r585/reserved-ids.json');ids=set(r['ids']);assert len(ids)==50 and r['coverage_baseline']==5583
 assert {int(x['mathdb_id']) for x in load(L/'root-mathdb-breadth-intake-r585/queue.json')}==ids
 cov=load(L/'root-mathdb-breadth-intake-r587/coverage-delta.json');assert len(cov)==5633 and len(load(L/'root-mathdb-breadth-intake-r585/coverage-delta.json'))==5583
 protected=set(r['protected_ids']);seen=set();own=0
 for res in load(L/'root-mathdb-breadth-intake-r587/active-breadth-reservations.json'):
  s=set(res['ids']);assert len(s)==50 and not s&seen and not s&protected and not s&set(map(int,cov));seen|=s
  if res['lane']==D.name:assert s==ids;own+=1
 assert own==1
 records=load(D/'literal-records.json');disps=load(D/'dispositions.json');assert len(records)==len(disps)==50 and {x['id'] for x in records}=={x['mathdb_id'] for x in disps}==ids
 byid={x['id']:x for x in records};need={x['chunk'] for x in records};raw={}
 for name in need:
  for num,line in enumerate(Path(name).open(),1):
   obj=json.loads(line)
   if obj['mathdb_id'] in ids:raw[obj['mathdb_id']]=(name,num,obj)
 assert set(raw)==ids
 for d in disps:
  i=d['mathdb_id'];rec=byid[i];chunk,line,obj=raw[i];assert chunk==rec['chunk']==d['corpus_chunk'] and line==rec['line']==d['corpus_line'];assert obj==rec['record']
  canon=hashlib.sha256(json.dumps(obj,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest();assert canon==rec['canonical_record_sha256']==d['canonical_record_sha256']
  assert d['statement']==obj['statement'];assert hashlib.sha256(d['statement'].encode()).hexdigest()==d['statement_utf8_sha256']
  flags=d['scope_flags'];assert flags['literal_statement_read'] is True and all(type(x)==bool for x in flags.values());assert d['credit']==0 and flags['registry_cleared'] is False
 assert load(D/'proposals.json')==[]
 for x in load(D/'source-provenance.json'):
  if 'failure' not in x:chk(D/x['file'],x)
 for x in load(D/'derivative-bindings.json'):chk(Path(x['path']),x)
 return {'integrity':'PASS','record_reviews':50,'proposals':0,'original_corpus_chunks':20,'frozen_inputs':8,'flat_original_bindings':len(refs),'latest_baseline':5633,'scientific_or_novelty_pass':False}
if __name__=='__main__':
 try:print(json.dumps(verify(),sort_keys=True))
 except Exception as e:print('FAIL: '+str(e),file=sys.stderr);sys.exit(1)
