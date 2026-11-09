"""Independent read-only verifier. Run through the fixed helper_guard; writes nothing."""
import json,hashlib,pathlib,sys
D=pathlib.Path(__file__).resolve().parent;L=D.parent;I=L/'root-mathdb-breadth-intake-r559'
def sha(b):return hashlib.sha256(b).hexdigest()
def validate_bytes(b,e):
 assert len(b)==e.get('size',e.get('bytes')),'size mismatch'
 assert sha(b)==e['sha256'],'hash mismatch'
def check(p,e):validate_bytes(p.read_bytes(),e)
def exact(actual,expected):assert set(actual)==set(expected),'extra/missing file mismatch'
def negative_tests():
 b=b'abcd';e={'size':4,'sha256':sha(b)};out={}
 for name,f in [('hash',lambda:validate_bytes(b'abce',e)),('size',lambda:validate_bytes(b'abcdx',e)),('extra_file',lambda:exact(['a','extra'],['a']))]:
  try:f()
  except AssertionError:out[name]='rejected'
  else:raise AssertionError('negative accepted '+name)
 return out
def main():
 receipt=D/'final-verification-receipt.json'
 if len(sys.argv)==3:pin={'sha256':sys.argv[1],'size':int(sys.argv[2])}
 else:pin=json.loads(receipt.read_text())['manifest']
 check(D/'manifest.json',pin);m=json.loads((D/'manifest.json').read_text())
 assert m['excluded_exact_paths']==['manifest.json','final-verification-receipt.json']
 exact([str(p.relative_to(D)) for p in D.rglob('*') if p.is_file()],[e['path'] for e in m['files']]+m['excluded_exact_paths'])
 assert len({e['path'] for e in m['files']})==len(m['files'])
 for e in m['files']:check(D/e['path'],e)
 for e in json.loads((D/'flat-bindings.json').read_text()):check(pathlib.Path(e['path']),e)
 im=json.loads((I/'manifest.json').read_text());exact([str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()],[e['path'] for e in im['files']]+im['excluded_exact_paths'])
 for e in im['files']:check(I/e['path'],e)
 for e in json.loads((I/'bindings.json').read_text()):
  check(pathlib.Path(e['original']),e);check(pathlib.Path(e['copy']),e)
 r=L/'pi-mathdb-full-corpus-inventory-r301';rm=json.loads((r/'manifest.json').read_text());chunks=[e for e in rm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(rm['frozen_inputs'])==8
 # Check original inventory manifest is exactly the intake-bound copy.
 assert (r/'manifest.json').read_bytes()==(I/'frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json').read_bytes()
 for e in chunks+rm['frozen_inputs']:check(r/e['path'],e)
 for n in ['accepted-exclusions.json','historical-dispositions.json']:
  assert (r/'frozen'/n).read_bytes()==(L/'root-mathdb-accepted-exclusions-r304'/n).read_bytes()
 C=json.loads((I/'coverage-delta.json').read_text());assert len(C)==4933
 R=json.loads((I/'reserved-ids.json').read_text());Q=json.loads((I/'queue.json').read_text());assert R['lane']==D.name and len(R['ids'])==len(set(R['ids']))==50 and set(R['ids'])=={e['mathdb_id'] for e in Q}
 seen=set();active=json.loads((I/'active-breadth-reservations.json').read_text());assert len(active)==3
 for a in active:
  s=set(a['ids']);assert len(s)==50 and not(s&seen) and not(s&set(map(int,C))) and not(s&set(R['protected_ids']));seen|=s
 assert set(R['ids'])<=seen and set(R['other_active_reservations'])==seen-set(R['ids'])
 assert R['active_hypothesis_ids']==[]
 disp=json.loads((D/'dispositions.json').read_text());assigned=json.loads((D/'assigned-records.json').read_text());assert len(disp)==len(assigned)==50;assert {x['mathdb_id'] for x in disp}==set(R['ids'])
 got={};locations={}
 for e in chunks:
  p=r/e['path']
  for n,line in enumerate(p.open(),1):
   rec=json.loads(line);i=rec['mathdb_id']
   if i in R['ids']:
    assert i not in got;got[i]=rec;locations[i]=(str(p),n)
 for a,d in zip(assigned,disp):
  rec=a['record'];i=rec['mathdb_id'];assert got[i]==rec and d['mathdb_id']==i
  assert locations[i]==(a['chunk'],a['line'])==(d['corpus_chunk'],d['corpus_line'])
  assert d['literal_statement']==rec['statement']
  assert d['statement_sha256']==a['statement_sha256']==sha(rec['statement'].encode('utf-8'))
  assert d['canonical_record_sha256']==a['canonical_record_sha256']==sha(json.dumps(rec,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf-8'))
  assert d['accepted_credit']==0 and not d['novelty_cleared']
 assert json.loads((D/'proposals.json').read_text())==[]
 print(json.dumps({'integrity':'PASS','scientific_or_novelty_pass':False,'literal_reviews':50,'baseline':4933,'original_chunks':20,'frozen_inputs':8,'negative_tests':negative_tests()}))
if __name__=='__main__':
 try:main()
 except Exception as e:print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
