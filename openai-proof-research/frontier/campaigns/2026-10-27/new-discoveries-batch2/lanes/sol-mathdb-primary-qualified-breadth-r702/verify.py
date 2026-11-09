"""Independent read-only payload/original/literal verifier; mismatch => nonzero exit."""
import pathlib,json,hashlib,sys,itertools
D=pathlib.Path(sys.argv[1]).resolve() if len(sys.argv)>1 else pathlib.Path(__file__).resolve().parent
L=pathlib.Path(__file__).resolve().parent.parent;I=L/'root-mathdb-breadth-intake-r701';R=L/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def check(p,h,n):
 b=p.read_bytes();assert len(b)==n,('size mismatch',str(p));assert hashlib.sha256(b).hexdigest()==h,('hash mismatch',str(p))
def inventory(d,m):
 assert set(m['excluded_exact_paths'])=={'manifest.json','final-verification-receipt.json'}
 expected={e['path'] for e in m['files']};assert len(expected)==len(m['files'])
 actual={str(p.relative_to(d)) for p in d.rglob('*') if p.is_file()};assert actual-set(m['excluded_exact_paths'])==expected,('extra/missing payload',sorted(actual^expected))
 for e in m['files']:check(d/e['path'],e['sha256'],e['size'])
def main():
 inventory(D,load(D/'manifest.json'))
 bound=load(D/'flat-bindings.json');lookup={e['path']:e for e in bound};assert len(lookup)==len(bound)
 for e in bound:check(pathlib.Path(e['path']),e['sha256'],e['size'])
 # Rebuild intake exact expected file set without invoking its verifier.
 im=load(I/'manifest.json');ie={e['path'] for e in im['files']}|set(im['excluded_exact_paths'])
 assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}==ie
 for e in im['files']:check(I/e['path'],e['sha256'],e['size'])
 for e in load(I/'bindings.json'):
  for k in ['original','copy']:check(pathlib.Path(e[k]),e['sha256'],e['bytes'])
 rm=load(R/'manifest.json');chunks=[e for e in rm['files'] if e['path'].startswith('corpus/mathdb-normalized-chunk-')];assert len(chunks)==20 and len(rm['frozen_inputs'])==8
 rb=next(e for e in load(I/'bindings.json') if e['original']==str(R/'manifest.json'));check(R/'manifest.json',rb['sha256'],rb['bytes'])
 for e in chunks+rm['frozen_inputs']:check(R/e['path'],e['sha256'],e['bytes'])
 q=load(I/'queue-r702.json');ids={e['mathdb_id'] for e in q};res=load(I/'reserved-ids-r702.json');assert len(q)==len(ids)==50 and ids==set(res['ids'])
 coverage=set(map(int,load(I/'coverage-delta.json')));assert len(coverage)==8433
 active=load(I/'active-breadth-reservations.json');assert len(active)==3
 for e in active:
  s=set(e['ids']);assert len(s)==50 and not s&coverage and not s&set(e['protected_ids']);assert not e['active_hypothesis_ids']
 for a,b in itertools.combinations(active,2):assert not set(a['ids'])&set(b['ids'])
 assert set(next(e for e in active if e['lane']=='sol-mathdb-primary-qualified-breadth-r702')['ids'])==ids
 assert {e['lane'] for e in active}=={'sol-mathdb-primary-qualified-breadth-r702','sol-mathdb-primary-qualified-breadth-r700','claude-mathdb-primary-qualified-breadth-r628'}
 actual={}
 for e in chunks:
  p=R/e['path']
  with p.open() as f:
   for n,line in enumerate(f,1):
    r=json.loads(line)
    if r['mathdb_id'] in ids:
     assert r['mathdb_id'] not in actual;actual[r['mathdb_id']]=(r,str(p),n)
 ds=load(D/'dispositions.json');ls=load(D/'literal-records.json');assert len(ds)==len(ls)==50 and {e['mathdb_id'] for e in ds}==ids
 assert len({e['record']['mathdb_id'] for e in ls})==50
 for e in ls:
  r,p,n=actual[e['record']['mathdb_id']];assert e['record']==r and e['chunk']==p and e['line']==n
  assert e['canonical_sha256']==hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()
 for e in ds:
  r,p,n=actual[e['mathdb_id']];assert e['chunk']==p and e['line']==n and e['statement_utf8']==r['statement']
  assert e['statement_sha256']==hashlib.sha256(r['statement'].encode()).hexdigest()
  assert e['canonical_record_sha256']==hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()
  assert e['classification'] in ['complete','definition-dependent','scope-ambiguous','incomplete']
  for k in ['classification_reason','quantifiers','technical_assessment','disposition']:assert isinstance(e[k],str) and e[k]
  assert e['credit']==0 and not e['novelty_cleared']
 assert load(D/'proposals.json')==[]
 for e in load(D/'source-provenance.json'):
  assert 'failure' not in e
  check(D/(e['name']+'.pdf'),e['pdf_sha256'],e['pdf_size']);check(D/(e['name']+'.txt'),e['text_sha256'],e['text_size'])
 print(json.dumps({'integrity':'PASS','intake_original_copy_pairs':len(load(I/'bindings.json')),'original_chunks':20,'frozen_inputs':8,'literal_records':50,'proposals':0,'baseline':8433,'reservation_sets':3,'math_or_novelty_pass':False}))
if __name__=='__main__':
 try:main()
 except Exception as e:print('FAIL',repr(e),file=sys.stderr);sys.exit(1)
