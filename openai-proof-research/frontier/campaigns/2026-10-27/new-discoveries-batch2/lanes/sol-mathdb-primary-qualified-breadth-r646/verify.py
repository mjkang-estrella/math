"""Independent, read-only verifier. Run only through verify.sh / fixed helper guard."""
import pathlib,json,hashlib,re,sys
O=pathlib.Path(__file__).resolve().parent;L=O.parent;I=L/'root-mathdb-breadth-intake-r643';R=L/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def digest(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),f'size mismatch {p}';assert digest(b)==e['sha256'],f'hash mismatch {p}'
def payload(root,m,negative=None):
 excludes={'manifest.json','final-verification-receipt.json'}
 assert set(m['excluded_exact_paths'])==excludes
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}-excludes
 expected={e['path'] for e in m['files']};assert len(expected)==len(m['files'])
 if negative=='extra':actual.add('INJECTED_EXTRA_FILE')
 assert actual==expected,'extra/missing file rejection'
 for e in m['files']:
  if negative in ['hash','size'] and e['path']=='proposals.json':
   e=dict(e)
   if negative=='hash':e['sha256']='0'*64
   else:e['size']+=1
  check(root/e['path'],e)
def main():
 neg=sys.argv[2] if len(sys.argv)==3 and sys.argv[1]=='--negative' else None
 payload(O,load(O/'manifest.json'),neg)
 if neg:raise AssertionError('negative injection was not rejected')
 flat=load(O/'flat-bindings.json')
 for p,e in flat.items():check(pathlib.Path(p),e)
 for p,e in load(O/'initial-bindings.json').items():check(pathlib.Path(p),e)
 im=load(I/'manifest.json');actual={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(im['excluded_exact_paths']);assert actual=={e['path'] for e in im['files']}
 for e in im['files']:check(I/e['path'],e)
 pairs=load(I/'bindings.json')
 for e in pairs:
  for k in ['original','copy']:check(pathlib.Path(e[k]),e)
 assert str(R/'manifest.json') in flat
 inv=load(R/'manifest.json');chunks=[e for e in inv['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(inv['frozen_inputs'])==8
 for e in chunks+inv['frozen_inputs']:check(R/e['path'],e)
 cov=load(I/'coverage-delta.json');assert len(cov)==7033;covered=set(map(int,cov));res=load(I/'reserved-ids-r646.json');ids=set(res['ids']);assert len(ids)==50 and res['coverage_baseline']==7033
 active=load(I/'active-breadth-reservations.json');assert len(active)==3;sets=[set(a['ids']) for a in active]
 for j,s in enumerate(sets):
  assert len(s)==50 and not s&covered and not s&set(res['protected_ids'])
  for t in sets[:j]:assert not s&t
 assert ids=={x['mathdb_id'] for x in load(I/'queue-r646.json')}
 dispositions=load(O/'dispositions.json');literals=load(O/'literal-records.json');assert len(dispositions)==len(literals)==50
 ds={d['mathdb_id']:d for d in dispositions};ls={w['record']['mathdb_id']:w for w in literals};assert set(ds)==set(ls)==ids
 found={}
 for e in chunks:
  p=R/e['path']
  for n,line in enumerate(p.open(),1):
   m=re.search(r'"(?:mathdb_id|id)"\s*:\s*(\d+)',line)
   if m and int(m[1]) in ids:
    r=json.loads(line);a=r['mathdb_id'];assert a not in found;found[a]=r;w=ls[a];d=ds[a]
    assert w['record']==r and w['chunk']==str(p) and w['line']==n
    h=digest(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
    assert h==w['canonical_record_sha256']==d['canonical_record_sha256']
    assert d['corpus_chunk']==str(p) and d['corpus_line']==n and d['statement_utf8']==r['statement'] and digest(r['statement'].encode())==d['statement_sha256']
    assert d['classification'] in ['complete','definition-dependent','scope-ambiguous','incomplete'] and d['classification_reason_and_quantifiers'] and d['technical_assessment'] and d['accepted_credit']==0
 assert set(found)==ids and len(load(O/'proposals.json'))<=3
 for e in load(O/'source-provenance.json'):
  if 'path' in e:check(O/e['path'],e)
 print(json.dumps({'integrity':'PASS','intake_exact_payload':True,'original_copy_pairs':len(pairs),'original_corpus_chunks':20,'frozen_inputs':8,'baseline':7033,'literal_reviews':50,'reservations_disjoint':True,'proposals':len(load(O/'proposals.json')),'mathematical_acceptance':False,'novelty_cleared':False}))
if __name__=='__main__':
 try:main()
 except Exception as e:print('FAIL: '+str(e),file=sys.stderr);sys.exit(1)
