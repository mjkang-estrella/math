"""Independent read-only verifier. Run under verify.sh's fixed resource guard."""
import pathlib,json,hashlib,sys,collections,datetime
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r647';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def sha(b):return hashlib.sha256(b).hexdigest()
def ck(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),f'size mismatch: {p}';assert sha(b)==e['sha256'],f'hash mismatch: {p}'
def exact(root,m):
 ns=[e['path'] for e in m['files']];assert len(ns)==len(set(ns))
 assert {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])==set(ns),f'exact payload mismatch: {root}'
 for e in m['files']:ck(root/e['path'],e)
def payload_map(names,reader,m):
 assert names=={e['path'] for e in m['files']}
 for e in m['files']:
  b=reader(e['path']);assert len(b)==e['size'];assert sha(b)==e['sha256']
def negative_tests(m):
 # Virtual byte/name mutations: verifier logic exercised on actual payload without writes.
 names={e['path'] for e in m['files']};target='proposals.json';raw=(P/target).read_bytes();out={}
 for kind in ['hash','size','extra-file']:
  def read(n):
   b=(P/n).read_bytes()
   if n==target:
    if kind=='hash':return bytes([b[0]^1])+b[1:]
    if kind=='size':return b+b' '
   return b
  try:payload_map(names|({'UNEXPECTED'} if kind=='extra-file' else set()),read,m)
  except AssertionError:out[kind]='REJECTED'
  else:raise AssertionError('negative accepted: '+kind)
 return out
def main():
 m=j(P/'manifest.json');assert m['excluded_exact_paths']==['manifest.json','final-verification-receipt.json'];exact(P,m)
 for path,e in j(P/'initial-bindings.json').items():ck(pathlib.Path(path),e)
 for path,e in j(P/'flat-bindings.json').items():ck(pathlib.Path(path),e)
 exact(I,j(I/'manifest.json'))
 for e in j(I/'bindings.json'):
  ck(pathlib.Path(e['original']),e);ck(pathlib.Path(e['copy']),e)
 inv=j(C/'manifest.json');chunks=[e for e in inv['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(inv['frozen_inputs'])==8
 for e in chunks+inv['frozen_inputs']:ck(C/e['path'],e)
 r=j(I/'reserved-ids-r648.json');q=j(I/'queue-r648.json');ids=set(r['ids']);assert len(ids)==50 and ids=={x['mathdb_id'] for x in q};assert r['lane']==P.name
 cov=j(I/'coverage-delta.json');assert len(cov)==7083
 seen=set();active=j(I/'active-breadth-reservations.json')
 for a in active:
  s=set(a['ids']);assert len(s)==50 and not s&seen and not s&set(map(int,cov)) and not s&set(a['protected_ids']);seen|=s
 assert len(seen)==150 and len(active)==3
 for a in active:assert set(a['other_active_reservations'])==seen-set(a['ids'])
 assert ids==set(next(a for a in active if a['lane']==P.name)['ids'])
 ds=j(P/'dispositions.json');assert len(ds)==50 and {d['mathdb_id'] for d in ds}==ids
 originals={}
 # Read only assigned original lines. No unrelated scientific rows decoded.
 groups=collections.defaultdict(dict)
 for d in ds:groups[d['corpus_chunk']][d['corpus_line']]=d['mathdb_id']
 corpuspaths={str((C/e['path']).resolve()) for e in chunks}
 for path,lines in groups.items():
  assert path in corpuspaths
  with pathlib.Path(path).open('rb') as f:
   for n,b in enumerate(f,1):
    if n not in lines:continue
    z=json.loads(b);assert z['mathdb_id']==lines[n];originals[z['mathdb_id']]=z
 assert len(originals)==50
 literal=j(P/'literal-records.json');assert len(literal)==50
 for x in literal:assert x['record']==originals[x['record']['mathdb_id']]
 for d in ds:
  z=originals[d['mathdb_id']];assert d['statement_utf8']==z['statement'];assert d['statement_sha256']==sha(z['statement'].encode());assert d['canonical_record_sha256']==sha(json.dumps(z,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
  assert d['classification'] in {'complete','incomplete','definition-dependent','scope-ambiguous'} and d['classification_reason_and_quantifiers'] and d['technical_assessment']
  assert d['complete_mathematical_statement_reviewed']==(d['classification']=='complete') and d['accepted_credit']==0 and d['current_registry_cleared'] is False
 for e in j(P/'source-provenance.json'):
  if 'path' in e:ck(P/e['path'],e)
 assert j(P/'proposals.json')==[]
 return {'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'integrity':'PASS','scientific_acceptance':False,'novelty':'HOLD','literal_reviews':50,'baseline_literal_reviews':7083,'root_reconciliation_pending_total':7133,'classifications':dict(collections.Counter(d['classification'] for d in ds)),'proposals':0,'credit':0,'original_chunks':20,'frozen_inputs':8,'direct_original_copy_pairs':len(j(I/'bindings.json')),'all_three_reserved_sets_disjoint':True,'bounded_negative_tests':negative_tests(m),'manifest':{'sha256':sha((P/'manifest.json').read_bytes()),'size':(P/'manifest.json').stat().st_size}}
if __name__=='__main__':
 try:print(json.dumps(main(),indent=2))
 except Exception as e:print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
