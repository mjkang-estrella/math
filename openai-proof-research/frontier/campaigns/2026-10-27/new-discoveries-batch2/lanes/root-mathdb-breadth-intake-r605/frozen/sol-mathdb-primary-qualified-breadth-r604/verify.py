"""Independent read-only verifier. Run only under the assigned helper_guard.py."""
import pathlib,json,hashlib,sys,datetime
D=pathlib.Path(__file__).resolve().parent
EXCLUDED={'manifest.json','final-verification-receipt.json'}
def load(p):return json.loads(p.read_text())
def digest(b):return hashlib.sha256(b).hexdigest()
def check_bytes(b,e,label):
 if len(b)!=e.get('size',e.get('bytes')):raise ValueError('size mismatch: '+label)
 if digest(b)!=e['sha256']:raise ValueError('hash mismatch: '+label)
def filecheck(p,e):
 if p.is_symlink():raise ValueError('symlink: '+str(p))
 check_bytes(p.read_bytes(),e,str(p))
def payloadcheck(files,m):
 expected={e['path']:e for e in m['files']}
 if len(expected)!=len(m['files']) or set(files)!=set(expected):raise ValueError('exact payload mismatch')
 for n,b in files.items():check_bytes(b,expected[n],n)
def payloadfiles():return {str(p.relative_to(D)):p.read_bytes() for p in D.rglob('*') if p.is_file() and str(p.relative_to(D)) not in EXCLUDED}
def run():
 m=load(D/'manifest.json');assert set(m['excluded_exact_paths'])==EXCLUDED
 for p in D.rglob('*'):assert not p.is_symlink(),str(p)
 payloadcheck(payloadfiles(),m)
 bindings=load(D/'flat-bindings.json');assert len({e['path'] for e in bindings})==len(bindings)
 for e in bindings:filecheck(pathlib.Path(e['path']),e)
 L=D.parent;I=L/'root-mathdb-breadth-intake-r603';R=L/'pi-mathdb-full-corpus-inventory-r301'
 im=load(I/'manifest.json');actual={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}
 assert actual=={e['path'] for e in im['files']}|set(im['excluded_exact_paths'])
 for e in im['files']:filecheck(I/e['path'],e)
 for e in load(I/'bindings.json'):
  filecheck(pathlib.Path(e['original']),e);filecheck(pathlib.Path(e['copy']),e)
 inv=load(R/'manifest.json');chunks=[e for e in inv['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(inv['frozen_inputs'])==8
 for e in chunks+inv['frozen_inputs']:filecheck(R/e['path'],e)
 a=load(I/'reserved-ids.json');q=load(I/'queue.json');cov=load(I/'coverage-delta.json');active=load(I/'active-breadth-reservations.json')
 assert len(cov)==6033 and len(q)==50 and a['lane']==D.name and [x['mathdb_id'] for x in q]==a['ids']
 ids=set(a['ids']);assert len(ids)==50
 seen=set();covered=set(map(int,cov));protected=set(a['protected_ids']);lanes=[]
 for x in active:
  s=set(x['ids']);assert len(s)==50 and not s&(seen|covered|protected);seen|=s;lanes.append(x['lane'])
 assert set(lanes)=={'claude-mathdb-primary-qualified-breadth-r602','sol-mathdb-primary-qualified-breadth-r600','sol-mathdb-primary-qualified-breadth-r604'}
 assert ids<=seen and set(a['other_active_reservations'])==seen-ids and len((I/'routing-queue.jsonl').read_text().splitlines())==8000
 rows=load(D/'literal-records.json');disp=load(D/'dispositions.json');assert len(rows)==len(disp)==50 and {d['mathdb_id'] for d in disp}==ids
 found={}
 for e in chunks:
  p=R/e['path']
  with p.open() as f:
   for n,line in enumerate(f,1):
    r=json.loads(line);i=r.get('mathdb_id',r.get('id'))
    if i in ids:
     assert i not in found;found[i]=(p,n,r)
 assert set(found)==ids
 byid={d['mathdb_id']:d for d in disp}
 for x in rows:
  i=x['record']['mathdb_id'];p,n,r=found[i];d=byid[i]
  assert x['record']==r and x['corpus_path']==str(p) and x['line']==n
  h=digest(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
  assert x['canonical_record_sha256']==d['canonical_record_sha256']==h
  assert d['statement_exact_utf8']==r['statement'] and d['statement_utf8_sha256']==digest(r['statement'].encode())
  assert d['corpus_path']==str(p) and d['corpus_line']==n and d['accepted_credit']==0
  if d['independent_statement_flag']=='incomplete':assert not d['complete_self_contained_statement']
 assert load(D/'proposals.json')==[]
 for e in load(D/'source-provenance.json')+load(D/'derivative-bindings.json'):filecheck(D/e['path'],e)
 if (D/'final-verification-receipt.json').exists():
  receipt=load(D/'final-verification-receipt.json');filecheck(D/'manifest.json',receipt['manifest'])
 return {'integrity_pass':True,'mathematics_pass':False,'novelty_pass':False,'literal_records':50,'corpus_chunks':20,'frozen_inputs':8,'coverage_baseline':6033,'payload_files':len(m['files']),'manifest':{'sha256':digest((D/'manifest.json').read_bytes()),'size':(D/'manifest.json').stat().st_size},'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
if __name__=='__main__':
 try:print(json.dumps(run(),indent=2))
 except Exception as e:print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
