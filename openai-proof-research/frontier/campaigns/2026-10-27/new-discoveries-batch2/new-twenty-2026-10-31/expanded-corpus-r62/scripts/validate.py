import pathlib,json,hashlib,itertools,datetime
D=pathlib.Path(__file__).resolve().parents[1]; sha=lambda b:hashlib.sha256(b).hexdigest()
r=json.loads((D/'reservation.json').read_text());x=json.loads((D/'results.json').read_text());assert len(x)==40 and set(map(int,x))==set(r['ids']);assert all(v['credit']==0 and not v['formal_endpoint_complete'] for v in x.values())
chunks={}
for k,v in x.items():
 p=pathlib.Path(v['provenance']['chunk']);p=p if p.is_absolute() else pathlib.Path.cwd()/p
 if p not in chunks:chunks[p]=p.read_bytes()
 b=chunks[p];raw=b.splitlines(keepends=True)[v['provenance']['line_1based']-1];assert raw.endswith(b'\n');assert (D/'raw'/f'{k}.jsonl').read_bytes()==raw
 o=json.loads(raw);assert str(o['mathdb_id'])==k and o['statement']==v['statement'];assert sha(b)==v['provenance']['chunk_sha256'];assert sha(raw)==v['provenance']['raw_sha256'];assert sha(o['statement'].encode())==v['provenance']['statement_utf8_sha256']
for p in (D/'sources').glob('*.receipt.json'):
 v=json.loads(p.read_text())
 if v.get('status')==200:assert sha(pathlib.Path(v['path']).read_bytes())==v['sha256']
C=D.parent.parent/'lanes/pi-mathdb-full-corpus-inventory-r301';m=json.loads((C/'manifest.json').read_text());verified=[]
for v in m['files']:
 if v['path'].startswith('corpus/mathdb-normalized-chunk-'):
  b=(C/v['path']).read_bytes();assert sha(b)==v['sha256'];verified.append(v['path'])
assert len(verified)==20
# Independent positional partition recognizer, as opposed to queue states.
def direct(w):
 n=len(w)
 for a in itertools.combinations(range(n),n//2):
  a=set(a)
  if ''.join(w[i] for i in range(n) if i in a)==''.join(w[i] for i in range(n) if i not in a):return True
 return False
def queue(w):
 states={''}
 for c in w:
  nxt=set()
  for q in states:
   nxt.add(q+c)
   if q and q[0]==c:nxt.add(q[1:])
  states=nxt
 return '' in states
count=0
for n in range(0,11,2):
 for a in itertools.product('01',repeat=n):
  w=''.join(a);assert queue(w)==direct(w);count+=1
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','reserved_entries':len(x),'raw_lines_verified':40,'all_manifest_chunks_verified':len(verified),'source_receipts_verified':len(list((D/'sources').glob('*.receipt.json'))),'independent_shuffle_comparisons':count,'credit':0,'lean_endpoint':None,'lean_rebuild':'not applicable: no endpoint','no_global_novelty_claim':True}
(D/'outputs/validation.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
