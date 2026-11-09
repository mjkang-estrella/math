from fetch import D
import json,hashlib,math,runpy,datetime,pathlib
sha=lambda b:hashlib.sha256(b).hexdigest()
x=json.loads((D/'results.json').read_text());ids=json.loads((D/'reservation.json').read_text())['ids'];assert set(map(int,x))==set(ids) and len(x)==40
chunks={}
for i,o in x.items():
 b=(D/o['raw_file']).read_bytes();assert b.endswith(b'\n');raw=json.loads(b);assert raw['mathdb_id']==int(i);assert raw['statement']==o['statement'];assert sha(b)==o['provenance']['raw_sha256'];assert sha(o['statement'].encode())==o['provenance']['statement_utf8_sha256'];p=o['provenance']['chunk']
 if p not in chunks:
  data=pathlib.Path(p).read_bytes();chunks[p]=(sha(data),data.splitlines(keepends=True))
 h,lines=chunks[p];assert h==o['provenance']['chunk_sha256'];assert lines[o['provenance']['line_1based']-1]==b
 assert o['credit']==0 and not o['formal_endpoint_complete']
receipts=[]
for p in (D/'sources').glob('*.receipt.json'):
 r=json.loads(p.read_text())
 if r.get('status')==200:assert sha(pathlib.Path(r['path']).read_bytes())==r['sha256']
 receipts.append(r)
# Independently compare Kronecker convolution to direct coefficient folding of
# binomial(n,k)*(-1)^(n-k) for the entire small overlapping box.
g=runpy.run_path(str(D/'scripts/agrawal.py'));mul=g['mul'];checked=0
for n in range(2,201):
 for r in range(2,13):
  a=[0]*r;a[0]=n-1;a[1]=1;b=[0]*r;b[0]=1;e=n
  while e:
   if e&1:b=mul(a,b,n,r)
   a=mul(a,a,n,r);e>>=1
  direct=[0]*r
  for k in range(n+1):direct[k%r]=(direct[k%r]+math.comb(n,k)*(-1)**(n-k))%n
  assert b==direct;checked+=1
inherited=[]
B=D.parent.parent
for p in [pathlib.Path('openai-proof-research/AGENTS.md'),B/'AGENTS.md',D.parent/'AGENTS.md',D.parent/'ledger.json',B/'ledger.json',B/'prior-campaign-context.json',pathlib.Path('openai-proof-research/sources/upstream.json'),pathlib.Path('openai-proof-research/sources/CONTENTS.md')]:
 if p.exists():inherited.append({'path':str(p.resolve()),'sha256':sha(p.read_bytes())})
meta={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exact_reserved_entries':len(x),'raw_newlines_and_chunk_lines_and_all_hashes':'PASS','successful_download_hashes':'PASS','direct_binomial_comparisons':checked,'inherited_read_only_hashes':inherited,'qualified_endpoints':0,'full_task_complete':False,'no_Lean_replay_claim':True}
(D/'outputs/validation.json').write_text(json.dumps(meta,indent=2)+'\n')
manifest={str(p.relative_to(D)):sha(p.read_bytes()) for p in D.rglob('*') if p.is_file() and p.name!='manifest-sha256.json' and '__pycache__' not in str(p) and not str(p.relative_to(D)).startswith('logs/validate')}
(D/'outputs/manifest-sha256.json').write_text(json.dumps(manifest,indent=2)+'\n');print(meta)
