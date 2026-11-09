import pathlib,json,hashlib,datetime
D=pathlib.Path(__file__).resolve().parents[1];sha=lambda b:hashlib.sha256(b).hexdigest()
r=json.loads((D/'results.json').read_text());reservation=json.loads((D/'reservation.json').read_text());checks=[]
assert len(r)==20 and set(map(int,r))==set(reservation['ids'])
chunks={}
for i,x in r.items():
 p=x['provenance'];path=pathlib.Path(p['chunk'])
 if path not in chunks:
  b=path.read_bytes();chunks[path]=(sha(b),b.splitlines(keepends=True))
 h,lines=chunks[path];raw=(D/f'raw/{i}.jsonl').read_bytes()
 assert h==p['chunk_sha256'] and lines[p['line_1based']-1]==raw and raw.endswith(b'\n')
 assert sha(raw)==p['raw_sha256'] and sha(x['statement'].encode())==p['statement_utf8_sha256']
 assert sha((D/x['source_file']).read_bytes())==x['source_receipt']['sha256']
 checks.append({'id':i,'raw_line_and_chunk_verified':True,'source_bytes_verified':True})
for p in (D/'sources').glob('*-tree.json'):
 o=json.loads(p.read_text());assert not o['truncated']
for p in (D/'outputs').glob('transversal*.jsonl'):
 for l in p.read_text().splitlines():
  o=json.loads(l);pr=o['p'];mod=pr*pr;w=o['witness'];res={(a%pr,b%pr) for a,b in w}
  assert len(res)==pr*pr
  support={((a-c)%mod,(b-d)%mod) for a,b in w for c,d in w}
  assert len(support)==o['best']==o['independent_support']
a=json.loads((D/'outputs/cambrian-fast8.json').read_text());b=json.loads((D/'outputs/cambrian.jsonl').read_text().splitlines()[-1]);assert a['image_counts']==[x['image'] for x in b['orientations']]
a=json.loads((D/'outputs/cambrian-rank9-merged.json').read_text());assert set(a['catalan_counts'])=={16796} and a['min']==a['linear'] and a['max']==a['bipartite']
for l in (D/'outputs/gonality-sequence.jsonl').read_text().splitlines():assert not json.loads(l)['failures']
(D/'receipts/validation.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'checks':checks,'diagnostic_crosschecks':'raw support recount, rank-7 Cambrian independent methods, rank-9 Catalan count, gonality-sequence output consistency','status':'PASS; ordinary Python checks, not Lean certification'},indent=2)+'\n')
manifest=[]
for p in sorted(D.rglob('*')):
 if p.is_file() and p.name!='artifact-manifest.json':manifest.append({'path':str(p.relative_to(D)),'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())})
(D/'artifact-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('PASS:',len(r),'ID-keyed results; raw lines, source bytes and diagnostic crosschecks verified')
