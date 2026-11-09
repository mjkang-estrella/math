import pathlib,json,hashlib,datetime,collections
D=pathlib.Path(__file__).resolve().parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
reservation=json.loads((D/'reservation.json').read_text())
results=json.loads((D/'results.json').read_text())
assert len(results)==40 and set(results)==set(map(str,reservation['ids']))
chunks={}
for key,r in results.items():
 assert int(key)==r['mathdb_id'] and r['credit']==0 and (r['lean_endpoint'] is None or key=='371639')
 raw=(D/f'raw/{key}.jsonl').read_bytes();prov=r['provenance']
 assert raw.endswith(b'\n') and sha(raw)==prov['raw_sha256']
 obj=json.loads(raw);assert obj['statement']==r['statement'] and obj['title']==r['title']
 assert sha(r['statement'].encode())==prov['statement_utf8_sha256']
 f=pathlib.Path(prov['chunk'])
 if f not in chunks:
  b=f.read_bytes();chunks[f]=(sha(b),b.splitlines(keepends=True))
 digest,lines=chunks[f]
 assert digest==prov['chunk_sha256'] and lines[prov['line_1based']-1]==raw
 receipt=json.loads((D/r['primary_receipt']).read_text());src=pathlib.Path(receipt['path'])
 assert receipt['status']==200 and sha(src.read_bytes())==receipt['sha256']==r['primary_sha256']
for f in (D/'sources').glob('*.receipt.json'):
 rec=json.loads(f.read_text())
 if 'sha256' in rec:assert sha(pathlib.Path(rec['path']).read_bytes())==rec['sha256']
root=json.loads((D/'sources/omega-root.json').read_text());shas={t['path']:t['sha'] for t in root['tree']}
reg=json.loads((D/'outputs/registry-screen.json').read_text())
for name in ['D5','Problems']:
 f=D.parent/f'expanded-corpus-r65/sources/omega-{name}.json';b=f.read_bytes();tree=json.loads(b)
 assert not tree['truncated'] and tree['sha']==shas[name]==reg[name]['sha'] and sha(b)==reg[name]['sha256']
assert json.loads((D/'lean/fresh-replay-r1/replay-receipts/result.json').read_text())['status']=='PASS'
manifest={str(p.relative_to(D)):{'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())} for p in sorted(D.rglob('*')) if p.is_file() and 'vendor' not in p.parts and 'fresh-replay-r1' not in p.parts and not p.name.endswith(('.olean','.ilean')) and '__pycache__' not in p.parts and p.name not in ['manifest.json','validation.json']}
(D/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
v={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'validated_exact_entries':40,'raw_lines_and_sources_hash_verified':True,'outcomes':dict(collections.Counter(r['outcome'] for r in results.values())),'proposed_credit':0,'lean_endpoint':'371639 only (zero credit pending review)','scope':'artifact integrity only; no theorem verification or acceptance'}
(D/'outputs/validation.json').write_text(json.dumps(v,indent=2)+'\n');print(json.dumps(v))
