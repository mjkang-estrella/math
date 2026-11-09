import pathlib,json,hashlib,datetime
D=pathlib.Path(__file__).resolve().parents[1];sha=lambda b:hashlib.sha256(b).hexdigest()
r=json.loads((D/'results.json').read_text());ids=json.loads((D/'reservation.json').read_text())['ids'];assert len(r)==20 and set(r)==set(map(str,ids))
inv=D.parent.parent/'lanes/pi-mathdb-full-corpus-inventory-r301';mp=inv/'manifest.json';manifest=json.loads(mp.read_text());bound={pathlib.Path(x['path']).name:x for x in manifest['files'] if x['path'].startswith('corpus/mathdb-normalized-chunk-')};assert len(bound)==20
checks=[];chunks={}
for i,o in r.items():
 p=pathlib.Path(o['provenance']['chunk'])
 if p not in chunks:
  b=p.read_bytes();assert sha(b)==bound[p.name]['sha256'];chunks[p]=b.splitlines(keepends=True)
 line=chunks[p][o['provenance']['line_1based']-1];raw=(D/'raw'/f'{i}.jsonl').read_bytes();assert raw==line and line.endswith(b'\n')
 obj=json.loads(line);assert obj['mathdb_id']==int(i) and obj['statement']==o['statement'];assert sha(line)==o['provenance']['raw_sha256'];assert sha(obj['statement'].encode())==o['provenance']['statement_utf8_sha256']
 src=o['primary_source_review'];assert sha((D/src['local_html']).read_bytes())==src['html_sha256']
 assert not o['accepted'] and o['credit_claimed']==0 and o['lean']['endpoint'] is None
 checks.append(int(i))
receipts=[]
for p in (D/'sources').glob('*.receipt.json'):
 o=json.loads(p.read_text())
 if o.get('status')==200:
  target=pathlib.Path(o['path']);assert target.is_relative_to(D);assert sha(target.read_bytes())==o['sha256']
 receipts.append({'receipt':str(p.relative_to(D)),'status':o.get('status'),'error':o.get('error')})
reg=json.loads((D/'outputs/registry-screen.json').read_text())
for o in reg:
 p=pathlib.Path(o['file']);assert sha(p.read_bytes())==o['sha256'];assert o['truncated'] is False
result=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),exactly_20_ids=True,verified_ids=checks,manifest=str(mp),manifest_sha256=sha(mp.read_bytes()),manifest_bound_chunk_count=20,used_chunks_verified=len(chunks),raw_newline_preserved=True,all_source_receipts_hash_verified=True,receipts=receipts,registries_untruncated_path_scopes_verified=True,lean_packet_created=False,credit_claimed=0)
(D/'receipts/validation.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
