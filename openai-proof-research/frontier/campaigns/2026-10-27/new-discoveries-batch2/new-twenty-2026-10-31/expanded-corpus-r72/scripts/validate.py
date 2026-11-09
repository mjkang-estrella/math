import pathlib,json,hashlib,zipfile
D=pathlib.Path(__file__).resolve().parents[1];sha=lambda b:hashlib.sha256(b).hexdigest();x=json.loads((D/'extracted.json').read_text());r=json.loads((D/'results.json').read_text());reserved=json.loads((D/'reservation.json').read_text())['ids'];assert len(r)==40 and set(map(int,r))==set(reserved)
chunks={}
for i,o in x.items():
 p=pathlib.Path(o['provenance']['chunk'])
 if p not in chunks:
  b=p.read_bytes();chunks[p]=(sha(b),b.splitlines(keepends=True))
 h,lines=chunks[p];raw=(D/'raw'/f'{i}.jsonl').read_bytes();assert raw.endswith(b'\n') and raw==lines[o['provenance']['line_1based']-1];assert h==o['provenance']['chunk_sha256'] and sha(raw)==o['provenance']['raw_sha256'];assert sha(o['statement'].encode())==o['provenance']['statement_utf8_sha256'];assert r[i]['discovery_credit']==0
with zipfile.ZipFile(D/'377831-proof-packet.zip') as z:
 assert not any(n.endswith('.olean') for n in z.namelist())
 manifest=json.loads(z.read('source-manifest.json'))
 for p,h in manifest.items():assert sha(z.read(p))==h
replay=json.loads((D/'fresh-replay/replay-receipts/result.json').read_text());assert replay['status']=='PASS' and replay['local_declarations']==35
receipts=[json.loads(p.read_text()) for p in (D/'fresh-replay/replay-receipts').glob('*.receipt.json')];assert all(p['reason'] is None and p['peak_rss_bytes']<=6*1024**3 and p['wall_seconds']<140 for p in receipts)
print('PASS: 40 exact IDs/raw lines/hashes; zero credits; source-only packet manifest; fresh replay and capped receipt checks')
(D/'outputs/delivery-validation.json').write_text(json.dumps({'status':'PASS','entries':40,'raw_lines':40,'discovery_credit':0,'fresh_replay':replay,'packet_sha256':sha((D/'377831-proof-packet.zip').read_bytes())},indent=2))
