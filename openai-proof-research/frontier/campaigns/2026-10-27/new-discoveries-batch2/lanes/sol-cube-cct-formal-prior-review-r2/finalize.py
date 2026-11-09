import pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
records=json.loads((L/'freeze.json').read_text());verified=[]
for r in records:
 if '/administrative/' in '/'+r['copy']:continue
 assert sha(pathlib.Path(r['original']))==r['sha256']==sha(L/r['copy'])
 verified.append(r)
for p in (L/'replay').glob('*.olean'):p.unlink()
(L/'before-after.json').write_text(json.dumps({'status':'PASS','scientific':verified,'administrative':'snapshot only','utc':str(datetime.datetime.now(datetime.timezone.utc))},indent=2))
manifest={str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
(L/'manifest.json').write_text(json.dumps(manifest,indent=2));print('manifest',len(manifest),'scientific-original/copy checks',len(verified))
