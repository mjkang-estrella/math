import pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((L/'manifest.json').read_text());bad=[]
for n,h in m.items():
 if sha(L/n)!=h:bad.append(n)
bindings=0
for f in L.glob('*-freeze.json'):
 for r in json.loads(f.read_text()):
  if sha(pathlib.Path(r['copy']))!=r['sha256']:bad.append(r['copy'])
  if f.name!='administrative-freeze.json' and sha(pathlib.Path(r['original']))!=r['sha256']:bad.append(r['original'])
  bindings+=1
history_checked=0
for name in ['history-index.json','alias-history.json','recent-summary-reference-recheck.json']:
 for r in json.loads((L/name).read_text()):
  if sha(pathlib.Path(r['path']))!=r['sha256']:bad.append(r['path'])
  history_checked+=1
assert 'manifest.json' not in m and 'verification-receipt.json' not in m
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
assert actual==set(m)
receipt={'status':'PASS' if not bad else 'FAIL','manifest_sha256':sha(L/'manifest.json'),'manifest_files':len(m),'freeze_bindings_verified':bindings,'immutable_history_references_verified':history_checked,'failures':bad,'verified_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'administrative_policy':'copies only; scientific originals and copies both checked','separate_process':True}
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt,indent=2));assert not bad
