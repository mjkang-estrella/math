from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((L/'manifest.json').read_text());bad=[]
for s,v in m.items():
 if h(L/s)!=v:bad.append(s)
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
assert actual==set(m),(actual-set(m),set(m)-actual)
rows=json.loads((L/'bindings.json').read_text())
for r in rows:
 if h(Path(r['original']))!=r['sha256'] or h(L/r['copy'])!=r['sha256']:bad.append(r['original'])
assert not bad,bad
receipt={'pass':True,'manifest_sha256':h(L/'manifest.json'),'manifest_entries':len(m),'source_pairs_verified_original_and_copy':len(rows),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'counts_unchanged':[9,39,40],'status':'HOLD pending root review; integrity verification is not mathematical acceptance'}
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt))
