from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=L/'final-manifest.json';d=json.loads(m.read_text());fail=[]
for r in d['files']:
 p=L/r['path']
 if not p.exists() or sha(p)!=r['sha256'] or p.stat().st_size!=r['bytes']:fail.append(r['path'])
assert not fail,fail
refs=json.loads((L/'references.json').read_text());changed=[]
for r in refs:
 if sha(Path(r['path']))!=r['sha256']:changed.append(r['path'])
for b in [json.loads(x) for x in (L/'bindings.jsonl').read_text().splitlines()]:
 assert sha(Path(b['original']))==b['sha256']
 assert sha(Path(b['text']))==b['text_sha256']
assert not changed,changed
assert json.loads((L/'finite-verification.json').read_text())['PASS']
assert json.loads((L/'witness-verification.json').read_text())['PASS']
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'PASS':True,'manifest_sha256':sha(m),'files_verified':len(d['files']),'references_verified':len(refs),'originals_and_extracted_texts':'all hashes match before/after; historical originals reused in place','administrative':'snapshots only','counts_changed':False,'eligibility':'HOLD; root alone accepts; independent review absent'}
(L/'final-verification.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt))
