import pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((L/'finalmanifest.json').read_text());fail=[]
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in m['excludes']}
assert actual==set(m['files'])
for n,e in m['files'].items():
 if sha(L/n)!=e['sha256'] or (L/n).stat().st_size!=e['bytes']:fail.append(n)
idx=json.loads((L/'freeze.json').read_text())
for e in idx:
 if sha(L/e['copy'])!=e['sha256']:fail.append(e['copy'])
 if e['kind']=='science' and sha(pathlib.Path(e['original']))!=e['sha256']:fail.append(e['original'])
hist=json.loads((L/'early-history.json').read_text())['verified_references']
for e in hist:
 if sha(pathlib.Path(e['path']))!=e['sha256']:fail.append(e['path'])
r=dict(status='PASS' if not fail else 'FAIL',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=sha(L/'finalmanifest.json'),manifest_files=len(actual),frozen_bindings=len(idx),history_references=len(hist),failures=fail,guarded=True,caps=dict(AS=536870912,groupRSS=536870912,CPU=210,wall=230),administrative_originals_rechecked=False)
(L/'verification-receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r));assert not fail
