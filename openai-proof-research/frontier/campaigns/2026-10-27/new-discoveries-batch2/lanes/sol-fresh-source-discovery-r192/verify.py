from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
fail=[];rows=json.loads((L/'scientific-freeze.json').read_text())
for r in rows:
 for p in [Path(r['original']),L/r['copy']]:
  if not p.exists() or sha(p)!=r['sha256']:fail.append(str(p))
m=json.loads((L/'finalmanifest.json').read_text())
for n,h in m['files'].items():
 if not (L/n).is_file() or sha(L/n)!=h:fail.append(n)
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()}-set(m['exclusions'])
if actual!=set(m['files']):fail.append(dict(missing=sorted(set(m['files'])-actual),extra=sorted(actual-set(m['files']))))
r=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),scientific_pairs=len(rows),manifest_entries=len(m['files']),failures=fail,pass_all=not fail,manifest_sha256=sha(L/'finalmanifest.json'),exclusions=m['exclusions'])
(L/'verification-receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r));assert not fail
