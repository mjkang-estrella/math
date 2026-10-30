import sys,json,hashlib,datetime
from pathlib import Path
L=Path(__file__).resolve().parent
def h(b):return hashlib.sha256(b).hexdigest()
def write(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
mode=sys.argv[1];now=datetime.datetime.now(datetime.timezone.utc).isoformat()
if mode=='science':
 j=json.loads((L/'scientific-freeze.json').read_text());bad=[]
 for r in j['records']:
  p=L/r['path'];b=p.read_bytes()
  if h(b)!=r['sha256'] or len(b)!=r['bytes']:bad.append(r['path'])
 import checks
 actual=json.dumps(checks.main(),indent=2)+'\n'
 replay=actual==(L/'checks.json').read_text()
 write('scientific-verification.json',dict(utc=now,records=len(j['records']),bad=bad,deterministic_exact_replay=replay,pass_all=not bad and replay))
 assert not bad and replay
elif mode=='manifest':
 ex=['finalmanifest.json','manifest-verification.json'];rows=[]
 for p in sorted(L.rglob('*')):
  if p.is_file() and p.relative_to(L).as_posix() not in ex:
   b=p.read_bytes();rows.append(dict(path=p.relative_to(L).as_posix(),sha256=h(b),bytes=len(b)))
 write('finalmanifest.json',dict(utc=now,records=rows,exclusions=ex,policy='Self and final verification receipt only; no unmanifested stdout logs.'))
elif mode=='final':
 j=json.loads((L/'finalmanifest.json').read_text());bad=[]
 for r in j['records']:
  p=L/r['path'];b=p.read_bytes()
  if h(b)!=r['sha256'] or len(b)!=r['bytes']:bad.append(r['path'])
 expected={r['path'] for r in j['records']};actual={p.relative_to(L).as_posix() for p in L.rglob('*') if p.is_file()}-set(j['exclusions'])
 extra=sorted(actual-expected);missing=sorted(expected-actual)
 write('manifest-verification.json',dict(utc=now,records=len(j['records']),bad=bad,extra=extra,missing=missing,pass_all=not(bad or extra or missing),exclusions=j['exclusions']))
 assert not(bad or extra or missing)
print(mode,'PASS')
