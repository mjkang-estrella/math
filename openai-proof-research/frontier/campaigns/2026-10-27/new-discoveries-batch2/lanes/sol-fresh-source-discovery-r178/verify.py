from pathlib import Path
import json,hashlib,sys,datetime
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
mode=sys.argv[1];now=datetime.datetime.now(datetime.timezone.utc).isoformat()
if mode=='scientific':
 j=json.loads((L/'scientific-freeze.json').read_text());bad=[]
 for n,h,z in j['records']:
  p=L/n
  if sha(p)!=h or p.stat().st_size!=z:bad.append(n)
 for n,h in j['originals']:
  if sha(Path(n))!=h:bad.append(n)
 save('scientific-verification.json',dict(utc=now,science_count=len(j['records']),external_original_count=len(j['originals']),mismatches=bad,exclusions=j['exclusions'],pass_=not bad));assert not bad
else:
 j=json.loads((L/'finalmanifest.json').read_text());bad=[]
 for n,h,z in j['records']:
  p=L/n
  if sha(p)!=h or p.stat().st_size!=z:bad.append(n)
 actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()};known={r[0] for r in j['records']}
 extras=sorted(actual-known-set(j['exclusions']));assert not extras
 save('manifest-verification.json',dict(utc=now,manifest_sha256=sha(L/'finalmanifest.json'),records=len(j['records']),mismatches=bad,unlisted=extras,exclusions=j['exclusions'],pass_=not bad));assert not bad
print(mode,'PASS')
