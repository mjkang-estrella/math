import sys,json,hashlib,gzip,shutil
from pathlib import Path
L=Path(__file__).resolve().parent
def h(p):
 s=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(65536):s.update(b)
 return s.hexdigest()
if sys.argv[1]=='prepare':
 lock={str(p.relative_to(L)):h(p) for p in (L/'sources').iterdir() if p.name in ['original.pdf','original.txt','partition.html','partition.html.txt']}
 (L/'source-lock.json').write_text(json.dumps(lock,indent=2)+'\n')
 rec=json.loads((L/'context-receipts.json').read_text());drift=[]
 for x in rec:
  p=Path(x['original']);drift.append(dict(original=str(p),as_read=x['sha256'],current=h(p),unchanged=h(p)==x['sha256']))
 (L/'context-drift.json').write_text(json.dumps(drift,indent=2)+'\n')
 p=L/'screen.sqlite'
 if p.exists():
  p.unlink()
 if (L/'screen.sqlite.gz').exists():(L/'screen.sqlite.gz').unlink()
elif sys.argv[1]=='seal':
 excluded={'finalmanifest.json','manifest-verification.json'}
 entries={str(p.relative_to(L)):h(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in excluded}
 (L/'finalmanifest.json').write_text(json.dumps({'entries':entries,'excluded_self_reference':sorted(excluded)},indent=2)+'\n')
elif sys.argv[1]=='verify':
 m=json.loads((L/'finalmanifest.json').read_text());expected=m['entries'];actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in m['excluded_self_reference']}
 assert actual==set(expected),(actual-set(expected),set(expected)-actual)
 for p,v in expected.items():assert h(L/p)==v,p
 receipt=dict(manifest_sha256=h(L/'finalmanifest.json'),verified_entries=len(expected),status='PASS',limits='manifest and detached receipt intentionally excluded from manifest payload; not mathematical completeness')
 (L/'manifest-verification.json').write_text(json.dumps(receipt,indent=2)+'\n');print(receipt)
