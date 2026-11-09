from pathlib import Path
import hashlib,json,sys,datetime
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dependencies():
 f=json.loads((L/'freeze.json').read_text());checks=[]
 for row in f['scientific']:
  for p in [Path(row['original']),L/row['copy']]:
   actual=sha(p);assert actual==row['sha256'],str(p)
   checks.append(dict(path=str(p),sha256=actual))
 for row in f['administrative_snapshots']:
  p=L/row['snapshot'];assert sha(p)==row['sha256']
 return checks
checks=dependencies()
if sys.argv[1]=='before':
 (L/'before-report-hashes.json').write_text(json.dumps(dict(status='PASS',checks=checks),indent=2)+'\n')
elif sys.argv[1]=='manifest':
 files={str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
 (L/'manifest.json').write_text(json.dumps(dict(algorithm='sha256',excludes=['manifest.json','verification-receipt.json'],files=files),indent=2)+'\n')
elif sys.argv[1]=='verify':
 m=json.loads((L/'manifest.json').read_text());actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in m['excludes']}
 assert actual==set(m['files'])
 for name,expected in m['files'].items():assert sha(L/name)==expected,name
 receipt=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=sha(L/'manifest.json'),manifest_files=len(actual),original_and_copy_checks=checks,administrative='snapshots checked only; live originals mutable',limits='AS/groupRSS512MiB CPU210 wall230; no raises',counts='9 additional / 39 total / next40; unchanged')
 (L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
else:raise ValueError(sys.argv[1])
print(sys.argv[1], 'PASS',len(checks),'original/copy comparisons')
