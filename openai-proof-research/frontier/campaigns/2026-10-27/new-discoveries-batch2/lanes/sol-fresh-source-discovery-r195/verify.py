from pathlib import Path
import json,hashlib,datetime,sys
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
if sys.argv[1]=='prepare':
 rows=json.loads((L/'scientific-freeze.json').read_text())
 for p in sorted((L/'sources').iterdir()):
  q=L/'primary-copies'/p.name;q.parent.mkdir(exist_ok=True);q.write_bytes(p.read_bytes())
  row=dict(original=str(p),copy=str(q.relative_to(L)),sha256=sha(p))
  if row not in rows:rows.append(row)
 (L/'scientific-freeze.json').write_text(json.dumps(rows,indent=2)+'\n')
 for r in rows:assert sha(Path(r['original']))==sha(L/r['copy'])==r['sha256']
 (L/'scientific-beforeafter.json').write_text(json.dumps(dict(status='PASS',pairs=len(rows),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()),indent=2)+'\n')
 excluded=['finalmanifest.json','verification-receipt.json']
 files={str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and str(p.relative_to(L)) not in excluded}
 (L/'finalmanifest.json').write_text(json.dumps(dict(excluded=excluded,files=files),indent=2)+'\n')
 print('prepared',len(rows),len(files))
else:
 m=json.loads((L/'finalmanifest.json').read_text());rows=json.loads((L/'scientific-freeze.json').read_text())
 actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()}-set(m['excluded'])
 assert actual==set(m['files'])
 for n,h in m['files'].items():assert sha(L/n)==h,n
 for r in rows:assert sha(Path(r['original']))==sha(L/r['copy'])==r['sha256'],r
 receipt=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=sha(L/'finalmanifest.json'),manifest_entries=len(m['files']),scientific_pairs=len(rows),explicit_exclusions=m['excluded'])
 (L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(receipt)
