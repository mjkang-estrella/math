from pathlib import Path
import hashlib,json,datetime,sys
L=Path(__file__).resolve().parent;R=L.parents[5]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
mode=sys.argv[1];fail=[];pairs=0
if mode=='science':
 for x in json.loads((L/'history-receipt.json').read_text())['records']:
  n,h,z=x
  for p in [R/n,L/'originals'/n]:
   if not p.is_file() or sha(p)!=h:fail.append(str(p))
  pairs+=1
 for x in json.loads((L/'additional-originals.json').read_text()):
  for p in [Path(x['original']),L/x['copy']]:
   if not p.is_file() or sha(p)!=x['sha256']:fail.append(str(p))
  pairs+=1
 for name in ['scientific-input-freeze.json','scientific-freeze.json']:
  for n,h in json.loads((L/name).read_text())['files'].items():
   if not (L/n).is_file() or sha(L/n)!=h:fail.append(name+':'+n)
 receipt=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS' if not fail else 'FAIL',original_copy_pairs=pairs,failures=fail,administrative='No live NEXT/ledger/prior-context checks; snapshot bytes only.')
 out='scientific-verification.json'
else:
 m=json.loads((L/'finalmanifest.json').read_text());excluded=set(m['excluded'])
 actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()}-excluded
 if actual!=set(m['files']):fail.append(dict(extra=sorted(actual-set(m['files'])),missing=sorted(set(m['files'])-actual)))
 for n,h in m['files'].items():
  if not (L/n).is_file() or sha(L/n)!=h:fail.append(n)
 receipt=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS' if not fail else 'FAIL',manifest_sha256=sha(L/'finalmanifest.json'),entries=len(m['files']),excluded=m['excluded'],failures=fail)
 out='manifest-verification.json'
(L/out).write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt));assert not fail
