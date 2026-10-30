from pathlib import Path
import sys,json,hashlib,datetime
L=Path(__file__).resolve().parent;R=L.parents[5]
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
def check(rows,root):
 bad=[]
 for p,h,z in rows:
  f=root/p
  if not f.is_file() or len(f.read_bytes())!=z or sha(f.read_bytes())!=h:bad.append(p)
 return bad
if sys.argv[1]=='science':
 local=json.loads((L/'scientific-freeze.json').read_text())['records'];orig=json.loads((L/'history-receipt.json').read_text())['records']
 b1=check(local,L);b2=check(orig,R)
 save('scientific-verification.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),local_files=len(local),external_originals=len(orig),local_changes=b1,external_changes=b2,status='PASS' if not b1+b2 else 'FAIL',exclusions=['live administrative NEXT/ledger originals: snapshots only','scientific-freeze self','scientific-verification receipt','finalmanifest self','manifest-verification receipt']))
 assert not b1+b2,(b1,b2)
 print('PASS scientific freeze',len(local),'local and',len(orig),'external original files')
elif sys.argv[1]=='manifest':
 excluded=['finalmanifest.json','manifest-verification.json']
 rows=[[str(p.relative_to(L)),sha(p.read_bytes()),p.stat().st_size] for p in sorted(L.rglob('*')) if p.is_file() and p.name not in excluded]
 save('finalmanifest.json',dict(records=rows,exclusions=excluded))
 bad=check(json.loads((L/'finalmanifest.json').read_text())['records'],L)
 save('manifest-verification.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),files=len(rows),manifest_sha256=sha((L/'finalmanifest.json').read_bytes()),changes=bad,status='PASS' if not bad else 'FAIL',exclusions=excluded,meaning='Manifest excludes itself and its verification receipt to avoid self-reference; scientific verification is separately included.'))
 assert not bad
 print('PASS final manifest',len(rows),'files; explicit self/receipt exclusions')
