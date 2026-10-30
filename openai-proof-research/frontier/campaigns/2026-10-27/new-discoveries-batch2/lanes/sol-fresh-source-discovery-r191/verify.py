from pathlib import Path
import hashlib,json,datetime,sys
L=Path(__file__).resolve().parent;R=L.parents[5]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(n,o):(L/n).write_text(json.dumps(o,indent=2)+'\n')
mode=sys.argv[1];utc=datetime.datetime.now(datetime.timezone.utc).isoformat()
if mode=='science':
 bad=[];pairs=0
 for p,h,z in json.loads((L/'raw-history-inventory.json').read_text())['records']:
  a=R/p;b=L/'originals'/p
  for tag,f in [('original',a),('copy',b)]:
   if not f.is_file() or sha(f)!=h:bad.append([tag,str(f)])
  pairs+=1
 for row in json.loads((L/'additional-originals.json').read_text()):
  for f in [Path(row['original']),L/row['copy']]:
   if not f.is_file() or sha(f)!=row['sha256']:bad.append(['additional',str(f)])
  pairs+=1
 fs=json.loads((L/'scientific-freeze.json').read_text())['files']
 for p,h in fs.items():
  if sha(L/p)!=h:bad.append(['scientific input',p])
 result=dict(utc=utc,status='PASS' if not bad else 'FAIL',original_copy_pairs=pairs,source_input_files=len(fs),failures=bad,administrative_policy='Only saved context snapshots; no live NEXT/ledger binding')
 save('scientific-verification.json',result);print(result);assert not bad
elif mode=='manifest':
 m=json.loads((L/'finalmanifest.json').read_text());bad=[]
 for p,h in m['files'].items():
  if not (L/p).is_file() or sha(L/p)!=h:bad.append(p)
 actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()}-set(m['excludes'])
 if actual!=set(m['files']):bad.append('file-set mismatch')
 result=dict(utc=utc,status='PASS' if not bad else 'FAIL',entries=len(m['files']),manifest_sha256=sha(L/'finalmanifest.json'),excludes=m['excludes'],failures=bad)
 save('manifest-verification.json',result);print(result);assert not bad
