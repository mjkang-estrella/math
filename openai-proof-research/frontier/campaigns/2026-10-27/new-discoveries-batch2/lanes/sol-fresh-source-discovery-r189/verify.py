import sys,json,hashlib,datetime
from pathlib import Path
L=Path(__file__).resolve().parent;R=L.parents[5]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
mode=sys.argv[1];manifest='scientific-freeze.json' if mode=='scientific' else 'finalmanifest.json'
j=json.loads((L/manifest).read_text());bad=[]
for n,h in j['files'].items():
 if not (L/n).is_file() or sha(L/n)!=h:bad.append(n)
count=0
for p,c,h,z in json.loads((L/'original-copy-provenance.json').read_text()):
 if sha(R/p)!=h or sha(L/c)!=h:bad.append([p,c])
 count+=1
for p,c,h,z in json.loads((L/'primary-copy-provenance.json').read_text()):
 if sha(L/p)!=h or sha(L/c)!=h:bad.append([p,c])
 count+=1
g=json.loads((L/'guard-binding.json').read_text())
if sha(Path(g['path']))!=g['sha256']:bad.append('guard drift')
if mode=='final':
 actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()}-set(j['explicit_exclusions'])
 if actual!=set(j['files']):bad.append('manifest census')
out=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest=manifest,manifest_sha256=sha(L/manifest),files=len(j['files']),original_copy_pairs=count,bad=bad,pass_all=not bad,administrative_live_files_checked=False)
(L/('scientific-verification.json' if mode=='scientific' else 'manifest-verification.json')).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out));assert not bad
