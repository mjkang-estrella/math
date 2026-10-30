from pathlib import Path
import hashlib,json,sys,datetime
L=Path(__file__).resolve().parent;R=L.parents[5]
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
mode=sys.argv[1];manifest=json.loads((L/('scientific-freeze.json' if mode=='science' else 'finalmanifest.json')).read_text())
bad=[n for n,v in manifest['records'].items() if not (L/n).is_file() or h(L/n)!=v]
extra=sorted(str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and str(p.relative_to(L)) not in manifest['records'] and str(p.relative_to(L)) not in manifest['exclusions'])
outside=[]
if mode=='science':
 for n,v in json.loads((L/'external-scientific-freeze.json').read_text())['records'].items():
  p=Path(n) if n.startswith('/') else R/n
  if not p.is_file() or h(p)!=v:outside.append(n)
out=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),mode=mode,entries=len(manifest['records']),bad=bad,extra=extra,external_bad=outside,pass_verification=not(bad or extra or outside),exclusions=manifest['exclusions'],stdout_artifacts_created=False)
(L/('scientific-verification.json' if mode=='science' else 'manifest-verification.json')).write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out));assert out['pass_verification']
