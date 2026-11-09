import hashlib,json,tarfile,gzip,io
from pathlib import Path
L=Path(__file__).resolve().parent
names=['BesselRatio.lean','BesselAnalytic.lean','BesselInterfaces.lean','BesselEndpoints.lean','BesselSeriesODE.lean','BesselODE.lean','BesselClosed.lean','Audit.lean','pins.json','run.py','reproduce.sh','helper-run.py','provenance.py','provenance.json','SUMMARY.md','package.py']
names+=sorted(str(p.relative_to(L)) for p in (L/'inputs').iterdir() if p.is_file())
manifest={n:hashlib.sha256((L/n).read_bytes()).hexdigest() for n in names}
(L/'component-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
names+=['component-manifest.json']
with (L/'component.tar.gz').open('wb') as out:
 with gzip.GzipFile(filename='',fileobj=out,mode='wb',mtime=0) as gz:
  with tarfile.open(fileobj=gz,mode='w') as tf:
   for n in sorted(names):
    data=(L/n).read_bytes();info=tarfile.TarInfo(n);info.size=len(data);info.mode=0o444 if n.endswith('.lean') and n in ['BesselRatio.lean','BesselAnalytic.lean','BesselInterfaces.lean'] else 0o644;info.mtime=0
    tf.addfile(info,io.BytesIO(data))
D=L/'fresh-replay';D.mkdir(exist_ok=False)
with tarfile.open(L/'component.tar.gz') as tf:tf.extractall(D,filter='data')
assert not list(D.glob('*.olean'))
assert all(hashlib.sha256((D/n).read_bytes()).hexdigest()==h for n,h in manifest.items())
print('PASS deterministic source-only packet, fresh extraction, payload hashes')
