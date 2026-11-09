from pathlib import Path
import json,hashlib,zipfile
r=Path(__file__).resolve().parent.parent
excluded={'MANIFEST.sha256','MANIFEST.json','ARCHIVES.sha256','middle-dossier.zip','receipts/package.json'}
files=[p for p in sorted(r.rglob('*')) if p.is_file() and str(p.relative_to(r)) not in excluded and p.relative_to(r).parts[0] not in {'cache','tmp','safe-extraction'}]
manifest={str(p.relative_to(r)): {'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size} for p in files}
(r/'MANIFEST.json').write_text(json.dumps({'algorithm':'SHA-256','excluded':['MANIFEST.json','MANIFEST.sha256','ARCHIVES.sha256','middle-dossier.zip','receipts/package.json','cache/','tmp/','safe-extraction/'],'files':manifest},indent=2)+'\n')
(r/'MANIFEST.sha256').write_text(''.join(v['sha256']+'  '+k+'\n' for k,v in manifest.items()))
with zipfile.ZipFile(r/'middle-dossier.zip','w',compression=zipfile.ZIP_DEFLATED,compresslevel=6) as z:
 for p in files+[r/'MANIFEST.json',r/'MANIFEST.sha256']:
  z.write(p,str(p.relative_to(r)))
with zipfile.ZipFile(r/'middle-dossier.zip') as z:
 assert set(z.namelist())==set(manifest)|{'MANIFEST.json','MANIFEST.sha256'}
 assert z.testzip() is None
 for n,v in manifest.items(): assert hashlib.sha256(z.read(n)).hexdigest()==v['sha256'],n
(r/'ARCHIVES.sha256').write_text(''.join(hashlib.sha256((r/n).read_bytes()).hexdigest()+'  '+n+'\n' for n in ['middle-source.zip','middle-dossier.zip']))
print('Full dossier ZIP verified:',len(manifest),'payload files,', (r/'middle-dossier.zip').stat().st_size,'bytes')
print((r/'ARCHIVES.sha256').read_text())
