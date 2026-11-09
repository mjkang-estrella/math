from pathlib import Path
import json,hashlib,zipfile
r=Path(__file__).resolve().parents[1]
files=sorted(list((r/'formal').glob('*.lean'))+[r/x for x in ['replay.py','scripts/capped.py','modules.json','audit-modules.json','closure.json','negative-controls.json','REPRODUCE.md','statement-correspondence.md','source-fixes.json','inherited-identity.json']])
manifest={str(p.relative_to(r)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
(r/'source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
files.append(r/'source-manifest.json')
p=r/'nut-r7q-source.zip'
with zipfile.ZipFile(p,'w',zipfile.ZIP_DEFLATED) as z:
 for f in files:z.write(f,str(f.relative_to(r)))
(r/'nut-r7q-source.zip.sha256').write_text(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.name+'\n')
print(len(files),'source-only packet files')
