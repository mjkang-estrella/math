from pathlib import Path
import json,hashlib,zipfile
r=Path(__file__).resolve().parent
files=sorted((r/'formal').glob('*.lean'))+sorted((r/'scripts').glob('*.py'))+[r/'replay.py',r/'modules.json']
manifest={str(p.relative_to(r)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
(r/'source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
with zipfile.ZipFile(r/'nut-r6p-source.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in files+[r/'source-manifest.json',r/'REPRODUCE.md',r/'statement-correspondence.md']:
  z.write(p,str(p.relative_to(r)))
(r/'nut-r6p-source.zip.sha256').write_text(hashlib.sha256((r/'nut-r6p-source.zip').read_bytes()).hexdigest()+'  nut-r6p-source.zip\n')
f=r/'fresh-extracted';f.mkdir(exist_ok=False)
with zipfile.ZipFile(r/'nut-r6p-source.zip') as z:z.extractall(f)
print('source packet extracted',len(files),'source/configuration files')
