from pathlib import Path
import json,hashlib,zipfile,sys
D=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(n,x):(D/n).write_text(json.dumps(x,indent=2)+'\n')
def zipfiles(name,files):
 with zipfile.ZipFile(D/name,'w',zipfile.ZIP_DEFLATED) as z:
  for p in sorted(files):z.write(p,p.relative_to(D))
if sys.argv[1]=='source':
 files=list((D/'formal').glob('*.lean'))+[D/'scripts'/s for s in ['replay.py','check_witness.py','safe_extract.py','build_paper.py']]+[D/s for s in ['REPRODUCE.md','pins.json','PROOF.md','paper.json']]
 dump('source-manifest.json',{str(p.relative_to(D)):sha(p) for p in files})
 zipfiles('source-only.zip',files+[D/'source-manifest.json'])
else:
 exclude={'dossier-manifest.json','full-dossier.zip','archive-hashes.json'}
 files=[p for p in D.rglob('*') if p.is_file() and p.relative_to(D).parts[0] not in ['fresh-replay','vendor','tmp'] and p.name not in exclude and p.suffix not in ['.olean','.ilean'] and '__pycache__' not in p.parts]
 # Preserve fresh replay evidence without duplicating its source files.
 files += [p for p in (D/'fresh-replay/receipts').glob('*') if p.is_file()]
 dump('dossier-manifest.json',{str(p.relative_to(D)):sha(p) for p in sorted(files)})
 zipfiles('full-dossier.zip',files+[D/'dossier-manifest.json'])
 dump('archive-hashes.json',{n:sha(D/n) for n in ['source-only.zip','full-dossier.zip']})
 print('Packaged',len(files),'dossier files')
