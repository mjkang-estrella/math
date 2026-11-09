from pathlib import Path
import json,hashlib,zipfile,shutil
r=Path(__file__).resolve().parent
files=list((r/'formal').glob('*.lean'))+list((r/'negative').glob('*.lean'))+list((r/'tools').glob('*.py'))+[r/p for p in ['replay.py','modules.json','audit-groups.json']]
manifest={str(p.relative_to(r)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
(r/'source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
with zipfile.ZipFile(r/'xor-magic-r5-source.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in files+[r/'source-manifest.json']:
  z.write(p,str(p.relative_to(r)))
replay=r/'fresh-replay'
assert not replay.exists()
with zipfile.ZipFile(r/'xor-magic-r5-source.zip') as z:
 assert all(not Path(p).is_absolute() and '..' not in Path(p).parts and '.olean' not in p for p in z.namelist())
 z.extractall(replay)
assert all((r/p).read_bytes()==(replay/p).read_bytes() for p in manifest)
print('EXTRACTED_SOURCE_IDENTITY',len(manifest))
