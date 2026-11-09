from pathlib import Path
import json,hashlib,zipfile
D=Path(__file__).resolve().parents[1]
files=[p for x in ['formal','scripts','negative'] for p in (D/x).glob('*') if p.is_file() and p.suffix in ['.lean','.py']]
files+=[D/'replay.py',D/'REPRODUCE.md',D/'statement-correspondence.md',D/'input-hashes-before.json']
h={str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
(D/'source-hashes.json').write_text(json.dumps(h,indent=2)+'\n');files+=[D/'source-hashes.json']
with zipfile.ZipFile(D/'kirchhoff-source-only.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in files:z.write(p,p.relative_to(D))
