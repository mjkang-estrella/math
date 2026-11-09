from pathlib import Path
import json,hashlib,zipfile
D=Path(__file__).resolve().parents[1]
names=['PROOF.md','REPRODUCE.md','paper-source.json','build_paper.py','replay.py','safe_extract.py','diagnostic.py','pins.json','tools/certificate.py','tools/capped.py','raw/378395.jsonl','receipts/minor-certificate.json']+[str(p.relative_to(D)) for p in sorted((D/'proof').glob('*.lean'))]
m={n:hashlib.sha256((D/n).read_bytes()).hexdigest() for n in names}
(D/'source-manifest.json').write_text(json.dumps(m,indent=2))
with zipfile.ZipFile(D/'source-only-proof.zip','w',zipfile.ZIP_DEFLATED) as z:
 for n in sorted(names+['source-manifest.json']):z.write(D/n,n)
print('Source archive ready',len(names))
