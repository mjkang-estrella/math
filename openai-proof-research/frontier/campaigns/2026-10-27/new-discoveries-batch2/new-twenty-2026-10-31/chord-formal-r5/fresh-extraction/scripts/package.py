from pathlib import Path
import zipfile,hashlib
root=Path(__file__).resolve().parent.parent
files=sorted([*root.glob('src/*.lean'),*root.glob('scripts/*'),*root.glob('frozen/*.json'),*root.glob('*.md'),root/'modules.txt',root/'merge.json',root/'results.json'])
with zipfile.ZipFile(root/'chord5-source.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in files:
  if p.is_file(): z.write(p,p.relative_to(root))
print(hashlib.sha256((root/'chord5-source.zip').read_bytes()).hexdigest())
