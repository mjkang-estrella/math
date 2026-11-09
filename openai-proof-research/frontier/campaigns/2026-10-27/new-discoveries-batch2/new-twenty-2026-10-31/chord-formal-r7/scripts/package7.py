from pathlib import Path
import zipfile,hashlib
root=Path(__file__).resolve().parent.parent
files=sorted([*root.glob('src/*.lean'),*root.glob('scripts/*.sh'),*root.glob('scripts/*7.py'),*root.glob('controls/*.lean'),*root.glob('*.md'),root/'modules.txt',root/'inherited-before.sha256',root/'inherited-after.sha256',root/'results.json',root/'regression7.json'])
with zipfile.ZipFile(root/'chord7-source.zip','w',zipfile.ZIP_DEFLATED) as z:
    for p in files:
        if p.is_file(): z.write(p,p.relative_to(root))
print(hashlib.sha256((root/'chord7-source.zip').read_bytes()).hexdigest())
