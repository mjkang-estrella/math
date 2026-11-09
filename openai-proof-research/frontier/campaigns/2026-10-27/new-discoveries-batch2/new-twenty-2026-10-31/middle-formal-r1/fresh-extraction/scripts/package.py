from pathlib import Path
import zipfile, hashlib
L=Path(__file__).resolve().parent.parent
files=sorted(L.glob('*.lean'))+sorted((L/'scripts').glob('*'))+[L/n for n in ['PROOF.md','STATEMENT-CORRESPONDENCE.md','REPRODUCE.md']]
with zipfile.ZipFile(L/'middle-source.zip','w',zipfile.ZIP_DEFLATED) as z:
    for p in files:
        assert p.is_file() and p.resolve().is_relative_to(L)
        z.write(p,p.relative_to(L))
dest=L/'fresh-extraction'
dest.mkdir(exist_ok=False)
with zipfile.ZipFile(L/'middle-source.zip') as z:
    for name in z.namelist():
        p=Path(name)
        assert not p.is_absolute() and '..' not in p.parts
    z.extractall(dest)
for p in files:
    assert p.read_bytes()==(dest/p.relative_to(L)).read_bytes()
print('source-only archive safely extracted; all source bytes equal')
