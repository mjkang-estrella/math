from pathlib import Path
from zipfile import ZipFile
import sys
root=Path(__file__).resolve().parent.parent
dest=root/sys.argv[1]
assert dest.parent.resolve()==root and not dest.exists()
expected={f'{m}.lean' for m in (root/'module-order.txt').read_text().splitlines()}|{'module-order.txt'}
with ZipFile(root/'proof-source.zip') as z:
    assert set(z.namelist())==expected and len(z.namelist())==len(expected)
    assert sum(i.file_size for i in z.infolist())<1000000
    dest.mkdir()
    for info in z.infolist():
        data=z.read(info)
        assert data==(root/('module-order.txt' if info.filename=='module-order.txt' else 'src/'+info.filename)).read_bytes()
        (dest/info.filename).write_bytes(data)
print('Fresh source-only extraction verified:',dest)
