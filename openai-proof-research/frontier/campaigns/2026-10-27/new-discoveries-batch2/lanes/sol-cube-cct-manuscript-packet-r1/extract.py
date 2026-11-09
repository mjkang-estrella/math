from pathlib import Path
import tarfile
L=Path(__file__).resolve().parent
with tarfile.open(L/'frozen/sol-cube-cct-source-formal-r1/source-only.tar.gz') as t:
 assert all(m.isfile() and not m.name.startswith('/') and '..' not in Path(m.name).parts for m in t.getmembers())
 t.extractall(L/'packet/formal',filter='data')
print('Extracted immutable formal source')
