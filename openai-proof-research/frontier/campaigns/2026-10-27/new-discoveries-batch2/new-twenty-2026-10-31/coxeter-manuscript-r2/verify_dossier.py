from pathlib import Path,PurePosixPath
import json,hashlib
w=Path(__file__).resolve().parent
m=json.loads((w/'dossier-manifest.json').read_text())
for name,h in m['files'].items():
 p=PurePosixPath(name);assert not p.is_absolute() and '..' not in p.parts
 assert hashlib.sha256((w/name).read_bytes()).hexdigest()==h,name
for name,h in json.loads((w/'packet-manifest.json').read_text()).items():
 assert hashlib.sha256((w/'proof'/name).read_bytes()).hexdigest()==h,name
assert hashlib.sha256((w/'frozen/330264-replay-fit-r2-source.zip').read_bytes()).hexdigest()=='00c3713935d6a13f701cd3a26f9c7f1a86633e0eb60ff00a7ed0d100ea3d2fb5'
print('PASS dossier manifest, 64 extracted source modules and exact current packet hash')
