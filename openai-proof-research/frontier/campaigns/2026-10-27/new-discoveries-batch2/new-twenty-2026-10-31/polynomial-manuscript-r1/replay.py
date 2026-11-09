#!/usr/bin/env python3
"""Fresh source-only replay. All writes are confined to a new child of this dossier."""
from pathlib import Path,PurePosixPath
import argparse,hashlib,json,stat,zipfile,subprocess,sys,shutil
sys.dont_write_bytecode=True
R=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--output',required=True);a=ap.parse_args();O=Path(a.output).absolute()
assert O.parent.resolve()==R and not O.exists() and not O.is_symlink(), 'use a fresh direct child of dossier'
with zipfile.ZipFile(R/'proof-source-only.zip') as z:
 assert hashlib.sha256((R/'proof-source-only.zip').read_bytes()).hexdigest()=='859afaf1d4cc7799f6e6559052766bdf0c81ca192d322b93b860ac1704aa5681'
 infos=z.infolist();names=[i.filename for i in infos];assert len(names)==len(set(names)) and sum(i.file_size for i in infos)<2000000
 manifest=json.loads(z.read('manifest.json'));assert set(names)==set(manifest)|{'manifest.json'}
 for i in infos:
  p=PurePosixPath(i.filename);assert not p.is_absolute() and '..' not in p.parts and not i.is_dir() and not stat.S_ISLNK(i.external_attr>>16)
  assert p.suffix not in {'.olean','.ilean','.o','.so'}
  if i.filename in manifest:assert hashlib.sha256(z.read(i)).hexdigest()==manifest[i.filename]
 assert sum(n.endswith('.lean') for n in names)==18
 O.mkdir()
 for i in infos:
  d=O/'replay/extracted'/i.filename;d.parent.mkdir(parents=True,exist_ok=True);d.write_bytes(z.read(i))
for name in ['replay-driver.py','controls.py']:shutil.copyfile(R/name,O/name)
env={'PATH':'/usr/bin:/bin','LANG':'C.UTF-8','PYTHONDONTWRITEBYTECODE':'1'}
for cmd in [[sys.executable,str(O/'replay-driver.py'),str(O/'replay/build')],[sys.executable,str(O/'controls.py')]]:
 p=subprocess.run(cmd,cwd=O,env=env)
 if p.returncode:raise SystemExit(p.returncode)
print('Fresh 18 builds, 18 checks and expanded origin audit complete. See output receipts.')
