from pathlib import Path
import hashlib,json,tarfile,gzip,io,shutil
L=Path(__file__).resolve().parent
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
mods=json.loads((L/'checked-modules.json').read_text())
order=[];seen=set()
def visit(m):
 if m in seen:return
 seen.add(m)
 for line in (L/(m.replace('.','/')+'.lean')).read_text().splitlines():
  if line.startswith('import '):
   for dep in line[7:].split():
    if dep in mods:visit(dep)
 order.append(m)
for m in mods:visit(m)
(L/'replay-modules.json').write_text(json.dumps(order,indent=2)+'\n')
replay='''#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
G=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py
mkdir -p logs
'''
for m in order+json.loads((L/'audit-modules.json').read_text()):
 f=m.replace('.','/');replay+=f'python "$G" python lean_guard.py logs/{m}.log -o {f}.olean {f}.lean >logs/{m}.console 2>&1\necho {m} OK\n'
(L/'replay.sh').write_text(replay)
# Replay archive contains current code only; immutable scientific references stay
# in freeze.json instead of recursively embedding predecessor evidence archives.
files=[p for p in L.glob('*.lean') if not p.name.startswith('attempt')]+list((L/'generated').glob('*.lean'))+list((L/'parts').glob('*.lean'))
files += [L/s for s in ['lean_guard.py','pins.json','replay-modules.json','replay.sh','freeze.json','assembly-inventory.json','assembly-modules.json','assemble.py','status.py','checked-modules.json','audit-modules.json']]
files=list(set(files+list(L.glob('*.py'))+list(L.glob('*.sh'))+list(L.glob('*.md'))))
with (L/'source-only.tar.gz').open('wb') as raw:
 with gzip.GzipFile(filename='',fileobj=raw,mode='wb',mtime=0) as gz:
  with tarfile.open(fileobj=gz,mode='w') as tar:
   for p in sorted(files):
    info=tar.gettarinfo(str(p),str(p.relative_to(L)));info.uid=info.gid=0;info.uname=info.gname='';info.mtime=0;info.mode=0o644
    with p.open('rb') as f:tar.addfile(info,f)
dest=L/'fresh-replay';dest.mkdir(exist_ok=True)
with tarfile.open(L/'source-only.tar.gz') as tar:tar.extractall(dest,filter='data')
(L/'archive-receipt.json').write_text(json.dumps(dict(sha256=sha(L/'source-only.tar.gz'),files=len(files),modules=len(order),own_compiled_artifacts=False),indent=2)+'\n')
print('archive modules',len(order))
