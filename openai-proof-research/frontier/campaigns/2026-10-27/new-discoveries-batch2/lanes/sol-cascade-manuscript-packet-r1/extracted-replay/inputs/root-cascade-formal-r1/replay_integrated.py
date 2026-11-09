"""Fresh source-only serial replay of the integrated mathematical modules."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

base = Path(__file__).resolve().parent
source = base / 'formal'
dest = base / 'fresh-integrated-serial-replay'
dest.mkdir(exist_ok=False)
files = {p.stem: p for p in source.glob('*.lean')}
seen = set()
order = []

def visit(name):
    if name in seen:
        return
    seen.add(name)
    for line in files[name].read_text().splitlines():
        if line.startswith('import '):
            for dep in line.split()[1:]:
                if dep in files:
                    visit(dep)
    order.append(name)

for name in sorted(files):
    visit(name)
shutil.copy2(source / 'run_lean.py', dest / 'run_lean.py')
for name in order:
    shutil.copy2(files[name], dest / files[name].name)
records = []
for name in order:
    result = subprocess.run([sys.executable, str(base / 'compile.py'), dest.name,
                             '-j1', '-DautoImplicit=false', '-DwarningAsError=true',
                             '-o', name + '.olean', name + '.lean'])
    records.append({'module': name, 'exit': result.returncode,
                    'sha256': hashlib.sha256(files[name].read_bytes()).hexdigest()})
    (base / 'integrated-serial-replay.json').write_text(json.dumps(records, indent=2) + '\n')
    if result.returncode:
        raise SystemExit(result.returncode)
print('PASS', len(order), 'modules including endpoint audit', flush=True)
