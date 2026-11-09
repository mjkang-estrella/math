import hashlib, json
from pathlib import Path

L = Path(__file__).resolve().parent
B = L.parent
inputs = {
    'r314-dispositions.json': B/'pi-mathdb-primary-first-breadth-r314/dispositions.json',
    'r314-proposals.json': B/'pi-mathdb-primary-first-breadth-r314/proposals.json',
    'r314-manifest.json': B/'pi-mathdb-primary-first-breadth-r314/manifest.json',
    'r314-receipt.json': B/'pi-mathdb-primary-first-breadth-r314/verification-receipt.json',
    'r314-bindings.json': B/'pi-mathdb-primary-first-breadth-r314/source-bindings.json',
    'r314-summary.md': B/'pi-mathdb-primary-first-breadth-r314/SUMMARY.md',
    'r314-verify.py': B/'pi-mathdb-primary-first-breadth-r314/verify.py',
    'r315-coverage.json': B/'root-mathdb-coverage-merge-r315/coverage-delta.json',
    'r311-reserved.json': B/'root-mathdb-inventory-intake-r311/next-breadth-ids.json',
}

def sha(data):
    return hashlib.sha256(data).hexdigest()

if __name__ == '__main__':
    (L/'frozen').mkdir(exist_ok=True)
    bindings = []
    for name, source in inputs.items():
        data = source.read_bytes()
        dest = L/'frozen'/name
        if dest.exists():
            assert dest.read_bytes() == data, name
        else:
            dest.write_bytes(data)
        bindings.append({'source': str(source), 'copy': str(dest.relative_to(L)), 'sha256': sha(data)})
    (L/'bindings.json').write_text(json.dumps(bindings, indent=2)+'\n')
    for name in ['r314-dispositions.json','r314-manifest.json','r315-coverage.json','r311-reserved.json']:
        obj=json.loads((L/'frozen'/name).read_text())
        print(name, 'keys', list(obj)[:15] if isinstance(obj,dict) else 'list', 'sample', str(obj)[:1300])
    for name in ['r314-receipt.json','r314-bindings.json','r314-verify.py']:
        print(name, (L/'frozen'/name).read_text()[:13000])
