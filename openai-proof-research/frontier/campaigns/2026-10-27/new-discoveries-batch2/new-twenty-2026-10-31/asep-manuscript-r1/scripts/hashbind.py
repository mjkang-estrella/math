"""Hash-bind the frozen inputs of this lane. Usage: python3 -I hashbind.py OUT.json"""
import hashlib, json, os, sys, datetime
from pathlib import Path
BASE = Path(__file__).resolve().parents[2]  # new-twenty-2026-10-31
INPUTS = ['expanded-corpus-r96', 'asep-review-r1', 'asep-root-adjudication-r1.json']
def sha(p):
    h = hashlib.sha256()
    with open(p, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''):
            h.update(b)
    return h.hexdigest()
files = {}
for root in INPUTS:
    p = BASE / root
    if p.is_file():
        files[root] = sha(p)
        continue
    for dp, dn, fn in os.walk(p):
        dn.sort()
        for n in sorted(fn):
            q = Path(dp) / n
            if q.is_symlink():
                files[str(q.relative_to(BASE))] = 'symlink:' + os.readlink(q)
            else:
                files[str(q.relative_to(BASE))] = sha(q)
agg = hashlib.sha256(''.join(f'{k}\0{v}\n' for k, v in sorted(files.items())).encode()).hexdigest()
out = {'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'base': str(BASE),
       'roots': INPUTS, 'file_count': len(files), 'aggregate_sha256': agg, 'files': files}
Path(sys.argv[1]).write_text(json.dumps(out, indent=1, sort_keys=True))
print(len(files), agg)
