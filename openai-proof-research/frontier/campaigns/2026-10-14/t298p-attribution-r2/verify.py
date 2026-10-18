"""Read-only authored-response identity verifier, with no mathematical verdict."""
import argparse
import hashlib
import json
import stat
from pathlib import Path

p = argparse.ArgumentParser()
p.add_argument('--anchor', required=True)
p.add_argument('--repo', required=True, type=Path)
a = p.parse_args()
r = Path(__file__).resolve().parent
repo = a.repo.resolve()


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def need(ok, reason):
    if not ok:
        raise SystemExit('REJECT: ' + reason)


need(sha(r / 'MANIFEST.json') == a.anchor, 'external manifest anchor')
m = json.loads((r / 'MANIFEST.json').read_bytes())
need({x.name for x in r.iterdir()} == set(m['files']) | {'MANIFEST.json'}, 'exact membership')
for name, h in dict(m['files'], **{'MANIFEST.json': a.anchor}).items():
    need('/' not in name and name not in {'.', '..'}, 'flat safe filename')
    s = (r / name).lstat()
    need(stat.S_ISREG(s.st_mode) and s.st_nlink == 1, 'regular single-link file')
    need(sha(r / name) == h, 'payload ' + name)
d = json.loads((r / 'inputs.json').read_bytes())
need(not d['accepted'] and d['count_change'] == 0 and not d['proof_change']
     and not d['scope_change'] and not d['independent_review'], 'status boundaries')
for name, h in d['anchors'].items():
    path = Path(name)
    need(not path.is_absolute() and '..' not in path.parts, 'safe dependency path')
    need(sha(repo / path) == h, 'dependency ' + name)
print(json.dumps({'status': 'PASS_IDENTITY_ONLY', 'payloads': len(m['files']),
                  'dependency_anchors': len(d['anchors']), 'count_change': 0,
                  'independent_verdict': False}))
