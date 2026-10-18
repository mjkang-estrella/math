"""Read-only attribution identities, not mathematical or contribution verification."""
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
need({x.name for x in r.iterdir()} == set(m['files']) | {'MANIFEST.json', 'private'}, 'exact root membership')
need((r / 'private').is_dir() and not (r / 'private').is_symlink(), 'private directory type')
for name, h in dict(m['files'], **{'MANIFEST.json': a.anchor}).items():
    need('/' not in name and name not in {'.', '..'}, 'flat safe payload name')
    s = (r / name).lstat()
    need(stat.S_ISREG(s.st_mode) and s.st_nlink == 1, 'public regular single-link file')
    need(sha(r / name) == h, 'payload ' + name)
d = json.loads((r / 'inputs.json').read_bytes())
need(d['count_change'] == 0 and not d['proof_change'] and not d['scope_change'] and not d['independent_verdict'], 'status boundaries')
author = repo / d['author_directory']
need(sha(author / 'MANIFEST.json') == d['author_manifest_sha256'], 'author manifest anchor')
need(sha(author / 'scope-freeze.md') == d['scope_sha256'], 'original scope')
t = repo / 'sources/preprints-tree.json'
need(sha(t) == d['tree_sha256'], 'canonical tree anchor')
tree = json.loads(t.read_bytes())
need(len(tree['tree']) == 13223 and not tree.get('truncated', False), 'complete tree')
need(json.loads((repo / 'sources/upstream.json').read_bytes())['commit'] == d['pin'], 'immutable pin')
canonical = {x['path']: x for x in tree['tree']}
for f in d['new_canonical_sources'] + d['existing_author_sources']:
    e = canonical[f['path']]
    need(e['type'] == 'blob' and e['sha'] == f['git_blob'], 'canonical Git membership')
    path = r / f['private_path'] if 'private_path' in f else repo / f['repo_private_path']
    data = path.read_bytes()
    need(hashlib.sha256(data).hexdigest() == f['sha256'], 'source SHA')
    need(hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == f['git_blob'], 'source Git blob')
for f in d['primary_receipts']:
    for field, hfield in [('file', 'sha256'), ('text_file', 'text_sha256')]:
        need(sha(repo / d['primary_private_directory'] / Path(f[field]).name) == f[hfield], 'primary identity')
print(json.dumps({'status': 'PASS_IDENTITY_ONLY', 'public_payloads': len(m['files']), 'new_generator_blobs': 3, 'existing_source298_blobs': 4, 'count_change': 0, 'independent_verdict': False}))
