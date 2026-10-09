"""Verify this round's downloads against the immutable complete preprint tree."""
from pathlib import Path
import hashlib
import json

root = Path(__file__).resolve().parents[3]
out = Path(__file__).resolve().parent
tree = json.loads((root/'sources/preprints-tree.json').read_text())
assert tree['truncated'] is False
entries = {e['path']: e for e in tree['tree']}
manifest = json.loads((out/'manifest.json').read_text())
checks = []
for e in manifest:
    p = root/e['path']
    b = p.read_bytes()
    sha = hashlib.sha256(b).hexdigest()
    assert sha == e['sha256'], str(p)
    row = {'path': e['path'], 'sha256': sha, 'bytes': len(b)}
    if 'upstream_path' in e:
        blob = hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        assert blob == e['git_blob'] == entries[e['upstream_path']]['sha']
        row.update(upstream_path=e['upstream_path'], git_blob=blob, pinned_tree_match=True)
    if 'status' in e:
        row['status'] = e['status']
    checks.append(row)
result = {'pin': 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',
          'complete_tree': True,
          'pinned_files': sum('upstream_path' in e for e in manifest),
          'external_downloads_including_failed_html': sum('upstream_path' not in e for e in manifest),
          'checks': checks, 'failures': 0}
(out/'verification.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k != 'checks'}, indent=2))
