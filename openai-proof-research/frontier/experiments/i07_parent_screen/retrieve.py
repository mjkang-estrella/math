"""Fetch selected pinned interfaces for the independent probability/quantum screen."""
from concurrent.futures import ThreadPoolExecutor
from hashlib import sha1, sha256
import json
from pathlib import Path
from urllib.request import urlopen

ROOT = Path(__file__).resolve().parents[3]
OUT = ROOT / 'frontier/sources/i07_parent_screen'
PIN = json.loads((ROOT / 'sources/upstream.json').read_text())['commit']
TREE = json.loads((ROOT / 'sources/preprints-tree.json').read_text())
assert not TREE['truncated']
families = (
    'A-Capacity-Criterion-for-Four-State-Potts',
    'The-exact-reconstruction-threshold-for-the-three-state',
    'The-entropy-photon-number-inequality',
    'Classical-capacity-and-entropy-inequalities-for-generalized-amplitude',
)
selected = [x for x in TREE['tree'] if any(f in x['path'] for f in families)
            and x['path'].endswith('.tex')]
OUT.mkdir(parents=True, exist_ok=True)


def fetch(entry):
    path = entry['path']
    url = f'https://raw.githubusercontent.com/openai/math/{PIN}/{path}'
    data = urlopen(url, timeout=60).read()
    blob = sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
    assert blob == entry['sha'], path
    name = path.replace('/', '__')
    (OUT / name).write_bytes(data)
    return {'file': name, 'pinned_path': path, 'url': url,
            'bytes': len(data), 'sha256': sha256(data).hexdigest(),
            'git_blob': blob}


if __name__ == '__main__':
    with ThreadPoolExecutor(max_workers=6) as pool:
        manifest = list(pool.map(fetch, selected))
    (OUT / 'retrieval-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps({'files': len(manifest), 'pin': PIN, 'all_git_blobs_match': True}))
