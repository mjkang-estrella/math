"""Retrieve only the immutable source files listed in the checked manifest."""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from urllib.request import urlopen
import hashlib
import json

ROOT = Path(__file__).resolve().parent / 'evidence'
manifest = json.loads((ROOT / 'upstream-manifest.json').read_text())

def fetch(row):
    path = ROOT / 'upstream' / row['path']
    data = path.read_bytes() if path.exists() else urlopen(row['url'], timeout=60).read()
    assert hashlib.sha256(data).hexdigest() == row['sha256'], row['path']
    assert hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == row['git_blob'], row['path']
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)
    return row['path']

if __name__ == '__main__':
    with ThreadPoolExecutor(max_workers=6) as pool:
        result = list(pool.map(fetch, manifest['files']))
    print(f'Verified {len(result)} pinned files against SHA-256 and Git-blob hashes.')
