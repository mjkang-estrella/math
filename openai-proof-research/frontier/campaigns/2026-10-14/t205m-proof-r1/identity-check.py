#!/usr/bin/env python3
"""MIT. Read-only reviewer identity check of the T205M author packet.

Usage: identity-check.py AUTHOR_PACKET_DIR CANONICAL_PREPRINTS_TREE_JSON
Checks the externally dispatched anchors, then compares every selected source
copy's Git blob id with the separately anchored canonical tree (not the
author's private copy), and lists every canonical entry in both families.
"""
import hashlib, json, sys
from pathlib import Path

ANCHORS = {
    'manifest.json': '29ab2fdb5cf45be3a9a1d36742e5b730a756ee27459fb0d900764d3c14d41db9',
    'verify.py': '5b27e887a79adc22c0c00fc1fa730eabd6fac0a249aec9df24083691f0e8bf1f',
    'candidate205m.md': '17b2b35c42ef10fd0600e0a7b4b5897f0b80cd57cfb1e12587b722294a3e20c5',
    'scope205m.md': '3eb9d790999b419a4083ead2a3ed0979217a36a12bdd78ceabe7fa6d3afb64f6',
    'source-and-credit.md': 'fe5d374d77c5140afda55bb5bfe7aba2393cbed0b8da3ef2fd80c613b1da5e2c',
    'kostka-low-capacity-proof.md': 'd8e029e92d03e946687c4601b6e92afdc6cad8607c2bf564b95af0a2a6ed6ea8',
    'provenance/parent-high-capacity.md': 'fc155c9ac03d70b8a68f501541daf0fb5c02bf9caf6734f61757065a6e796430',
    'finite-proof-certificate.json': '5ffb18808a16add627497b29c82ee389187ad8f4d6df0f6fa52cc6ab49d99263',
}
TREE = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
FAMILIES = ['preprints/A-Cyclic-Polytabloid-Proof-of-Saxls-Conjecture-September-24-2026',
            'preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026']


def sha(b):
    return hashlib.sha256(b).hexdigest()


def main(packet, tree_path):
    packet = Path(packet); out = {'anchors': {}}
    for rel, want in ANCHORS.items():
        got = sha((packet / rel).read_bytes())
        assert got == want, rel
        out['anchors'][rel] = got
    raw = Path(tree_path).read_bytes()
    assert sha(raw) == TREE
    tree = json.loads(raw)
    assert tree['truncated'] is False and len(tree['tree']) == 13223
    manifest = json.loads((packet / 'manifest.json').read_bytes())
    fam = [e for e in tree['tree'] if any(e['path'].startswith(f + '/') for f in FAMILIES)]
    by = {e['path']: e for e in fam}
    rec = json.loads((packet / 'source205-receipts.json').read_bytes())
    rows = []
    for r in rec:
        assert r['path'] in manifest['files']
        b = (packet / r['path']).read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
        assert by[r['source_path']]['sha'] == blob, r['source_path']
        rows.append({'source_path': r['source_path'], 'bytes': len(b), 'git_blob': blob})
    wanted = sorted(e['path'] for e in fam if e['type'] == 'blob' and (e['path'].endswith('.tex') or e['path'].endswith('/README.md')))
    assert sorted(r['source_path'] for r in rows) == wanted
    out.update({'canonical_tree_sha256': TREE, 'canonical_tree_entries': len(tree['tree']),
                'family_entries': len(fam), 'family_blob_paths_not_selected': sorted(e['path'] for e in fam if e['type'] == 'blob' and e['path'] not in wanted),
                'selected_sources_matching_canonical_blobs': rows,
                'manifest_files': len(manifest['files']), 'manifest_directories': len(manifest['directories'])})
    print(json.dumps(out, indent=1, sort_keys=True))


if __name__ == '__main__':
    main(*sys.argv[1:3])
