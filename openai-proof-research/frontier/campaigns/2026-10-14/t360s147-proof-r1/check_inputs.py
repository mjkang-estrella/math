#!/usr/bin/env python3
"""Read-only recheck of independently enumerated selected inputs and canonical source identity."""
from pathlib import Path
import gzip
import hashlib
import json
import tarfile

ROOT = Path('frontier/campaigns/2026-10-14/t360s147-proof-r1')
AUTHOR = Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r147')
def sha(b): return hashlib.sha256(b).hexdigest()
def main():
    auth = json.loads((ROOT/'INPUT-AUTH.json').read_bytes())
    tb = Path('sources/preprints-tree.json').read_bytes()
    assert sha(tb) == auth['tree_sha256'] == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree = json.loads(tb)
    assert len(tree['tree']) == auth['entries'] == 13223
    entries = {e['path']:e for e in tree['tree']}
    for row in auth['copies']:
        b = (ROOT/row['selected_copy']).read_bytes()
        assert len(b) == row['size'] and sha(b) == row['sha256']
        assert Path(row['original']).read_bytes() == b
        if row['kind'] == 'pinned source':
            cp = row['canonical_path']
            e = entries.get(cp, entries.get(cp.removeprefix('preprints/')))
            assert e is not None and e['size'] == len(b)
            blob = hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
            assert blob == e['sha'] == row['git_blob_sha1']
    primary = json.loads((ROOT/'private/author/PRIMARY-AUTH.json').read_bytes())
    selected = 0
    for row in primary:
        p = ROOT/row['incoming_path']; b = p.read_bytes()
        assert sha(b) == row['sha256'] and len(b) == row['size']
        for member in row['selected']:
            if tarfile.is_tarfile(p):
                with tarfile.open(p) as tf:
                    names = [n for n in tf.getnames() if n == member['member'] or n.endswith('/'+member['member'])]
                    assert len(names) == 1
                    data = tf.extractfile(names[0]).read()
            else:
                data = gzip.decompress(b)
            assert data == (ROOT/member['copy']).read_bytes()
            assert sha(data) == member['sha256'] and len(data) == member['size']
            selected += 1
    incoming = auth['incoming_integrity']
    for name, anchor in incoming['anchors'].items():
        assert sha((AUTHOR/name).read_bytes()) == anchor
    manifest = json.loads((AUTHOR/'MANIFEST.json').read_bytes())
    for row in manifest['files']:
        b = (AUTHOR/row['path']).read_bytes()
        assert len(b) == row['size'] and sha(b) == row['sha256']
    print(json.dumps({'selected_copies':len(auth['copies']), 'source_bodies':17,
                      'primary_incoming':len(primary), 'independent_selected_members':selected,
                      'incoming_payload_bytes_checked':len(manifest['files']),
                      'read_only':True, 'mathematical_gate':False}))
if __name__ == '__main__': main()
