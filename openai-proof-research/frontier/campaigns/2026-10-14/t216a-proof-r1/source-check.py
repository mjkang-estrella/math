#!/usr/bin/env python3
# MIT. Reviewer identity checks only; they certify no mathematics.
# Reads the frozen author packet and canonical tree; writes only to a fresh /var/tmp directory.
import hashlib, json, shutil, subprocess, sys, tempfile
from pathlib import Path

REPO = Path(__file__).absolute().parents[4]
PACKET = REPO / 'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r49'
PARENT = REPO / 'frontier/campaigns/2026-10-14/t216a-parent/continuum-boundary-pressure.md'
TREE = REPO / 'sources/preprints-tree.json'
TREE_SHA256 = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
ANCHORS = {
    'manifest.json': '14f72cc77fd6ac2facbf0b95391d9429629ca5f07215ee8e3f4265d9ec7f0e79',
    'verify.py': '1eeddb3c315cf9e2a98954a8b7bac5f0e17334512a2be212a57d1d3a339152eb',
    'README.md': '2dae4164cb34882cc2aa179f96906eec99ad2123d5e35af4ba497b2a0ed482ce',
    'original-scope.txt': '923b6386840979b177b9053811fc3a30cd3f9196519c7d860e2c26835127c746',
    'lattice-interface.md': '09f9991e89c75ca51167b91edad3d8e9a7115d024360b49036ba492c705e028c',
    'continuum-boundary-pressure.md': '06ae2006375cb4dc4e2fae84e5a4165dbcaf06c06fcf54be4e36d47c566c78c7',
    'amplitude-assembly.md': 'e794dc340ab0ef0ef8db09223928e078d724c10274de999d72daf910dfa67212',
    'contribution.md': 'c3ca414129acddd3e98ed8499a6d6aa1f8e97cfb3f9781f91d189b2e68555f99',
}
REPLAYED = ['abjj', 'mmp1978', 'sidak1967', 'jsw', 'ginibre1970', 'newmanwu2019']


def sha256(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    out = {'identity_only': True}
    if sha256(TREE) != TREE_SHA256:
        raise SystemExit('REJECT: canonical tree hash')
    tree = json.loads(TREE.read_text())
    assert tree['truncated'] is False
    out['canonical_tree_entries'] = len(tree['tree'])
    blobs = {r['path']: r['sha'] for r in tree['tree'] if r['type'] == 'blob'}
    private = PACKET / 'private'
    matched = []
    for p in sorted((private / 'preprints').rglob('*')):
        if p.is_symlink() or not p.is_file():
            if p.is_symlink():
                raise SystemExit('REJECT: link ' + str(p))
            continue
        rel = p.relative_to(private).as_posix()
        b = p.read_bytes()
        g = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
        if blobs.get(rel) != g:
            raise SystemExit('REJECT: blob mismatch ' + rel)
        matched.append(rel)
    out['actual_source_blobs_matched_to_canonical_tree'] = len(matched)
    for name, h in ANCHORS.items():
        if sha256(PACKET / name) != h:
            raise SystemExit('REJECT: anchor ' + name)
    out['author_anchors_matched'] = len(ANCHORS)
    out['parent_continuum_copy_identical'] = sha256(PARENT) == ANCHORS['continuum-boundary-pressure.md']
    if shutil.which('pdftotext'):
        work = Path(tempfile.mkdtemp(prefix='t216a-proof-r1-pdf.', dir='/var/tmp'))
        try:
            rep = {}
            for n in REPLAYED:
                t = work / (n + '.txt')
                subprocess.run(['pdftotext', '-layout', str(private / 'primary' / (n + '.pdf')), str(t)], check=True)
                rep[n] = t.read_bytes() == (private / 'primary' / (n + '.txt')).read_bytes()
            out['pdftotext_layout_replay_identical'] = rep
        finally:
            shutil.rmtree(work)
    print(json.dumps(out, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
