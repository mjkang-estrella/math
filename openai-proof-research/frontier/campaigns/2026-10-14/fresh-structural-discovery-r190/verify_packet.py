"""Read-only artifact verification; explicit detached anchors are mandatory.
No mathematical correctness/contribution conclusion is made.
"""
import argparse, hashlib, json
from pathlib import Path, PurePosixPath


def digest(b):
    return hashlib.sha256(b).hexdigest()


def verify(root, anchors):
    for name, expected in anchors.items():
        assert len(expected) == 64 and all(c in '0123456789abcdef' for c in expected)
        assert digest((root / name).read_bytes()) == expected, 'detached anchor mismatch: ' + name
    manifest = json.loads((root / 'private/MANIFEST.json').read_bytes())
    seen = set()
    for row in manifest['files']:
        rel = PurePosixPath(row['path'])
        assert not rel.is_absolute() and '..' not in rel.parts
        assert row['path'] not in seen
        seen.add(row['path'])
        path = root / rel
        assert not path.is_symlink() and path.resolve().is_relative_to(root.resolve())
        b = path.read_bytes()
        assert len(b) == row['bytes'] and digest(b) == row['sha256'], 'payload mismatch: ' + str(rel)
    return len(seen)


def originals(root, project):
    # Only explicit direct paths and exact recorded original section spans.
    for name in ['direct-extents.json', 'original-extents.json']:
        for row in json.loads((root / 'private' / name).read_bytes()):
            with (project / row['path']).open('rb') as stream:
                stream.seek(row['start']); b = stream.read(row['end'] - row['start'])
            assert digest(b) == row['sha256'], 'original span changed: ' + row['path']
            assert b == (root / row['copy']).read_bytes()
    for row in json.loads((root / 'private/completed-auth.json').read_bytes()):
        b = (project / row['path']).read_bytes()
        assert len(b) == row['bytes'] and digest(b) == row['sha256']
    brief = project / 'frontier/campaigns/2026-10-14/expanded-target-2026-10-17/fresh-structural-r190-brief.txt'
    assert digest(brief.read_bytes()) == 'e51a54e850412d33f134c84871c8ab86123d48a2d0dcf8d11a85af0a43e55d9a'
    tree_bytes = (project / 'sources/preprints-tree.json').read_bytes()
    assert len(tree_bytes) == 4858136
    assert digest(tree_bytes) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree = json.loads(tree_bytes)['tree']; assert len(tree) == 13223
    prefix = 'preprints/cyclic-length-and-chromatic-fixed-point-loss-september-24-2026/'
    blobs = {e['path']:e for e in tree if e['path'].casefold().startswith(prefix) and e['type']=='blob'}
    rows = json.loads((root / 'private/source-auth.json').read_bytes())
    assert len(rows) == 13 and {e['path'] for e in rows} == set(blobs)
    for row in rows:
        b = (root / row['local']).read_bytes(); meta = blobs[row['path']]
        assert len(b) == meta['size'] == row['bytes']
        assert digest(b) == row['sha256']
        assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest() == meta['sha'] == row['git_blob']
    for row in json.loads((root / 'private/primary-extents.json').read_bytes()):
        with (root / row['local']).open('rb') as stream:
            stream.seek(row['start']); b = stream.read(row['end']-row['start'])
        assert digest(b) == row['sha256']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', required=True)
    parser.add_argument('--final-sha256', required=True)
    parser.add_argument('--manifest-sha256', required=True)
    parser.add_argument('--report-sha256', required=True)
    parser.add_argument('--originals', help='actual project root, for direct read-only bindings')
    args = parser.parse_args(); root = Path(args.root)
    n = verify(root, {'FINAL.md':args.final_sha256,'private/MANIFEST.json':args.manifest_sha256,'REPORT.md':args.report_sha256})
    if args.originals: originals(root,Path(args.originals))
    print(json.dumps({'artifact_verification':'matched','payload_files':n,'originals_checked':bool(args.originals),'mathematical_gate':False}))

if __name__ == '__main__': main()
