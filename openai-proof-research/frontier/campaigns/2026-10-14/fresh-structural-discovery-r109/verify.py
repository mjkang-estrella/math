#!/usr/bin/env python3
"""Read-only integrity verifier. A detached manifest hash is mandatory.

This verifies bytes and source identity, never mathematical truth or eligibility.
It creates no files, runs no network requests, and does not execute packet code.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys

PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def safe_path(base, rel):
    p = Path(rel)
    require(not p.is_absolute() and '..' not in p.parts and rel not in ('', '.'),
            'unsafe relative path: '+rel)
    target = base / p
    for part in (target, *target.parents):
        if part == base.parent:
            break
        require(not part.is_symlink(), 'symlink forbidden: '+str(part))
    return target


def verify(root, repo, expected):
    raw = (root/'manifest.json').read_bytes()
    require(len(expected)==64 and all(c in '0123456789abcdef' for c in expected),
            'expected hash must be 64 lowercase hexadecimal characters')
    require(digest(raw)==expected, 'detached manifest anchor mismatch')
    manifest = json.loads(raw)
    require(manifest['revision']==PIN, 'wrong pinned revision')
    require(manifest['claim_status']=='AUTHOR_FULL_PROOF_UNREVIEWED', 'wrong claim status')
    require(manifest['accepted'] is False and manifest['count_change']==0, 'count/gate guard')
    require(manifest['independent_proof_gate'] is None and
            manifest['independent_contribution_gate'] is None, 'independent gate guard')
    records = manifest['files']
    require(len({x['path'] for x in records})==len(records), 'duplicate manifest path')
    expected_files = {x['path'] for x in records} | {'manifest.json'}
    actual_files, actual_dirs = set(), set()
    for item in root.rglob('*'):
        rel = item.relative_to(root).as_posix()
        require(not item.is_symlink(), 'symlink forbidden: '+rel)
        if item.is_file():
            actual_files.add(rel)
        elif item.is_dir():
            actual_dirs.add(rel)
        else:
            raise ValueError('nonregular entry: '+rel)
    require(actual_files==expected_files,
            'exact file membership mismatch: '+str(sorted(actual_files^expected_files)))
    expected_dirs = set()
    for rel in expected_files:
        expected_dirs.update(p.as_posix() for p in Path(rel).parents if p != Path('.'))
    require(actual_dirs==expected_dirs, 'exact directory membership mismatch')
    total_bytes = 0
    for record in records:
        data = safe_path(root,record['path']).read_bytes()
        require(len(data)==record['bytes'], 'size mismatch: '+record['path'])
        require(digest(data)==record['sha256'], 'SHA256 mismatch: '+record['path'])
        total_bytes += len(data)
    anchors = manifest['external_anchors']
    for anchor in anchors:
        data = safe_path(repo,anchor['path']).read_bytes()
        require(len(data)==anchor['bytes'] and digest(data)==anchor['sha256'],
                'external context anchor mismatch: '+anchor['path'])
    upstream = json.loads((repo/'sources/upstream.json').read_text())
    require(upstream['commit']==PIN, 'upstream pin mismatch')
    tree = json.loads((repo/'sources/preprints-tree.json').read_text())
    require(tree['truncated'] is False and len(tree['tree'])==13223, 'incomplete tree')
    require(sum(x['type']=='blob' for x in tree['tree'])==10373, 'wrong tree blob count')
    paths = {x['path']:x for x in tree['tree']}
    receipts = json.loads((root/'upstream-receipts.json').read_text())
    require(len(receipts)==92, 'wrong retained source count')
    for receipt in receipts:
        path = receipt['path']
        data = safe_path(root,receipt['local']).read_bytes()
        blob = hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        require(paths[path]['type']=='blob' and paths[path]['sha']==blob==receipt['git_blob'],
                'complete-tree Git blob mismatch: '+path)
        require(len(data)==receipt['bytes'] and digest(data)==receipt['sha256'],
                'source receipt SHA256/size mismatch: '+path)
        require(receipt['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+path,
                'unpinned raw source URL: '+path)
    primary = json.loads((root/'primary-receipts.json').read_text())
    for receipt in primary:
        data = safe_path(root,'private/primary/'+receipt['name']).read_bytes()
        txt = safe_path(root,'private/primary/'+Path(receipt['name']).with_suffix('.txt').name).read_bytes()
        require(len(data)==receipt['bytes'] and digest(data)==receipt['sha256'], 'primary PDF mismatch')
        require(digest(txt)==receipt['text_sha256'], 'primary text mismatch')
    freeze = json.loads((root/'scope-freeze.json').read_text())
    require(freeze['scope_sha256']==digest((root/'public/scope.md').read_bytes()), 'frozen scope changed')
    require(freeze['model']=='gpt-6-astra' and freeze['reasoningEffort']=='high' and
            freeze['serviceTier']=='default', 'recorded runtime requirement mismatch')
    return {'status':'INTEGRITY_ONLY_VERIFIED','manifest_sha256':expected,
            'manifested_files':len(records),'manifested_bytes':total_bytes,
            'external_anchors':len(anchors),'source_blobs':len(receipts),
            'primary_pdfs':len(primary),'tree_entries':len(tree['tree']),
            'mathematical_verdict':None,'contribution_verdict':None,'count_change':0}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--expected-sha256',required=True)
    parser.add_argument('--repo-root',type=Path)
    args = parser.parse_args()
    root = Path(__file__).absolute().parent
    repo = args.repo_root.absolute() if args.repo_root else root.parents[3]
    try:
        result = verify(root,repo,args.expected_sha256)
    except (OSError,ValueError,KeyError,TypeError) as error:
        print(json.dumps({'status':'INTEGRITY_REJECTED','reason':str(error)}),file=sys.stderr)
        return 1
    print(json.dumps(result,indent=2,sort_keys=True))
    return 0


if __name__=='__main__':
    raise SystemExit(main())
