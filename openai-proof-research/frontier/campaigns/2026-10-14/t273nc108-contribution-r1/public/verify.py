#!/usr/bin/env python3
"""MIT. Offline read-only integrity verifier. Requires a DETACHED manifest digest."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import stat

PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
OWNED = 'frontier/campaigns/2026-10-14/t273nc108-contribution-r1'
AUTHOR = 'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r108'
AUTHOR_MANIFEST = '6778e2c605f6f50275d70f4d27fa14351a11e717ab97942e1facb2d29b77c743'
SCOPE = '837137e682d13cae985a97173e731a79db7418df6221de38df3626bc93275618'
PACKAGE = Path(__file__).absolute().parents[1]
REPO = PACKAGE.parents[3]


def require(value, message):
    if not value:
        raise ValueError(message)


def sha(body):
    return hashlib.sha256(body).hexdigest()


def safe_file(base, relative):
    p = PurePosixPath(relative)
    require(not p.is_absolute() and str(p)==relative and
            all(x not in ('','.','..') for x in p.parts), 'unsafe relative path')
    current=base
    require(not base.is_symlink(), 'base symlink forbidden')
    for part in p.parts:
        current=current/part
        require(not current.is_symlink(), 'symlink forbidden: '+relative)
    require(current.is_file() and stat.S_ISREG(current.stat().st_mode), 'missing/nonregular file: '+relative)
    return current


def inventory(base, omit_manifest=False):
    files, dirs = [], []
    for p in base.rglob('*'):
        require(not p.is_symlink(),'inventory symlink forbidden')
        name=p.relative_to(base).as_posix()
        if p.is_dir():
            dirs.append(name)
        else:
            require(stat.S_ISREG(p.stat().st_mode),'inventory nonregular file')
            if not (omit_manifest and name=='manifest.json'):
                files.append(name)
    return sorted(files),sorted(dirs)


def check_rows(base, rows):
    require(len(rows)==len({r['path'] for r in rows}),'duplicate inventory row')
    for row in rows:
        body=safe_file(base,row['path']).read_bytes()
        require(len(body)==row['bytes'] and sha(body)==row['sha256'], 'bytes/hash mismatch: '+row['path'])


def validate(manifest):
    require(PACKAGE.relative_to(REPO).as_posix()==OWNED,'wrong package layout')
    require(manifest['owned_directory']==OWNED and manifest['revision']==PIN,'root/pin mismatch')
    require(manifest['target']=='T273NC108' and manifest['review_round']==1,'wrong target/round')
    require(manifest['verdict']=='TECHNICAL_CONDITIONAL_ON_CORRECTNESS','verdict mismatch')
    require(manifest['correctness_verdict']=='NOT_ISSUED' and manifest['count_change']==0,'gate/count mismatch')
    files,dirs=inventory(PACKAGE,True)
    require(files==sorted(r['path'] for r in manifest['payloads']) and dirs==manifest['directories'],'review inventory mismatch')
    check_rows(PACKAGE,manifest['payloads'])
    anchors=manifest['external_anchors']
    require(all(not r['path'].startswith(OWNED+'/') for r in anchors),'nonexternal anchor')
    required={'AGENTS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json',AUTHOR+'/manifest.json',AUTHOR+'/public/frozen-target.md'}
    require(required<={r['path'] for r in anchors},'required anchors missing')
    check_rows(REPO,anchors)
    author_manifest=safe_file(REPO,AUTHOR+'/manifest.json').read_bytes()
    require(sha(author_manifest)==AUTHOR_MANIFEST,'author detached seal changed')
    require(sha(safe_file(REPO,AUTHOR+'/public/frozen-target.md').read_bytes())==SCOPE,'original scope changed')
    afiles,adirs=inventory(REPO/AUTHOR)
    baseline=json.loads(safe_file(PACKAGE,'private/author-inventory.json').read_bytes())
    require(afiles==sorted(r['path'] for r in baseline['files']) and adirs==baseline['directories'],'author inventory changed')
    check_rows(REPO/AUTHOR,baseline['files'])
    upstream=json.loads(safe_file(REPO,'sources/upstream.json').read_bytes())
    require(upstream['commit']==PIN,'upstream pin changed')
    tree=json.loads(safe_file(REPO,'sources/preprints-tree.json').read_bytes())
    require(tree['truncated'] is False and len(tree['tree'])==13223,'incomplete inventory')
    entries={r['path']:r for r in tree['tree']}
    require(len(entries)==13223,'duplicate tree entry')
    family='preprints/The-entropy-photon-number-inequality-September-24-2026/'
    actual={p for p,r in entries.items() if r['type']=='blob' and p.startswith(family) and p.endswith('.tex')}
    provenance=json.loads(safe_file(PACKAGE,'private/provenance.json').read_bytes())
    rows=provenance['selected_source_blobs']
    require(len(rows)==9 and actual=={r['upstream_path'] for r in rows},'selected source inventory mismatch')
    for row in rows:
        body=safe_file(REPO,row['path']).read_bytes()
        blob=hashlib.sha1(b'blob '+str(len(body)).encode()+b'\0'+body).hexdigest()
        require(entries[row['upstream_path']]['sha']==row['git_blob']==blob,'pinned blob mismatch')
        require(sha(body)==row['sha256'],'pinned source hash mismatch')
        require(row['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+row['upstream_path'],'unpinned URL')
    ledger=json.loads(safe_file(PACKAGE,'private/reading-ledger.json').read_bytes())
    for row in ledger['readings']:
        body=safe_file(REPO,row['path']).read_bytes()
        require(sha(body)==row['sha256'],'reading anchor changed')
        n=len(body.decode('utf-8').splitlines())
        require(n==row['line_count'],'line count changed')
        for lo,hi in row['semantic_ranges']:
            require(1<=lo<=hi<=n,'invalid reading range')
    return {'status':'INTEGRITY_ONLY','target':'T273NC108','verdict':'TECHNICAL_CONDITIONAL_ON_CORRECTNESS',
            'correctness_verdict':'NOT_ISSUED','count_change':0,'payloads':len(files),'external_anchors':len(anchors),
            'author_files_unchanged':len(afiles),'complete_tree_entries':len(entries),'selected_family_tex':len(rows),
            'meaning':'Evidence integrity only; no mathematics or acceptance is certified.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--expected-sha256',required=True,help='External detached digest, never inferred from the package')
    args=parser.parse_args()
    expected=args.expected_sha256
    body=safe_file(PACKAGE,'manifest.json').read_bytes()
    require(len(expected)==64 and all(c in '0123456789abcdef' for c in expected) and sha(body)==expected,'DETACHED manifest digest mismatch')
    print(json.dumps(validate(json.loads(body)),indent=2,sort_keys=True))


if __name__=='__main__':
    main()
