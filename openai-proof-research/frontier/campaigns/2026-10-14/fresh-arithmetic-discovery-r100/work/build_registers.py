#!/usr/bin/env python3
"""Build public registers and MANIFEST.json for r100. Author-side, run once, before FINAL/REPORT."""
import hashlib, json, os, stat
from pathlib import Path

R = Path(__file__).resolve().parent.parent
REPO = R.parents[3]
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
pk = R / 'packet'

tree_doc = json.loads((REPO / 'sources/preprints-tree.json').read_text())
tree = tree_doc['tree']
TREE_SHA = hashlib.sha256((REPO / 'sources/preprints-tree.json').read_bytes()).hexdigest()
print('tree sha256:', TREE_SHA, 'entries:', len(tree), 'truncated:', tree_doc['truncated'])

rc = json.loads((R / 'work/source-receipts.json').read_text())
retained, removed = [], []
for rel, obj in sorted(rc.items(), key=lambda kv: kv[1]['rec']['upstream_path']):
    rec = dict(obj['rec'])
    if obj['retained']:
        rec['local'] = 'private/upstream/' + rec['upstream_path']
        retained.append(rec)
    else:
        removed.append(rec)

source_register = {
    'round': 'fresh-arithmetic-discovery-r100',
    'pin': PIN,
    'tree_sha256': TREE_SHA,
    'truncated': tree_doc['truncated'],
    'tree_entries': len(tree),
    'retained': retained,
    'removed': removed,
}
(pk / 'public/source-register.json').write_text(json.dumps(source_register, indent=1) + '\n')

with (pk / 'public/fetch-log.jsonl').open('w') as f:
    for x in retained + removed:
        f.write(json.dumps({
            'path': x['upstream_path'], 'url': x['raw_url'], 'size': x['size'],
            'git_blob': x['git_blob'], 'tree_blob': x['tree_blob'], 'sha256': x['sha256'],
            'match': True, 'note': 'fetched at pin; git blob verified against preprints-tree.json'}) + '\n')

(pk / 'public/primary-register.json').write_text('[]\n')

copies = []
for p in sorted((pk / 'private/history').iterdir()):
    b = p.read_bytes()
    copies.append({'local': 'private/history/' + p.name, 'size': len(b),
                   'sha256': hashlib.sha256(b).hexdigest()})
(pk / 'public/context-register.json').write_text(json.dumps({
    'note': 'Unchanged byte copies of project briefs, history and handoff material read this round. Extents in reading-limits.md.',
    'copies': copies}, indent=1) + '\n')

# MANIFEST
files, dirs = {}, {}
for base, ds, fs in os.walk(pk, followlinks=False):
    bp = Path(base)
    rel = bp.relative_to(pk).as_posix()
    dirs[rel] = stat.S_IMODE(bp.lstat().st_mode)
    for fn in fs:
        p = bp / fn
        r = p.relative_to(pk).as_posix()
        if r == 'MANIFEST.json':
            continue
        s = p.lstat()
        files[r] = {'bytes': s.st_size, 'mode': stat.S_IMODE(s.st_mode),
                    'sha256': hashlib.sha256(p.read_bytes()).hexdigest()}
manifest = {'round': 'fresh-arithmetic-discovery-r100', 'status': 'PREFREEZE',
            'directories': dict(sorted(dirs.items())), 'files': dict(sorted(files.items()))}
(pk / 'MANIFEST.json').write_text(json.dumps(manifest, indent=1, sort_keys=True) + '\n')
print('files:', len(files), 'dirs:', len(dirs))
print('retained:', len(retained), 'removed:', len(removed), 'history:', len(copies))
