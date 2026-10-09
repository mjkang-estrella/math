#!/usr/bin/env python3
"""Seal or verify this handoff; verification makes no writes or network requests."""
import argparse, hashlib, json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[3]
SOURCE=ROOT/'frontier/sources/i15_odd_order_topology_resumed'
EXPERIMENT=ROOT/'frontier/experiments/i15_odd_order_topology_resumed'
REPORT=ROOT/'frontier/iterations/i15-odd-order-topology-resumed.md'
MANIFEST=SOURCE/'artifact-manifest.json'

def record(p):
    assert p.is_file() and not p.is_symlink(), str(p)
    b=p.read_bytes()
    return dict(path=str(p.relative_to(ROOT)),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())

def artifacts():
    paths=[REPORT]+[p for d in (SOURCE,EXPERIMENT) for p in d.rglob('*') if p.is_file() and p!=MANIFEST]
    return [record(p) for p in sorted(paths)]

def dependencies():
    snapshot=json.loads((SOURCE/'inputs/frontier/iterations/pause-at-four-artifact-snapshot.json').read_text())
    rows=sorted((r for r in snapshot['files'] if 'i15' in r['path']),key=lambda r:r['path'])
    for r in rows:
        assert record(ROOT/r['path'])==r, 'Changed old dependency: '+r['path']
    old_paths={str(p.relative_to(ROOT)) for d in [ROOT/'frontier/sources/i15_odd_order_topology',ROOT/'frontier/experiments/i15_odd_order_topology'] for p in d.rglob('*') if p.is_file()}
    old_paths.add('frontier/iterations/i15-odd-order-topology.md')
    assert old_paths=={r['path'] for r in rows}, 'Old inventory changed'
    return rows

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    group=parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--create',action='store_true')
    group.add_argument('--verify',action='store_true')
    args=parser.parse_args()
    current=dict(schema=1,scope='Resumed author handoff; integrity is not independent proof acceptance',files=artifacts(),old_dependencies=dependencies())
    if args.create:
        MANIFEST.write_text(json.dumps(current,indent=2)+'\n')
    else:
        assert json.loads(MANIFEST.read_text())==current, 'Seal mismatch: changed, missing or unlisted artifact'
    print(json.dumps(dict(status='SEALED' if args.create else 'VERIFIED',resumed_artifacts=len(current['files']),old_dependencies=len(current['old_dependencies']),report_sha256=record(REPORT)['sha256'])))

if __name__=='__main__':
    main()
