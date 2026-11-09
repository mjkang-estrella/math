"""Read-only artifact verifier; no mathematical certification."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat

DETACHED = {'MANIFEST.json', 'REPORT.md', 'ANCHORS.json'}
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TREE_SHA = 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
FAMILIES = ('preprints/A-Logarithmic-Independence-Bound-for-Clique-Free-Graphs-September-25-2026', 'preprints/Correspondence-Coloring-Graphs-with-a-Forbidden-Clique-October-5-2026')
EXCEPTIONS = (
 'frontier/campaigns/2026-10-14/discovery-arithmetic-r163-sol-parent/assessment.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r163-sol/private/COMPARISON.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r163-sol/WORKLOG.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r163-sol/private/READING-LIMITS.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r163-sol/FINAL.md')

def digest(b):
    return hashlib.sha256(b).hexdigest()

def safe(s):
    assert isinstance(s, str) and s and '\\' not in s and '\x00' not in s
    p = PurePosixPath(s)
    assert not p.is_absolute() and all(x not in ('', '.', '..') for x in s.split('/'))
    assert p.as_posix() == s
    return s

def snapshot(root):
    root = Path(root)
    assert stat.S_ISDIR(root.lstat().st_mode)
    files, dirs = [], [{'path': '.', 'mode': root.lstat().st_mode}]
    for base, ds, fs in os.walk(root, followlinks=False):
        ds.sort(); fs.sort()
        for n in ds:
            p = Path(base)/n
            assert stat.S_ISDIR(p.lstat().st_mode), 'symlink or non-directory'
            dirs.append({'path': safe(p.relative_to(root).as_posix()), 'mode': p.lstat().st_mode})
        for n in fs:
            p = Path(base)/n; rel = safe(p.relative_to(root).as_posix())
            assert stat.S_ISREG(p.lstat().st_mode), 'symlink or non-file'
            if rel in DETACHED:
                continue
            b = p.read_bytes()
            files.append({'path': rel, 'sha256': digest(b), 'bytes': len(b), 'mode': p.lstat().st_mode})
    return {'format': 1, 'detached': sorted(DETACHED), 'files': sorted(files, key=lambda x:x['path']), 'directories': sorted(dirs, key=lambda x:x['path'])}

def payload(root, m):
    assert m.get('format') == 1 and m.get('detached') == sorted(DETACHED)
    for key in ('files', 'directories'):
        ps = [x['path'] for x in m[key]]
        assert ps == sorted(ps) and len(set(ps)) == len(ps), 'order/duplicate'
        for p in ps:
            if key == 'directories' and p == '.':
                continue
            safe(p)
    assert snapshot(root) == m, 'membership/hash/length/full-mode mismatch'

def anchor(root, name, expected):
    assert re.fullmatch('[0-9a-f]{64}', expected), 'bad anchor format'
    assert digest((Path(root)/name).read_bytes()) == expected, name+' anchor mismatch'

def bindings(root, project):
    root, project = Path(root), Path(project)
    b = (root/'private/preprints-tree.json').read_bytes()
    assert digest(b) == TREE_SHA
    t = json.loads(b)
    assert t['truncated'] is False and len(t['tree']) == 13223
    wanted = [e for e in t['tree'] if any(e['path'] == p or e['path'].startswith(p+'/') for p in FAMILIES)]
    src = json.loads((root/'private/SOURCE-BINDINGS.json').read_text())
    assert len(src) == 32 and sum(e['type']=='blob' for e in src) == 24
    assert len({e['path'] for e in src}) == 32
    assert {e['path'] for e in src} == {e['path'] for e in wanted}
    canonical = {e['path']: e for e in wanted}
    for e in src:
        for k, value in canonical[e['path']].items():
            assert e[k] == value, (e['path'], k)
        if e['type'] == 'blob':
            assert e['local'] == 'private/source/'+e['path']
            raw = (root/safe(e['local'])).read_bytes()
            assert len(raw) == e['size'] and digest(raw) == e['sha256']
            assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest() == e['sha']
            assert e['url_raw'] == 'https://raw.githubusercontent.com/openai/math/'+PIN+'/'+e['path']
        else:
            kids = [z for z in src if PurePosixPath(z['path']).parent.as_posix() == e['path']]
            kids.sort(key=lambda z:PurePosixPath(z['path']).name+('/' if z['type']=='tree' else ''))
            raw = b''.join((z['mode'].lstrip('0')+' '+PurePosixPath(z['path']).name).encode()+b'\0'+bytes.fromhex(z['sha']) for z in kids)
            assert hashlib.sha1(b'tree '+str(len(raw)).encode()+b'\0'+raw).hexdigest() == e['sha']
    assert json.loads((root/'private/upstream.json').read_text())['commit'] == PIN
    records = json.loads((root/'private/completed-bindings.json').read_text())
    assert [e['path'] for e in records] == list(EXCEPTIONS)
    for e in records:
        p, q = project/e['path'], root/safe(e['copy'])
        assert stat.S_ISREG(p.lstat().st_mode) and stat.S_ISREG(q.lstat().st_mode)
        assert p.lstat().st_mode == q.lstat().st_mode == e['mode']
        x, y = p.read_bytes(), q.read_bytes()
        assert x == y and len(x) == e['bytes'] and digest(x) == e['sha256']
    return {'source_blobs': 24, 'source_entries': 32, 'exact_completed_pairs': 5}

def verify(root, project, final, manifest, report):
    for name, h in [('FINAL.md', final), ('MANIFEST.json', manifest), ('REPORT.md', report)]:
        anchor(root, name, h)
    m = json.loads((Path(root)/'MANIFEST.json').read_text())
    payload(root, m)
    result = bindings(root, project)
    result.update(status='MATCH', payloads=len(m['files']), bytes=sum(e['bytes'] for e in m['files']), directories=len(m['directories']))
    return result

if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    for name in ('root', 'project', 'final-sha256', 'manifest-sha256', 'report-sha256'):
        ap.add_argument('--'+name, required=True)
    a = ap.parse_args()
    print(json.dumps(verify(a.root, a.project, a.final_sha256, a.manifest_sha256, a.report_sha256), sort_keys=True))
