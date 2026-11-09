#!/usr/bin/env python3
"""Read-only verifier. Supply detached FINAL, MANIFEST, REPORT SHA256 anchors."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat

ROOT = Path(__file__).resolve().parent
PREFIX = 'preprints/Simulating-One-Tape-Time-in-Two-Fifths-Power-Space-September-25-2026'
ORIGINALS = [
 'frontier/campaigns/2026-10-14/discovery-arithmetic-r162bd-parent/assessment.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bd/private/DERIVATIONS.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bd/private/WORKING.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bd/private/READING-LIMITS.md',
 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bd/FINAL.md',
]

def digest(data):
    return hashlib.sha256(data).hexdigest()

def safe(name):
    assert isinstance(name, str) and name and '\\' not in name
    p = PurePosixPath(name)
    assert not p.is_absolute() and '..' not in p.parts
    assert str(p) == name and name != '.'
    return name

def regular(path):
    st = path.lstat()
    assert stat.S_ISREG(st.st_mode) and not path.is_symlink(), str(path)
    return st

def check_file(root, rec):
    path = root / safe(rec['path'])
    st = regular(path)
    b = path.read_bytes()
    assert len(b) == rec['bytes'], rec['path'] + ': bytes'
    assert digest(b) == rec['sha256'], rec['path'] + ': digest'
    assert stat.S_IMODE(st.st_mode) == rec['mode'], rec['path'] + ': mode'

def inventory(root):
    files, dirs = [], []
    assert not root.is_symlink()
    for base, subdirs, names in os.walk(root, followlinks=False):
        bp = Path(base)
        assert stat.S_ISDIR(bp.lstat().st_mode) and not bp.is_symlink()
        rel = bp.relative_to(root).as_posix()
        dirs.append({'path':rel, 'mode':stat.S_IMODE(bp.lstat().st_mode)})
        for name in subdirs:
            assert not (bp/name).is_symlink()
        for name in names:
            p=bp/name; regular(p)
            files.append(safe(p.relative_to(root).as_posix()))
    return sorted(files), sorted(dirs, key=lambda d:d['path'])

def check_packet(root, manifest):
    assert manifest['format'] == 'r162be-1'
    assert manifest['envelopes'] == ['MANIFEST.json','REPORT.md']
    assert set(manifest['envelope_modes']) == set(manifest['envelopes'])
    for name in manifest['envelopes']:
        assert stat.S_IMODE(regular(root/name).st_mode) == manifest['envelope_modes'][name], name + ': mode'
    recs=manifest['files']; names=[safe(r['path']) for r in recs]
    assert names == sorted(names) and len(names) == len(set(names))
    actual, dirs = inventory(root)
    assert actual == sorted(names + manifest['envelopes']), 'exact membership'
    expected_dirs=manifest['directories']
    dn=[r['path'] for r in expected_dirs]
    assert dn==sorted(dn) and len(dn)==len(set(dn))
    assert expected_dirs == dirs, 'directory membership/modes'
    for rec in recs: check_file(root,rec)
    bindings=json.loads((root/'private/COPY-BINDINGS.json').read_text())
    assert [r['original'] for r in bindings] == ORIGINALS
    project=root.parents[3]
    for rec in bindings:
        original=project/safe(rec['original']); copied=root/safe(rec['copy'])
        so=regular(original); sc=regular(copied)
        b=original.read_bytes()
        assert b==copied.read_bytes() and len(b)==rec['bytes'] and digest(b)==rec['sha256']
        assert stat.S_IMODE(so.st_mode)==rec['original_mode']
        assert stat.S_IMODE(sc.st_mode)==rec['copy_mode']
    selection=json.loads((root/'private/source/tree-selection.json').read_text())
    assert len(selection)==15
    blobs=[e for e in selection if e['type']=='blob']; assert len(blobs)==10
    auth=json.loads((root/'private/source/authentication.json').read_text())
    assert len(auth)==10 and len({e['path'] for e in auth})==10
    bypath={e['path']:e for e in auth}
    for e in selection:
        assert e['path']==PREFIX or e['path'].startswith(PREFIX+'/')
    for e in blobs:
        name=safe(e['path'][len(PREFIX)+1:]); p=root/'private/source'/name
        st=regular(p); b=p.read_bytes(); a=bypath[e['path']]
        assert len(b)==e['size']==a['bytes']
        assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['sha']==a['git_blob']
        assert digest(b)==a['sha256']
        assert stat.S_IMODE(st.st_mode)==(int(e['mode'],8)&0o7777)
        assert a['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
    assert (root/'private/controls/FINAL.copy').read_bytes()==(root/'FINAL.md').read_bytes()
    return {'payload_records':len(recs),'payload_bytes':sum(r['bytes'] for r in recs),
            'whole_root_files':len(actual),'directories_including_root':len(dirs),
            'source_blobs':len(blobs),'exact_completed_copies':len(bindings)}

def verify(root, final_anchor, manifest_anchor, report_anchor):
    for name, anchor in [('FINAL.md',final_anchor),('MANIFEST.json',manifest_anchor),('REPORT.md',report_anchor)]:
        assert len(anchor)==64 and set(anchor)<=set('0123456789abcdef')
        regular(root/name)
        assert digest((root/name).read_bytes())==anchor, name+': detached anchor'
    return check_packet(root,json.loads((root/'MANIFEST.json').read_text()))

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--final',required=True);p.add_argument('--manifest',required=True);p.add_argument('--report',required=True)
    a=p.parse_args()
    print(json.dumps({'artifact_integrity':'MATCH',**verify(ROOT,a.final,a.manifest,a.report)},sort_keys=True))

if __name__=='__main__': main()
