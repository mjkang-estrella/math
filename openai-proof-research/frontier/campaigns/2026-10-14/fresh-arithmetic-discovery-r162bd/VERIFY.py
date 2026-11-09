#!/usr/bin/env python3
"""Read-only packet verifier. Detached anchors MUST be supplied explicitly."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def safe(name):
    require(isinstance(name, str) and name and '\\' not in name, 'unsafe path')
    p = PurePosixPath(name)
    require(not p.is_absolute() and all(x not in ('', '.', '..') for x in name.split('/')),
            'unsafe path component')
    require(p.as_posix() == name, 'noncanonical path')
    return name


def inventory(root):
    require(root.is_dir() and not root.is_symlink(), 'unsafe root')
    files, dirs = {}, {'': stat.S_IMODE(root.stat().st_mode)}
    def visit(base):
        for ent in os.scandir(base):
            require(not ent.is_symlink(), 'symlink rejected')
            p = Path(ent.path)
            name = safe(p.relative_to(root).as_posix())
            mode = stat.S_IMODE(ent.stat(follow_symlinks=False).st_mode)
            if ent.is_dir(follow_symlinks=False):
                dirs[name] = mode
                visit(p)
            else:
                require(ent.is_file(follow_symlinks=False), 'special file rejected')
                files[name] = mode
    visit(root)
    return files, dirs


def verify_bindings(root):
    meta = json.loads((root/'private/source-metadata.json').read_bytes())
    auth = json.loads((root/'private/source-authentication.json').read_bytes())
    prefix = 'preprints/The-PCP-for-PPAD-conjecture-a-quasilinear-reduction-September-25-2026'
    pin = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
    own = 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bd/'
    require(len(meta) == 19 and len(auth) == 16, 'source cardinality')
    require(len({x['path'] for x in meta}) == 19, 'duplicate source metadata')
    require(len({x['path'] for x in auth}) == 16, 'duplicate source authentication')
    blobs = {x['path']: x for x in meta if x['type'] == 'blob'}
    require(set(blobs) == {x['path'] for x in auth}, 'source blob membership')
    for x in auth:
        name = x['path']
        require(name.startswith(prefix+'/'), 'source prefix')
        rel = safe('private/source/'+name[len(prefix)+1:])
        require(x['local'] == own+rel, 'source local binding')
        require(x['url'] == 'https://raw.githubusercontent.com/openai/math/'+pin+'/'+name,
                'source pinned URL')
        b = (root/rel).read_bytes()
        git = hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        require(len(b) == x['bytes'] == blobs[name]['size'], 'source size')
        require(git == x['git_blob'] == blobs[name]['sha'], 'source Git blob')
        require(sha(b) == x['sha256'], 'source SHA256')
        require(blobs[name]['mode'] == '100644', 'source Git mode')
    copies = json.loads((root/'private/COPY-BINDINGS.json').read_bytes())
    require(copies['compared_before_seal'] is True, 'missing copy comparison')
    rows = copies['copies']
    require(len(rows) == 5 and len({x['original'] for x in rows}) == 5, 'copy cardinality')
    require({x['local'] for x in rows} ==
            {'private/completed-exception-'+str(i)+'.md' for i in range(1,6)}, 'copy membership')
    for x in rows:
        p = root/safe(x['local']); b = p.read_bytes()
        require(len(b) == x['bytes'] and sha(b) == x['sha256'], 'copy bytes')
        require(stat.S_IMODE(p.stat().st_mode) == x['copy_mode'], 'copy mode')
    primary = json.loads((root/'private/primary/access.json').read_bytes())
    require(len(primary) == 6 and len({x['name'] for x in primary}) == 6, 'primary cardinality')
    for x in primary:
        for ext, size, digest in [('pdf',x['bytes'],x['sha256']),
                                  ('txt',x['text_bytes'],x['text_sha256'])]:
            b = (root/safe('private/primary/'+x['name']+'.'+ext)).read_bytes()
            require(len(b) == size and sha(b) == digest, 'primary binding')


def verify(root, anchors, manifest_bytes=None, preflight=False):
    """preflight only changes the source of manifest bytes and expected self-file presence."""
    require(set(anchors) == {'FINAL.md','MANIFEST.json','REPORT.md'}, 'explicit anchors required')
    for value in anchors.values():
        require(isinstance(value,str) and len(value)==64 and
                all(c in '0123456789abcdef' for c in value), 'bad anchor')
    if manifest_bytes is None:
        require(not preflight, 'preflight requires candidate bytes')
        manifest_bytes = (root/'MANIFEST.json').read_bytes()
    require(sha(manifest_bytes) == anchors['MANIFEST.json'], 'manifest anchor mismatch')
    for name in ('FINAL.md','REPORT.md'):
        require(sha((root/name).read_bytes()) == anchors[name], name+' anchor mismatch')
    m = json.loads(manifest_bytes)
    require(m['format'] == 'r162bd-packet-v1', 'manifest format')
    rows = m['files']; names = [safe(x['path']) for x in rows]
    require(names == sorted(names) and len(names) == len(set(names)), 'file order/uniqueness')
    require('MANIFEST.json' not in names and 'REPORT.md' not in names and 'FINAL.md' in names,
            'envelope placement')
    files, dirs = inventory(root)
    expected = set(names)|{'REPORT.md','MANIFEST.json'}
    if preflight:
        require('MANIFEST.json' not in files, 'packet already sealed')
        expected.remove('MANIFEST.json')
    require(set(files) == expected, 'exact file membership mismatch')
    drows = m['directories']; dnames = [x['path'] for x in drows]
    require(dnames == sorted(dnames) and len(dnames)==len(set(dnames)), 'directory order/uniqueness')
    require(set(dnames)==set(dirs), 'directory membership mismatch')
    for x in drows:
        if x['path']: safe(x['path'])
        require(dirs[x['path']] == x['mode'], 'directory mode mismatch')
    for x in rows:
        p = root/x['path']; b = p.read_bytes()
        require(len(b)==x['bytes'] and sha(b)==x['sha256'], 'file bytes mismatch: '+x['path'])
        require(files[x['path']]==x['mode'], 'file mode mismatch: '+x['path'])
    require(files['REPORT.md']==m['envelope_modes']['REPORT.md'], 'report mode')
    if not preflight:
        require(files['MANIFEST.json']==m['envelope_modes']['MANIFEST.json'], 'manifest mode')
    if m['bindings']:
        verify_bindings(root)
    return {'payload_files':len(rows), 'whole_root_files':len(expected)+(1 if preflight else 0),
            'directories_including_root':len(dirs), 'source_and_copy_bindings':m['bindings']}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root',required=True,type=Path)
    ap.add_argument('--final-sha256',required=True)
    ap.add_argument('--manifest-sha256',required=True)
    ap.add_argument('--report-sha256',required=True)
    a=ap.parse_args()
    result=verify(a.root,{'FINAL.md':a.final_sha256,'MANIFEST.json':a.manifest_sha256,
                          'REPORT.md':a.report_sha256})
    print(json.dumps({'artifact_verification':'PASS',**result},sort_keys=True))

if __name__=='__main__':
    main()
