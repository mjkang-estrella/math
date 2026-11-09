#!/usr/bin/env python3
"""Read-only artifact verification. Requires externally supplied detached anchors.
No mathematical, contribution, priority, acceptance or release verdict.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys


def digest(data):
    return hashlib.sha256(data).hexdigest()


def fail(message):
    raise ValueError(message)


def safe(base, name):
    q = PurePosixPath(name)
    if q.is_absolute() or '..' in q.parts:
        fail('unsafe relative path')
    return base.joinpath(*q.parts)


def regular(path):
    s = path.lstat()
    if not stat.S_ISREG(s.st_mode) or s.st_nlink != 1:
        fail('not a single-link regular file: ' + str(path))
    return s


def read(path):
    regular(path)
    return path.read_bytes()


def record(path):
    s = regular(path)
    return {'sha256': digest(path.read_bytes()), 'bytes': s.st_size,
            'mode': stat.S_IMODE(s.st_mode)}


def audit(event, args):
    if event == 'open':
        mode, flags = args[1], args[2]
        if isinstance(mode, str) and any(c in mode for c in 'wax+'):
            fail('write denied')
        if isinstance(flags, int) and flags & (os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND):
            fail('write denied')
    if event in {'os.remove','os.rename','os.mkdir','os.rmdir','os.chmod',
                 'os.link','os.symlink','os.truncate','os.utime',
                 'subprocess.Popen','socket.connect'}:
        fail('mutation/network denied: ' + event)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', required=True, type=Path)
    ap.add_argument('--project', required=True, type=Path)
    for n in ['final','manifest','report']:
        ap.add_argument('--'+n+'-sha256', required=True)
    a = ap.parse_args()
    sys.addaudithook(audit)
    root = a.root.resolve(); project = a.project.resolve(); packet = root/'packet'
    for s in [a.final_sha256,a.manifest_sha256,a.report_sha256]:
        if re.fullmatch('[0-9a-f]{64}',s) is None:fail('invalid detached anchor')
    fb=read(root/'FINAL.json'); mb=read(packet/'MANIFEST.json'); rb=read(root/'REPORT.md')
    if digest(fb)!=a.final_sha256:fail('detached FINAL mismatch')
    if digest(mb)!=a.manifest_sha256:fail('detached MANIFEST mismatch')
    if digest(rb)!=a.report_sha256:fail('detached outside REPORT mismatch')
    final=json.loads(fb); manifest=json.loads(mb)
    if final['manifest_sha256']!=a.manifest_sha256 or final['report_sha256']!=a.report_sha256:
        fail('FINAL anchor bindings mismatch')
    files={}; directories={}
    for parent, dirs, names in os.walk(packet,followlinks=False):
        p=Path(parent);s=p.lstat()
        if not stat.S_ISDIR(s.st_mode):fail('non-directory payload node')
        directories[p.relative_to(packet).as_posix()]=stat.S_IMODE(s.st_mode)
        for name in dirs:
            if (p/name).is_symlink():fail('directory symlink')
        for name in names:
            q=p/name; rel=q.relative_to(packet).as_posix()
            if rel=='MANIFEST.json':regular(q);continue
            files[rel]=record(q)
    if files!=manifest['files']:fail('payload file set/hash/size/mode mismatch')
    if directories!=manifest['directories']:fail('payload directory set/mode mismatch')
    for name,expected in final['outside_bindings'].items():
        if record(safe(root,name))!=expected:fail('outside binding mismatch: '+name)
    treeb=read(packet/'private/controls/sources/preprints-tree.json')
    if digest(treeb)!='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b':
        fail('complete tree hash mismatch')
    tree=json.loads(treeb)
    if tree.get('truncated') is not False or len(tree['tree'])!=13223:fail('tree scope mismatch')
    index={z['path']:z for z in tree['tree']}
    source=json.loads(read(packet/'private/source-register.json'))
    for z in source:
        b=read(safe(packet/'private/upstream',z['path']))
        gh=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        ent=index[z['path']]
        if digest(b)!=z['sha256'] or gh!=z['blob'] or gh!=ent['sha'] or len(b)!=z['bytes'] or len(b)!=ent['size']:
            fail('pinned source authentication mismatch: '+z['path'])
    primary=json.loads(read(packet/'private/primary/register.json'))
    for z in primary:
        for suffix,key in [('.pdf','sha256'),('.txt','text_sha256')]:
            if digest(read(packet/'private/primary'/(z['id']+suffix)))!=z[key]:fail('primary hash mismatch')
    originals=json.loads(read(packet/'private/originals-before.json'))
    for z in originals:
        original=read(safe(project,z['path']))
        copied=read(safe(packet/'private/controls',z['path']))
        if digest(original)!=z['sha256'] or len(original)!=z['bytes'] or copied!=original:
            fail('original/copy preservation mismatch: '+z['path'])
    if digest(read(packet/'public/frozen-scope.md'))!=final['frozen_scope_sha256']:
        fail('frozen scope changed')
    print(json.dumps({'artifact_verification':'PASS','mathematical_gate':False,
        'payload_files':len(files),'payload_directories':len(directories),
        'pinned_bodies':len(source),'primary_pdfs':len(primary),
        'originals_and_copies_unchanged':len(originals),
        'limits':'Exact packet domain; explicit FINAL/outside bindings; original files listed in originals-before. Not whole workspace, syscall sandbox, or mathematical review.'},sort_keys=True))


if __name__=='__main__':
    try:main()
    except (ValueError,KeyError,OSError,AssertionError) as e:
        print('FAIL: '+str(e),file=sys.stderr);sys.exit(1)
