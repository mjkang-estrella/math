#!/usr/bin/env python3
"""Read-only review verifier. All three detached byte anchors must be supplied."""
from pathlib import Path
import argparse, hashlib, json, os, stat

FORMAT = 'structural-r220-correctness-r1-exact-selection-v1'

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def mode(p):
    return format(stat.S_IMODE(p.lstat().st_mode), '04o')

def inventory(packet):
    files, directories = [], []
    def visit(p):
        st=p.lstat()
        if not stat.S_ISDIR(st.st_mode):
            raise ValueError('directory is not a real directory')
        rel=p.relative_to(packet).as_posix()
        directories.append({'path':rel,'mode':mode(p)})
        with os.scandir(p) as it:
            children=sorted(list(it),key=lambda x:x.name)
        for child in children:
            cp=Path(child.path); st=cp.lstat()
            if stat.S_ISLNK(st.st_mode):
                raise ValueError('symlink forbidden')
            if stat.S_ISDIR(st.st_mode):
                visit(cp)
            elif stat.S_ISREG(st.st_mode):
                files.append({'path':cp.relative_to(packet).as_posix(),
                              'bytes':st.st_size,'mode':mode(cp),'sha256':digest(cp)})
            else:
                raise ValueError('nonregular member forbidden')
    visit(packet)
    return sorted(files,key=lambda x:x['path']), sorted(directories,key=lambda x:x['path'])

def verify(root, manifest_sha256, final_sha256, report_sha256):
    root=Path(root)
    for label,value in [('manifest',manifest_sha256),('FINAL',final_sha256),('REPORT',report_sha256)]:
        if len(value)!=64 or any(c not in '0123456789abcdef' for c in value):
            raise ValueError('invalid explicit '+label+' anchor')
    if root.is_symlink(): raise ValueError('symlink root forbidden')
    for name,anchor in [('MANIFEST.json',manifest_sha256),('REPORT.md',report_sha256)]:
        p=root/name
        if not stat.S_ISREG(p.lstat().st_mode) or mode(p)!='0400':
            raise ValueError('outside file type or mode mismatch: '+name)
        if digest(p)!=anchor: raise ValueError('detached anchor mismatch: '+name)
    manifest=json.loads((root/'MANIFEST.json').read_bytes())
    if manifest.get('format')!=FORMAT: raise ValueError('unsupported manifest')
    for group in ['files','directories']:
        names=[v['path'] for v in manifest[group]]
        if len(names)!=len(set(names)): raise ValueError('duplicate selected path')
        for name in names:
            p=Path(name)
            if p.is_absolute() or '..' in p.parts or p.as_posix()!=name:
                raise ValueError('unsafe selected path')
    files,dirs=inventory(root/'packet')
    if files!=manifest['files']: raise ValueError('exact file selection, bytes or modes mismatch')
    if dirs!=manifest['directories']: raise ValueError('exact directory selection or modes mismatch')
    if digest(root/'packet/FINAL.md')!=final_sha256: raise ValueError('FINAL anchor mismatch')
    return {'artifact_verification':'PASS: exact selected bytes, membership and modes',
            'files':len(files),'directories':len(dirs),'selected_file_bytes':sum(v['bytes'] for v in files),
            'manifest_sha256':manifest_sha256,'final_sha256':final_sha256,'report_sha256':report_sha256,
            'mathematical_gate':False}

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root',required=True)
    ap.add_argument('--manifest-sha256',required=True)
    ap.add_argument('--final-sha256',required=True)
    ap.add_argument('--report-sha256',required=True)
    args=ap.parse_args()
    print(json.dumps(verify(args.root,args.manifest_sha256,args.final_sha256,args.report_sha256),indent=2))
