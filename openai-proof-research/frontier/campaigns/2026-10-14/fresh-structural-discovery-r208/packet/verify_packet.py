"""Read-only exact-selection verifier; detached anchors must be explicit arguments."""
from pathlib import Path
import argparse, hashlib, json, os, stat

def sha(b): return hashlib.sha256(b).hexdigest()

def verify(root, final_anchor, manifest_anchor, report_anchor):
    root=Path(root)
    for name,anchor in [('packet/FINAL.txt',final_anchor),('MANIFEST.json',manifest_anchor),('REPORT.txt',report_anchor)]:
        p=root/name
        if p.is_symlink() or not p.is_file(): raise ValueError('missing/linked anchor: '+name)
        if sha(p.read_bytes())!=anchor: raise ValueError('anchor mismatch: '+name)
    m=json.loads((root/'MANIFEST.json').read_bytes())
    payload=root/'packet'
    actual_files={};actual_dirs={}
    stack=[payload]
    while stack:
        p=stack.pop();rel=p.relative_to(payload).as_posix()
        actual_dirs[rel]=stat.S_IMODE(p.stat().st_mode)
        with os.scandir(p) as it:
            for e in it:
                q=Path(e.path)
                if e.is_symlink():raise ValueError('symlink in packet')
                if e.is_dir(follow_symlinks=False):stack.append(q)
                elif e.is_file(follow_symlinks=False):actual_files[q.relative_to(payload).as_posix()]=q
                else:raise ValueError('non-regular entry')
    expected={e['path']:e for e in m['entries']}
    if len(expected)!=len(m['entries']):raise ValueError('duplicate entry')
    if set(actual_files)!=set(expected):raise ValueError('selection mismatch: missing='+str(sorted(set(expected)-set(actual_files)))+' extra='+str(sorted(set(actual_files)-set(expected))))
    if actual_dirs!=m['directories']:raise ValueError('directory selection/mode mismatch')
    for name,p in actual_files.items():
        e=expected[name];b=p.read_bytes()
        if len(b)!=e['bytes'] or sha(b)!=e['sha256']:raise ValueError('payload mismatch: '+name)
        if stat.S_IMODE(p.stat().st_mode)!=e['mode']:raise ValueError('mode mismatch: '+name)
    for name in ['MANIFEST.json','REPORT.txt']:
        if stat.S_IMODE((root/name).stat().st_mode)!=0o444:raise ValueError('anchor file mode mismatch: '+name)
    return {'artifact_verification':'exact selection, detached hashes, sizes and modes match','files':len(expected),'directories':len(actual_dirs),'mathematical_gate':False}

if __name__=='__main__':
    p=argparse.ArgumentParser()
    for x in ['root','final-sha256','manifest-sha256','report-sha256']:p.add_argument('--'+x,required=True)
    a=p.parse_args()
    print(json.dumps(verify(a.root,a.final_sha256,a.manifest_sha256,a.report_sha256),indent=2))
