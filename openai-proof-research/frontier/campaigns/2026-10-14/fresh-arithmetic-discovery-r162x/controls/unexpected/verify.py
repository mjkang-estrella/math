#!/usr/bin/env python3
"""Read-only verification; callers MUST supply three detached SHA256 anchors."""
import argparse, hashlib, json, stat
from pathlib import Path
RESERVED={'FINAL.md','MANIFEST.json','REPORT.md','ANCHORS.json'}
def sha(b): return hashlib.sha256(b).hexdigest()
def inventory(root):
    files={}; dirs=[]
    for p in sorted(root.rglob('*')):
        rel=p.relative_to(root).as_posix()
        if p.is_symlink(): raise ValueError('symlink rejected: '+rel)
        if p.is_dir(): dirs.append(rel)
        elif p.is_file():
            if rel in RESERVED: continue
            b=p.read_bytes(); files[rel]={'bytes':len(b),'sha256':sha(b),'mode':stat.S_IMODE(p.stat().st_mode)}
        else: raise ValueError('nonregular member: '+rel)
    return files,dirs
def verify(root,anchors):
    root=Path(root).resolve()
    for name,expected in anchors.items():
        if len(expected)!=64 or any(c not in '0123456789abcdef' for c in expected): raise ValueError('invalid explicit SHA256')
        p=root/name
        if p.is_symlink() or sha(p.read_bytes())!=expected: raise ValueError('detached anchor mismatch: '+name)
    m=json.loads((root/'MANIFEST.json').read_text())
    if m['format']!='r162x-exact-local-v1': raise ValueError('manifest format')
    files,dirs=inventory(root)
    if files!=m['files']: raise ValueError('exact file membership/content/mode mismatch')
    if dirs!=m['directories']: raise ValueError('exact directory membership mismatch')
    return {'artifact_integrity':'matched','files':len(files),'directories':len(dirs),'mathematical_gate':False}
def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--root',required=True)
    for x in ['final','manifest','report']:p.add_argument('--'+x+'-sha256',required=True)
    a=p.parse_args()
    try: print(json.dumps(verify(a.root,{'FINAL.md':a.final_sha256,'MANIFEST.json':a.manifest_sha256,'REPORT.md':a.report_sha256}),sort_keys=True))
    except (OSError,ValueError,KeyError,TypeError) as e: p.exit(1,'REJECT: '+str(e)+'\n')
if __name__=='__main__': main()
