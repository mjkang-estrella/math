#!/usr/bin/env python3
"""Read-only exact-selection verifier; supply detached anchors explicitly."""
import argparse, hashlib, json, os, re, stat, sys
from pathlib import Path, PurePosixPath

def sha(b): return hashlib.sha256(b).hexdigest()
def mode(p): return format(stat.S_IMODE(p.stat(follow_symlinks=False).st_mode), '04o')
def safe(s):
    q=PurePosixPath(s)
    if q.is_absolute() or '..' in q.parts or str(q)!=s or s=='.':
        raise ValueError('unsafe or noncanonical file path')
    return q

def verify(a):
    for value in (a.final_sha256,a.manifest_sha256,a.report_sha256):
        if not re.fullmatch('[0-9a-f]{64}',value): raise ValueError('anchors must be explicit SHA256 hex')
    root=Path(a.packet)
    if root.is_symlink() or not root.is_dir(): raise ValueError('packet must be a real directory')
    manifest=Path(a.manifest); report=Path(a.report)
    if manifest.is_symlink() or report.is_symlink(): raise ValueError('detached files may not be symlinks')
    mb=manifest.read_bytes(); rb=report.read_bytes()
    if sha(mb)!=a.manifest_sha256: raise ValueError('MANIFEST anchor mismatch')
    if sha(rb)!=a.report_sha256: raise ValueError('REPORT anchor mismatch')
    if mode(manifest)!='0444' or mode(report)!='0444': raise ValueError('detached file mode mismatch')
    m=json.loads(mb)
    if m.get('version')!=1: raise ValueError('unsupported manifest version')
    expected={x['path']:x for x in m['packet_files']}
    if len(expected)!=len(m['packet_files']): raise ValueError('duplicate file entry')
    ed={x['path']:x['mode'] for x in m['packet_directories']}
    if len(ed)!=len(m['packet_directories']): raise ValueError('duplicate directory entry')
    actual={}; ad={'.':mode(root)}; stack=[root]
    while stack:
        d=stack.pop()
        with os.scandir(d) as iterator:
            for e in iterator:
                q=Path(e.path); rel=q.relative_to(root).as_posix()
                if e.is_symlink(): raise ValueError('symlink in packet: '+rel)
                if e.is_dir(follow_symlinks=False):
                    ad[rel]=mode(q); stack.append(q)
                elif e.is_file(follow_symlinks=False): actual[rel]=q
                else: raise ValueError('special file in packet: '+rel)
    if set(actual)!=set(expected): raise ValueError('exact file selection mismatch')
    if ad!=ed: raise ValueError('exact directory selection or mode mismatch')
    for rel,entry in expected.items():
        safe(rel); q=actual[rel]; b=q.read_bytes()
        if len(b)!=entry['bytes'] or sha(b)!=entry['sha256']: raise ValueError('file bytes mismatch: '+rel)
        if mode(q)!=entry['mode']: raise ValueError('file mode mismatch: '+rel)
    if 'FINAL.md' not in expected or sha(actual['FINAL.md'].read_bytes())!=a.final_sha256:
        raise ValueError('FINAL anchor mismatch')
    txt=rb.decode('utf-8')
    for label,value in [('FINAL SHA256',a.final_sha256),('MANIFEST SHA256',a.manifest_sha256)]:
        if label+': '+value not in txt: raise ValueError('REPORT does not bind '+label)
    return {'ok':True,'files':len(actual),'directories':len(ad),'read_only':True}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    for arg in ['packet','manifest','report','final-sha256','manifest-sha256','report-sha256']:
        p.add_argument('--'+arg,required=True)
    try: print(json.dumps(verify(p.parse_args()),sort_keys=True))
    except Exception as e:
        print(json.dumps({'ok':False,'error':str(e)},sort_keys=True)); sys.exit(1)
if __name__=='__main__': main()
