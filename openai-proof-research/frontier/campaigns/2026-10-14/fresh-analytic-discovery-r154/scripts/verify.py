#!/usr/bin/env python3
"""Read-only exact file-membership verifier; requires three detached anchors."""
import argparse,hashlib,json,os,re,stat
from pathlib import Path
ENVELOPES={'FINAL.md','MANIFEST.json','REPORT.md'}
def sha(b): return hashlib.sha256(b).hexdigest()
def files(root):
    result={}
    for base,dirs,names in os.walk(root,topdown=True,followlinks=False):
        for name in dirs:
            p=Path(base)/name
            if p.is_symlink(): raise ValueError('symlink directory: '+str(p))
        for name in names:
            p=Path(base)/name;s=p.lstat();rel=p.relative_to(root).as_posix()
            if not stat.S_ISREG(s.st_mode) or s.st_nlink!=1:
                raise ValueError('nonregular or linked file: '+rel)
            result[rel]=p
    return result

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('root',type=Path)
    for n in ['final','manifest','report']:ap.add_argument('--'+n+'-sha256',required=True)
    a=ap.parse_args();root=a.root
    if root.is_symlink() or not root.is_dir():raise ValueError('root must be a real directory')
    anchors={'FINAL.md':a.final_sha256,'MANIFEST.json':a.manifest_sha256,'REPORT.md':a.report_sha256}
    actual=files(root)
    for n,h in anchors.items():
        if not re.fullmatch('[0-9a-f]{64}',h):raise ValueError('invalid detached anchor: '+n)
        if n not in actual or sha(actual[n].read_bytes())!=h:raise ValueError('envelope mismatch: '+n)
    manifest=json.loads(actual['MANIFEST.json'].read_bytes())
    if manifest['format']!='r154-exact-files-v1':raise ValueError('manifest format')
    entries=manifest['files'];expected={}
    for x in entries:
        n=x['path'];p=Path(n)
        if p.is_absolute() or '..' in p.parts or p.as_posix()!=n or n in ENVELOPES or n in expected:
            raise ValueError('invalid or duplicate manifest path: '+n)
        expected[n]=x
    if set(actual)-ENVELOPES!=set(expected):
        raise ValueError('membership mismatch; missing='+repr(sorted(set(expected)-set(actual)))+' extra='+repr(sorted(set(actual)-ENVELOPES-set(expected))))
    for n,x in expected.items():
        b=actual[n].read_bytes()
        if len(b)!=x['size'] or sha(b)!=x['sha256']:raise ValueError('payload mismatch: '+n)
    print(json.dumps({'artifact_check':'MATCH','payload_files':len(expected),'envelopes':3,'scope':'regular single-link file membership and bytes; not mathematics, rights, modes or empty directories'}))
if __name__=='__main__':
    try:main()
    except Exception as e:
        print(json.dumps({'artifact_check':'REJECT','reason':str(e)}));raise SystemExit(1)
