#!/usr/bin/env python3
"""Read-only packet verifier. Three SHA256 anchors must be supplied externally."""
import argparse,hashlib,json,os,re,stat
from pathlib import Path
ENVELOPES=('envelopes/FINAL.md','envelopes/MANIFEST.json','envelopes/REPORT.md')
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def inspect(root):
    files={};dirs=[]
    for base,dnames,fnames in os.walk(root,topdown=True,followlinks=False):
        for name in dnames:
            p=Path(base)/name;s=p.lstat()
            if not stat.S_ISDIR(s.st_mode) or p.is_symlink():raise ValueError('nonordinary directory '+str(p))
            dirs.append(p.relative_to(root).as_posix())
        for name in fnames:
            p=Path(base)/name;s=p.lstat();rel=p.relative_to(root).as_posix()
            if not stat.S_ISREG(s.st_mode) or s.st_nlink!=1:raise ValueError('nonordinary or multiply linked file '+rel)
            files[rel]={'bytes':s.st_size,'sha256':digest(p)}
    return files,sorted(dirs)
def main():
    a=argparse.ArgumentParser();a.add_argument('root');a.add_argument('--final-sha',required=True);a.add_argument('--manifest-sha',required=True);a.add_argument('--report-sha',required=True);v=a.parse_args()
    r=Path(v.root)
    if r.is_symlink() or not r.is_dir():raise ValueError('root must be an ordinary directory')
    anchors=(v.final_sha,v.manifest_sha,v.report_sha)
    for name,sha in zip(ENVELOPES,anchors):
        if not re.fullmatch('[0-9a-f]{64}',sha):raise ValueError('invalid detached SHA256')
        p=r/name
        if p.is_symlink() or not p.is_file() or p.stat().st_nlink!=1:raise ValueError('invalid envelope '+name)
        if digest(p)!=sha:raise ValueError('detached anchor mismatch '+name)
    m=json.loads((r/ENVELOPES[1]).read_text())
    if m['schema']!='r130-exact-v1' or m['excluded_envelopes']!=list(ENVELOPES):raise ValueError('manifest schema mismatch')
    files,dirs=inspect(r)
    for name in ENVELOPES:del files[name]
    if files!=m['files']:raise ValueError('payload bytes or exact file membership mismatch')
    if dirs!=m['directories']:raise ValueError('exact directory membership mismatch')
    print(json.dumps({'artifact_check':'consistent','payload_files':len(files),'directories':len(dirs),'envelopes':3,'mathematical_gate':False}))
if __name__=='__main__':
    try:main()
    except Exception as e:raise SystemExit('INVALID: '+str(e))
