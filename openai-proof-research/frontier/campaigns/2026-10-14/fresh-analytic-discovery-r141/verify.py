#!/usr/bin/env python3
"""Read-only exact packet verifier. Three external anchors are mandatory.
No network, originals mutation, acquisition, or mathematical gate is performed.
"""
from pathlib import Path
import argparse,hashlib,json,os,stat,sys

def sha(b):return hashlib.sha256(b).hexdigest()
def inventory(root):
    files={};dirs=[]
    for d,ds,fs in os.walk(root,followlinks=False):
        for n in ds:
            p=Path(d)/n
            if not stat.S_ISDIR(p.lstat().st_mode) or p.is_symlink():raise ValueError('non-directory or symlink: '+str(p))
            dirs.append(str(p.relative_to(root)))
        for n in fs:
            p=Path(d)/n
            if not stat.S_ISREG(p.lstat().st_mode):raise ValueError('nonregular file: '+str(p))
            b=p.read_bytes();files[str(p.relative_to(root))]={'size':len(b),'sha256':sha(b)}
    return files,sorted(dirs)

def verify(root,anchors):
    envelopes={'FINAL.md','MANIFEST.json','REPORT.md'}
    for name,anchor in anchors.items():
        if len(anchor)!=64 or any(c not in '0123456789abcdef' for c in anchor):raise ValueError('invalid detached anchor')
        p=root/name
        if not stat.S_ISREG(p.lstat().st_mode):raise ValueError('nonregular envelope')
        if sha(p.read_bytes())!=anchor:raise ValueError('detached anchor mismatch: '+name)
    m=json.loads((root/'MANIFEST.json').read_text())
    if m['outside_envelopes']!=sorted(envelopes):raise ValueError('wrong outside set')
    files,dirs=inventory(root)
    actual={k:v for k,v in files.items() if k not in envelopes}
    expected=m['files']
    if actual!=expected:raise ValueError('payload membership or bytes differ')
    if dirs!=m['directories']:raise ValueError('directory membership differs')
    auth=root/'source-authentication.json'
    if auth.exists():
        a=json.loads(auth.read_text());treepath=root/'private/original-selections/02-preprints-tree.json';tb=treepath.read_bytes();t=json.loads(tb)
        if sha(tb)!='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b' or t['truncated'] or len(t['tree'])!=13223:raise ValueError('canonical full tree mismatch')
        bypath={x['path']:x for x in t['tree']}
        for row in a['files']:
            p=root/row['local'];b=p.read_bytes();x=bypath[row['path']]
            blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
            if len(b)!=row['size'] or len(b)!=x['size'] or blob!=row['git_blob'] or blob!=x['sha'] or sha(b)!=row['sha256']:raise ValueError('source authentication mismatch')
            if row['url']!='https://raw.githubusercontent.com/openai/math/'+a['pin']+'/'+row['path']:raise ValueError('source URL mismatch')
    print(json.dumps({'result':'ARTIFACT_INTEGRITY_ONLY','payload_files':len(actual),'outside_envelopes':3,'directories':len(dirs)}))

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('root',type=Path);p.add_argument('--final-sha256',required=True);p.add_argument('--manifest-sha256',required=True);p.add_argument('--report-sha256',required=True)
    a=p.parse_args()
    verify(a.root,{'FINAL.md':a.final_sha256,'MANIFEST.json':a.manifest_sha256,'REPORT.md':a.report_sha256})
if __name__=='__main__':
    try:main()
    except Exception as e:print('FAIL: '+str(e),file=sys.stderr);sys.exit(1)
