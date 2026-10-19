#!/usr/bin/env python3
"""Read-only archive authentication. Requires independently supplied anchors."""
import argparse, hashlib, json, os, re, stat, sys
from pathlib import Path, PurePosixPath
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TREE='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
def need(ok,msg):
    if not ok: raise ValueError(msg)
def regular(p):
    s=p.lstat(); need(stat.S_ISREG(s.st_mode) and s.st_nlink==1,'not singly linked regular file: '+str(p))
def data(p):
    regular(p); return p.read_bytes()
def digest(p): return hashlib.sha256(data(p)).hexdigest()
def readjson(p):
    def unique(pairs):
        d={}
        for k,v in pairs:
            need(k not in d,'duplicate JSON key');d[k]=v
        return d
    return json.loads(data(p),object_pairs_hook=unique)
def safe(s):
    need(isinstance(s,str) and s and not s.startswith('/') and '..' not in PurePosixPath(s).parts and str(PurePosixPath(s))==s,'unsafe relative path');return s
def inventory(base):
    need(stat.S_ISDIR(base.lstat().st_mode),'directory required')
    files=[]; dirs=[]
    for here,ds,fs in os.walk(base,followlinks=False):
        for name in ds:
            p=Path(here)/name;need(stat.S_ISDIR(p.lstat().st_mode),'symlink/special directory');dirs.append(p.relative_to(base).as_posix())
        for name in fs:
            p=Path(here)/name;regular(p);files.append(p.relative_to(base).as_posix())
    return sorted(files),sorted(dirs)
def entry(base,row,key):
    p=base/safe(row[key]);need(p.stat().st_size==row['bytes'],'size mismatch '+str(p));need(digest(p)==row['sha256'],'hash mismatch '+str(p))
def main():
    a=argparse.ArgumentParser();a.add_argument('--root',required=True);a.add_argument('--finalhash',required=True);a.add_argument('--reporthash',required=True);a.add_argument('--tree',required=True);v=a.parse_args()
    need(re.fullmatch('[0-9a-f]{64}',v.finalhash) is not None,'invalid final anchor');need(re.fullmatch('[0-9a-f]{64}',v.reporthash) is not None,'invalid report anchor')
    root=Path(v.root).absolute();need(stat.S_ISDIR(root.lstat().st_mode),'root directory required')
    need(digest(root/'FINAL.json')==v.finalhash,'detached FINAL mismatch')
    f=readjson(root/'FINAL.json');need(set(f)=={'schema','pin','status','manifest_sha256','report_sha256','verifier_sha256','controls_program_sha256','tree_sha256'},'FINAL schema')
    need(f['schema']==1 and f['pin']==PIN and f['status']=='PREFREEZE_NO_TARGET_NO_NOMINEE','FINAL contract')
    need(f['report_sha256']==v.reporthash==digest(root/'REPORT.md'),'detached report mismatch')
    need(digest(root/'verify.py')==f['verifier_sha256'],'verifier mismatch')
    need(Path(__file__).absolute()==root/'verify.py','run the verifier in the selected archive')
    need(digest(root/'run_controls.py')==f['controls_program_sha256'],'control program mismatch')
    need(digest(root/'MANIFEST.json')==f['manifest_sha256'],'manifest mismatch')
    m=readjson(root/'MANIFEST.json');need(set(m)=={'schema','files','directories'} and m['schema']==1,'manifest schema')
    files,dirs=inventory(root/'packet')
    wanted=[safe(x['path']) for x in m['files']];need(wanted==sorted(set(wanted)),'duplicate/unsorted manifest file')
    need(m['directories']==sorted(set(safe(x) for x in m['directories'])),'directory list invalid')
    need(files==wanted and dirs==m['directories'],'packet exact membership mismatch')
    for row in m['files']:need(set(row)=={'path','bytes','sha256'},'entry schema');entry(root/'packet',row,'path')
    tree=Path(v.tree);need(digest(tree)==TREE==f['tree_sha256'],'external tree mismatch')
    need(digest(root/'packet/private/context/preprints-tree.json')==TREE,'copied tree mismatch')
    t=readjson(tree);need(t['truncated'] is False and len(t['tree'])==13223 and t['sha']=='df0564b2deaab87e07854b6344d8c2f037682e77','tree contract')
    idx={x['path']:x for x in t['tree']};need(len(idx)==13223,'duplicate canonical path')
    need(readjson(root/'packet/private/context/upstream.json')['commit']==PIN,'upstream pin')
    up=root/'packet/private/upstream';rows=readjson(up/'provenance.json');seen=set();retained=0
    for row in rows:
        p=safe(row['path']);need(p not in seen,'duplicate upstream path');seen.add(p)
        canonical=idx[p];need(canonical['type']=='blob' and canonical['sha']==row['git_blob'] and canonical['size']==row['bytes'],'canonical blob metadata')
        need(row['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+p,'pinned raw URL mismatch')
        if row['retained']:
            entry(up,row,'path');b=data(up/p);need(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==row['git_blob'],'Git blob mismatch');retained+=1
        else:need(not (up/p).exists(),'removed unread body reappeared')
    primary=root/'packet/private/primary'
    for row in readjson(primary/'provenance.json'):
        if row['retained']:entry(primary,row,'file')
        elif 'file' in row:need(not (primary/row['file']).exists(),'removed primary reappeared')
    for row in readjson(primary/'artifacts.json'):entry(primary,row,'file')
    hist=root/'packet/private/history'
    for row in readjson(hist/'copies.json'):entry(hist,row,'copy')
    print(json.dumps({'integrity':'verified','files':len(files),'directories':len(dirs),'canonical_bodies':retained,'canonical_entries':len(idx),'mathematical_gate':False},sort_keys=True))
if __name__=='__main__':
    try:main()
    except Exception as e:print('REJECT: '+str(e),file=sys.stderr);sys.exit(1)
