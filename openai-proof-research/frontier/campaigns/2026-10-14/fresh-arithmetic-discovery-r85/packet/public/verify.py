#!/usr/bin/env python3
"""MIT. Read-only evidence verifier; no mathematical judgments."""
import argparse, hashlib, json, re, stat, sys
from pathlib import Path, PurePosixPath
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TREEHASH='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
def need(ok,msg):
    if not ok: raise ValueError(msg)
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def regular(p):
    s=p.lstat();need(stat.S_ISREG(s.st_mode) and s.st_nlink==1,'nonregular/symlink/hardlink: '+str(p))
def read(p):
    regular(p)
    def unique(items):
        d={}
        for k,v in items:
            need(k not in d,'duplicate JSON key');d[k]=v
        return d
    return json.loads(p.read_text(),object_pairs_hook=unique)
def safe(base,s):
    need(isinstance(s,str) and '\\' not in s,'invalid path')
    q=PurePosixPath(s)
    need(s!='' and not q.is_absolute() and '..' not in q.parts and '.' not in q.parts and str(q)==s,'unsafe path')
    return base.joinpath(*q.parts)
def inventory(root):
    need(root.is_dir() and not root.is_symlink(),'packet root')
    files={};dirs=[]
    for p in sorted(root.rglob('*')):
        s=p.lstat();r=p.relative_to(root).as_posix()
        need(not stat.S_ISLNK(s.st_mode),'symlink: '+r)
        if stat.S_ISDIR(s.st_mode):dirs.append(r)
        else:
            regular(p);files[r]={'sha256':sha(p),'bytes':s.st_size}
    return files,dirs

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',required=True,type=Path)
    ap.add_argument('--finalhash',required=True);ap.add_argument('--reporthash',required=True)
    ap.add_argument('--tree',required=True,type=Path);a=ap.parse_args()
    for v in [a.finalhash,a.reporthash]:need(bool(re.fullmatch('[0-9a-f]{64}',v)),'anchor format')
    root=a.root.absolute();need(not root.is_symlink(),'root symlink')
    final=root/'FINAL.json';regular(final);need(sha(final)==a.finalhash,'FINAL anchor mismatch');F=read(final)
    need(F['pin']==PIN and F['status']=='PREFREEZE_NO_NOMINEE' and F['frozen_target'] is None,'final identity')
    report=root/'REPORT.md';regular(report)
    need(sha(report)==a.reporthash==F['report_sha256'],'REPORT anchor mismatch')
    mf=root/'MANIFEST.json';regular(mf);need(sha(mf)==F['manifest_sha256'],'manifest anchor mismatch');M=read(mf)
    need(M['schema']==1 and M['pin']==PIN,'manifest identity')
    P=root/'packet';files,dirs=inventory(P)
    need(files==M['files'],'packet files/hash/size mismatch');need(dirs==M['directories'],'packet directory membership mismatch')
    for rel in M['files']:safe(P,rel)
    need(sha(P/'public/verify.py')==F['verifier_sha256'],'verifier identity')
    regular(a.tree);need(sha(a.tree)==TREEHASH,'external tree anchor mismatch')
    tpath=P/'private/context/preprints-tree.json';need(sha(tpath)==TREEHASH,'sealed tree mismatch')
    T=read(a.tree);need(T.get('truncated') is False and len(T['tree'])==13223,'complete tree required')
    entries={e['path']:e for e in T['tree']};need(len(entries)==13223,'duplicate canonical tree path')
    need(sum(e['type']=='blob' for e in entries.values())==10373,'tree blob count')
    need(read(P/'private/context/upstream.json')['commit']==PIN,'upstream pin mismatch')
    sources=read(P/'private/upstream-records.json');seen=set()
    for r in sources:
        need(r['path'] not in seen,'duplicate source path');seen.add(r['path'])
        f=safe(P,r['copy']);regular(f);b=f.read_bytes();e=entries[r['path']]
        need(e['type']=='blob' and e['sha']==r['git_blob'],'canonical record mismatch')
        need(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==r['git_blob'],'Git blob mismatch')
        need(sha(f)==r['sha256'] and len(b)==r['bytes']==e['size'],'source byte binding')
        need(r['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+r['path'],'raw URL pin mismatch')
        need(bool(r['semantic_reading']),'missing source reading limit')
        for label in r.get('cited_labels',[]):need(('\\label{'+label+'}') in b.decode(),'source label missing')
    for ledger in ['context-records.json','history-records.json']:
        records=read(P/'private'/ledger)
        for r in records:
            f=safe(P,r['copy']);regular(f);need(sha(f)==r['sha256'],'copied record mismatch')
            if 'bytes' in r:need(f.stat().st_size==r['bytes'],'copied record size')
    primaries=read(P/'private/primary-records.json');success=0
    for r in primaries:
        need(r['status'] in ['retrieved','failed'],'primary status')
        if r['status']=='failed':need(bool(r['error']),'failure missing error');continue
        success+=1
        for field,hkey,bkey in [('copy','sha256','bytes'),('text_copy','text_sha256','text_bytes')]:
            f=safe(P,r[field]);regular(f);need(sha(f)==r[hkey] and f.stat().st_size==r[bkey],'primary binding mismatch')
        need(bool(r['semantic_reading']),'missing primary reading limit')
    need(len(sources)==19 and success==6,'source/primary inventory')
    print(json.dumps({'integrity':'verified','payload_files':len(files),'directories':len(dirs),'canonical_blobs':len(sources),'primary_pairs':success,'history_copies':len(read(P/'private/history-records.json')),'mathematical_gate':None},sort_keys=True))
if __name__=='__main__':
    try:main()
    except (ValueError,KeyError,OSError,TypeError) as e:
        print('REJECT: '+str(e),file=sys.stderr);sys.exit(1)
