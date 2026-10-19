#!/usr/bin/env python3
"""Read-only artifact verification; no mathematical gates. Original code: MIT."""
import argparse, hashlib, json, os, re, stat, sys
from pathlib import Path, PurePosixPath
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TREE_SHA='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'

def audit(event,args):
    if event=='open':
        mode=args[1]; flags=args[2]
        if (isinstance(mode,str) and any(c in mode for c in 'wax+')) or (isinstance(flags,int) and flags & (os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)):
            raise PermissionError('read-only verifier denies write-open')
    if event in {'os.remove','os.unlink','os.rename','os.rmdir','os.mkdir','os.chmod','os.chown','os.link','os.symlink','os.truncate','os.utime','subprocess.Popen','os.system'}:
        raise PermissionError('read-only verifier denies '+event)

def need(x,msg):
    if not x: raise ValueError(msg)
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def obj(p): return json.loads(p.read_text())
def rel(s):
    need(isinstance(s,str) and s and '\\' not in s,'invalid path')
    q=PurePosixPath(s)
    need(not q.is_absolute() and '..' not in q.parts and str(q)==s,'unsafe path')
    return s

def run(root,anchor):
    need(re.fullmatch('[0-9a-f]{64}',anchor) is not None,'detached FINAL SHA256 required')
    need(root.is_dir() and not root.is_symlink(),'root must be real directory')
    final=root/'FINAL.json';need(not final.is_symlink(),'FINAL symlink')
    need(sha(final)==anchor,'detached FINAL mismatch');f=obj(final)
    need(f['schema']=='arithmetic-r93-v1' and f['pin']==PIN,'wrong schema/pin')
    need(f['status']=='AUTHOR_PROOF_FOR_INDEPENDENT_ASSESSMENT','wrong declared status')
    need(f['gates']=={'correctness':None,'contribution':None,'acceptance':None},'unexpected gate claim')
    need(sha(root/'REPORT.md')==f['report_sha256'],'outside report mismatch')
    for path,record in f['root_files'].items():
        q=root/rel(path);need(q.is_file() and not q.is_symlink(),'root file type')
        need(sha(q)==record['sha256'] and q.stat().st_size==record['bytes'],'root file mismatch: '+path)
    packet=root/'packet'; need(packet.is_dir() and not packet.is_symlink(),'packet root type')
    manifest=packet/'MANIFEST.json';need(not manifest.is_symlink(),'manifest symlink')
    need(sha(manifest)==f['manifest_sha256'],'manifest mismatch'); m=obj(manifest)
    gotfiles={};gotdirs={'.'}
    for d,dirs,files in os.walk(packet,followlinks=False):
        for n in dirs:
            q=Path(d)/n; need(not q.is_symlink(),'directory symlink');gotdirs.add(q.relative_to(packet).as_posix())
        for n in files:
            q=Path(d)/n; st=q.lstat();need(stat.S_ISREG(st.st_mode),'nonregular payload')
            r=q.relative_to(packet).as_posix()
            if r!='MANIFEST.json':gotfiles[r]=q
    need(set(gotfiles)==set(m['files']),'exact file membership mismatch')
    need(gotdirs==set(m['directories']),'exact directory membership mismatch')
    for r,rec in m['files'].items():
        q=gotfiles[rel(r)];st=q.stat()
        need(st.st_size==rec['bytes'] and sha(q)==rec['sha256'],'payload bytes mismatch: '+r)
        need(stat.S_IMODE(st.st_mode)==rec['mode'] and st.st_nlink==rec['nlink']==1,'payload mode/link mismatch: '+r)
    for r,mode in m['directory_modes'].items():
        need(r=='.' or rel(r),'directory path')
        need(stat.S_IMODE((packet/r).stat().st_mode)==mode,'directory mode mismatch')
    need(set(m['directory_modes'])==gotdirs,'directory mode coverage')
    need(sha(packet/'public/FROZEN.md')==f['frozen_sha256'],'frozen external anchor')
    freeze=obj(packet/'public/freeze.json');need(freeze['sha256']==f['frozen_sha256'] and freeze['frozen_path']=='public/FROZEN.md','freeze receipt mismatch')
    treepath=packet/'private/context/sources/preprints-tree.json'
    need(sha(treepath)==TREE_SHA==f['tree_sha256'],'complete tree anchor')
    tree=obj(treepath);need(tree.get('truncated') is False,'truncated tree')
    entries=tree['tree'];need(len(entries)==13223,'tree count')
    bypath={x['path']:x for x in entries};need(len(bypath)==13223,'duplicate tree path')
    rows=obj(packet/'public/canonical.json');need(len(rows)==22,'canonical count')
    need(len({x['canonical']['path'] for x in rows})==len(rows),'duplicate source')
    for x in rows:
        c=x['canonical'];need(bypath.get(c['path'])==c,'canonical full metadata mismatch')
        need(c['type']=='blob','not canonical blob')
        need(x['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+c['path'],'unpinned raw URL')
        b=(packet/rel(x['local'])).read_bytes()
        need(len(b)==c['size'] and hashlib.sha256(b).hexdigest()==x['sha256'],'canonical body sha/size')
        need(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==c['sha'],'canonical Git blob mismatch')
    primary=obj(packet/'public/primary.json'); successes=0
    for x in primary:
        if 'failure' in x:continue
        successes+=1
        need(sha(packet/rel(x['pdf']))==x['sha256'],'primary PDF mismatch')
        need(sha(packet/rel(x['text']))==x['text_sha256'],'primary text mismatch')
    need(successes==4,'primary pair count')
    for name,count in [('context',5),('history',28)]:
        rows=obj(packet/('public/'+name+'.json'));need(len(rows)==count,'copy count')
        for x in rows:
            q=packet/rel(x['local']);need(sha(q)==x['sha256'] and q.stat().st_size==x['bytes'],'copy anchor mismatch')
    return {'status':'INTEGRITY_ONLY_OK','payloads':len(gotfiles),'directories':len(gotdirs),'canonical_bodies':22,'primary_pairs':4,'history_copies':28,'context_copies':5,'frozen_sha256':f['frozen_sha256'],'manifest_sha256':f['manifest_sha256'],'report_sha256':f['report_sha256'],'mathematical_gate':False}

def main():
    a=argparse.ArgumentParser();a.add_argument('--root',required=True);a.add_argument('--final-sha256',required=True);ns=a.parse_args()
    sys.addaudithook(audit)
    try: print(json.dumps(run(Path(ns.root),ns.final_sha256),sort_keys=True))
    except Exception as e:
        print(json.dumps({'status':'REJECT','error':str(e)}));return 1
    return 0
if __name__=='__main__':sys.exit(main())
