#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. SPDX-License-Identifier: MIT
"""Read-only external-anchor authentication; not a mathematical proof checker."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys

AUTHOR='10665dc832a51bca7651cbb091951b8b3ae3a7442339a64fd3b69e4b9743c606'
SCOPE='bda045b928a2f5b4ea52b96eb1ae6f3ea17146a575cefd955461994399d19f03'
CANDIDATE='2fd9649ae04c531eca486848917cbc3dc7ddfffdac9881ff1742594d2060147d'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'

def need(ok,why):
    if not ok:raise ValueError(why)
def sha(b):return hashlib.sha256(b).hexdigest()
def pairs(items):
    d={}
    for k,v in items:need(k not in d,'duplicate JSON key');d[k]=v
    return d
def parse(b):return json.loads(b,object_pairs_hook=pairs)
def safe(n):
    need(isinstance(n,str) and n and n!='.' and '\\' not in n,'bad path')
    p=PurePosixPath(n);need(not p.is_absolute() and str(p)==n and '..' not in p.parts,'unsafe path')
    return n

def read(root,name):
    p=root/safe(name)
    for q in [p,*p.parents]:need(not q.is_symlink(),'symlink ancestor')
    need(stat.S_ISREG(p.lstat().st_mode),'not regular file')
    return p.read_bytes()

def inventory(root,anchor):
    need(re.fullmatch('[0-9a-f]{64}',anchor) is not None,'invalid external anchor')
    raw=read(root,'manifest.json');need(sha(raw)==anchor,'external manifest anchor mismatch');m=parse(raw)
    names=set()
    for e in m['files']:
        n=safe(e['path']);need(n not in names and n!='manifest.json','duplicate/reserved payload');names.add(n)
        b=read(root,n);need(len(b)==e['bytes'] and sha(b)==e['sha256'],'payload mismatch: '+n)
    ff=set();dd=set()
    for p in root.rglob('*'):
        need(not p.is_symlink(),'symlink entry')
        n=p.relative_to(root).as_posix()
        if stat.S_ISREG(p.lstat().st_mode):ff.add(n)
        else:need(p.is_dir(),'special entry');dd.add(n)
    need(ff==names|{'manifest.json'},'exact file membership mismatch')
    need(dd==set(m['directories']) and len(dd)==len(m['directories']),'exact directory membership mismatch')
    return m,len(names)

def audit(event,args):
    if event=='open':
        mode,flags=args[1:3]
        need(not isinstance(mode,str) or not any(c in mode for c in 'wax+'),'writes forbidden')
        need(not isinstance(flags,int) or not flags & (os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND),'write flags forbidden')
    need(event not in {'os.remove','os.rename','os.mkdir','os.rmdir','os.chmod','os.symlink','os.link','os.truncate','subprocess.Popen','os.system'},'mutation/execution forbidden')
    need(not event.startswith('socket.'),'network forbidden')

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--anchor',required=True);a=ap.parse_args()
    sys.addaudithook(audit)
    root=Path(__file__).absolute().parent
    m,n=inventory(root,a.anchor);need(m['schema']=='W5-proof-review-v1','review schema')
    author=root.parent/'fresh-analytic-discovery-r25';am,an=inventory(author,AUTHOR)
    need(am['schema']=='W5-exact-membership-v1' and an==69,'author identity/count')
    need(sha(read(author,'original-scope.md'))==SCOPE and sha(read(author,'candidate.md'))==CANDIDATE,'frozen full target identity')
    fr=parse(read(author,'freeze-receipt.json'));need(fr['scope_sha256']==SCOPE,'freeze scope')
    for name,h in fr['pre_freeze_files'].items():need(sha(read(author,name))==h,'pre-freeze record')
    treebytes=read(author,'inputs/sources/preprints-tree.json');tree=parse(treebytes)
    need(tree['truncated'] is False,'complete preprints tree required')
    repo=root.parents[3];need(read(repo,'sources/preprints-tree.json')==treebytes,'root/copied complete-tree mismatch')
    need(parse(read(author,'inputs/sources/upstream.json'))['commit']==PIN,'source pin')
    blobs={e['path']:e['sha'] for e in tree['tree'] if e['type']=='blob'}
    sr=parse(read(author,'source-receipt.json'));need(sr['pin']==PIN and len(sr['entries'])==35,'source receipt')
    for e in sr['entries']:
        b=read(author,e['path']);gh=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        need(gh==e['git_blob']==blobs[e['upstream_path']],'Git blob mismatch')
        need(sha(b)==e['sha256'] and len(b)==e['bytes'],'source byte receipt')
        need(e['url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+e['upstream_path'],'unpinned URL')
    ar=parse(read(root,'authentication.json'))
    need(ar['author_manifest_sha256']==AUTHOR and ar['scope_sha256']==SCOPE and ar['candidate_sha256']==CANDIDATE,'review authentication linkage')
    need(ar['root_complete_tree_sha256']==sha(treebytes),'tree identity')
    prefix='preprints/A-negatively-pinched-Kahler-threefold-without-bounded-holomorphic-coordinates-September-25-2026/'
    actual={p for p in blobs if p.startswith(prefix) and not p.endswith('.pdf')}
    selected=[e for e in sr['entries'] if e['upstream_path'].startswith(prefix)]
    need(ar['relevant_family_text_blobs']==selected and len(selected)==12,'retained family entries')
    need(actual-{e['upstream_path'] for e in selected}=={prefix+'build/references.bib'} and len(actual)==13,'family reading inventory')
    status=parse(read(root,'status.json'))
    need(status['verdict']=='PASS_FULL_W5' and status['blocking_failures']==[] and status['full_original_scope_unchanged'] is True,'proof verdict binding')
    need(status['contribution_verdict'] is None and status['full_theorem_formalized'] is False and status['count_change']==0 and status['published'] is False,'gate boundary')
    print(json.dumps({'status':'IDENTITY_ONLY','recorded_verdict':'PASS_FULL_W5','review_payloads':n,'author_payloads':an,'pinned_blobs':35,'relevant_retained_blobs':12,'unretained_bibliography':1,'writes':0,'mathematics_executed':False,'count_change':0},sort_keys=True))

if __name__=='__main__':
    try:main()
    except (OSError,ValueError,TypeError,KeyError) as e:raise SystemExit('REJECT: '+str(e))
