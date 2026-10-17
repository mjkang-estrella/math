#!/usr/bin/env python3
"""Review-owned read-only exact inventory verifier.
Inventory primitives derived from the manuscript MIT verifier; preserved copyright
2026 Myeongjin Kang. New review checks original MIT code.
Read-only exact inventory verifier. Original code MIT.
Requires a detached seal SHA256 supplied outside this packet. Identity only.
Does not execute mathematical scripts or third-party/author code.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys

SCOPE='133c0d45fdd9f4a1c328dee664b142ac2cf09c6d0600fcc1ed53bdb565dea838'
COMMIT='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
EXTERNAL=[
 ('fresh-structural-discovery-r16','fc997d93ac553767e1ce252e73e57ffb3c675d36b09d1949c1e8a14f6f9db9af',35,8),
 ('complex-projector-borsuk-review-r1','c9527d05aff931a233962ef61a0f2de62d962a5fc3375735ac5afdcacdfaaa44',30,5),
 ('complex-projector-borsuk-contribution-r2','398bf6aea0b3d95ae36f10429279adf0f9472ec779a4192d8da6017536ac62a1',40,4),
 ('complex-projector-borsuk-contribution-r3','d4664c449265b527ab40b7146d500d8bd998379f57b5d852ff42f823854dc1ed',14,1)]
META=['manifest.json','seal.json']
def need(ok,why):
    if not ok:raise ValueError(why)
def digest(b):return hashlib.sha256(b).hexdigest()
def pairs(items):
    out={}
    for k,v in items:
        need(k not in out,'duplicate JSON key');out[k]=v
    return out
def parse(b):return json.loads(b,object_pairs_hook=pairs)
def safe_name(x,directory=False):
    need(isinstance(x,str) and x and '\\' not in x,'bad path')
    if directory and x=='.':return x
    p=PurePosixPath(x)
    need(not p.is_absolute() and p.as_posix()==x and all(v not in ('','..','.') for v in p.parts),'noncanonical path')
    need('__pycache__' not in p.parts and not x.endswith(('.pyc','.pyo')),'bytecode forbidden')
    return x
def no_symlink_ancestors(p):
    for q in [p,*p.parents]:need(not q.is_symlink(),'symlink ancestor')
def read(root,name):
    p=root/safe_name(name);no_symlink_ancestors(p)
    need(stat.S_ISREG(p.lstat().st_mode),'not a regular file')
    return p.read_bytes()
def inventory(root):
    no_symlink_ancestors(root);need(root.is_dir(),'missing root')
    files=set();dirs={'.'}
    for base,ds,fs in os.walk(root,followlinks=False):
        for name in ds:
            p=Path(base)/name;need(not p.is_symlink() and p.is_dir(),'unsafe directory')
            dirs.add(safe_name(p.relative_to(root).as_posix(),True))
        for name in fs:
            p=Path(base)/name;need(not p.is_symlink() and stat.S_ISREG(p.lstat().st_mode),'unsafe file')
            files.add(safe_name(p.relative_to(root).as_posix()))
    return files,dirs
def authenticate(root,anchor,counts=None):
    need(re.fullmatch('[0-9a-f]{64}',anchor) is not None,'bad external anchor')
    sb=read(root,'seal.json');need(digest(sb)==anchor,'external seal anchor mismatch')
    s=parse(sb);need(s['metadata']==META and s['scope_sha256']==SCOPE,'seal contract')
    mb=read(root,'manifest.json');need(len(mb)==s['manifest_size'] and digest(mb)==s['manifest_sha256'],'manifest identity')
    m=parse(mb);need(m['metadata']==META and m['upstream_commit']==COMMIT,'manifest contract')
    names=set()
    for e in m['files']:
        name=safe_name(e['path']);need(name not in names and name not in META,'duplicate/reserved member')
        names.add(name);b=read(root,name)
        need(len(b)==e['size'] and digest(b)==e['sha256'],'payload mismatch: '+name)
        need(bool(e['role']),'missing role')
    ds=[safe_name(x,True) for x in m['directories']]
    need(len(ds)==len(set(ds)) and '.' in ds,'duplicate/missing directory')
    actual_files,actual_dirs=inventory(root)
    need(actual_files==names|set(META) and actual_dirs==set(ds),'exact membership mismatch')
    need((len(actual_files),len(actual_dirs))==(s['owned_files'],s['owned_directories']),'count mismatch')
    if counts is not None:need(counts==(len(actual_files),len(actual_dirs)),'externally fixed count mismatch')
    return s,m

def audit(event,args):
    if event=='open':
        mode=args[1];flags=args[2]
        need(not isinstance(mode,str) or not any(c in mode for c in 'wax+'),'write forbidden')
        need(not isinstance(flags,int) or not flags & (os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND),'write flags forbidden')
    need(event not in {'os.remove','os.rename','os.mkdir','os.rmdir','os.chmod','os.symlink','os.link','os.truncate','subprocess.Popen','os.system'},'mutation/execution forbidden')
    need(not event.startswith('socket.'),'network forbidden')

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--seal-sha256',required=True);args=ap.parse_args()
    sys.addaudithook(audit)
    root=Path(__file__).absolute().parent
    s,m=authenticate(root,args.seal_sha256)
    need(s['status']=='PASS_MANUSCRIPT','review status')
    manuscript=root.parent/'complex-projector-borsuk-manuscript-r1'
    authenticate(manuscript,'4f3f038684c6359be5e4e63b990d5485b11eb33ffe7c5c1ec5aa15a37173d1f2',(37,6))
    for name,anchor,nf,nd in EXTERNAL:authenticate(root.parent/name,anchor,(nf,nd))
    repo=root.parents[3]
    inputs=parse(read(manuscript,'input-manifest.json'))['files']
    for e in inputs:
        b=read(repo,e['path']);need(len(b)==e['size'] and digest(b)==e['sha256'],'external input mismatch')
    extras=parse(read(root,'input-receipts.json'))['immutable_files']
    for e in extras:
        b=read(repo,e['path']);need(len(b)==e['size'] and digest(b)==e['sha256'],'extra input mismatch')
    pdf='rebuild/output/pdf/complex-projective-plane-borsuk-nine.pdf'
    need(digest(read(root,pdf))=='870941e2499b3005f13063694ce183d3c77fdbea6ead1263a3c3e49dd58a517b','rebuilt PDF')
    need(read(root,'rebuild/main.tex')==read(manuscript,'main.tex'),'rebuilt source')
    need(read(root,'appendix-replay.json')==read(manuscript,'checks/example-10-2-exact.json'),'exact appendix replay')
    qa=parse(read(root,'visual-review.json'))
    need(qa['pdf_sha256']==digest(read(root,pdf)) and [r['page'] for r in qa['pages']]==list(range(1,12)),'visual scope')
    for row in qa['pages']:
        need(row['inspected'] is True and digest(read(root,row['path']))==row['sha256'],'visual page identity')
    status=parse(read(root,'status.json'))
    need(status['verdict']=='PASS_MANUSCRIPT' and status['count_change']==0 and not status['published'],'status')
    need(not status['independent_formal_pass'] and not status['full_B8C_formalized'],'formal limits')
    print(json.dumps({'result':'INTEGRITY_OK_ONLY','review_files':s['owned_files'],'review_directories':s['owned_directories'],'manuscript_files':37,'predecessor_packages':4,'explicit_external_inputs':len(inputs),'extra_immutable_inputs':len(extras),'rebuilt_pdf_byte_identical':True,'visually_inspected_pages':11,'writes':0,'mathematical_program_run':False},sort_keys=True))
if __name__=='__main__':
    try:main()
    except Exception as e:raise SystemExit('INTEGRITY_REJECT: '+str(e))
