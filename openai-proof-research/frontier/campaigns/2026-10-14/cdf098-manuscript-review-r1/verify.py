#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT.
"""Read-only externally anchored independent manuscript-review inventory. Identity only, not proof.
Adapted from the reviewed manuscript MIT verifier; original attribution retained.
Does not execute any author, reviewer, formal or mathematical program.
"""
import argparse, hashlib, json, os, re, stat, sys
from pathlib import Path, PurePosixPath
SCOPE='bb115b9c504b9e5d8e3f62d841bc16095049f23719a47eb13d18d253ed1741c5'
COMMIT='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
META=['manifest.json','seal.json']
EXTERNAL=[
 ('fresh-parent-discovery-r8','f417cfd409e18a34c97f488fb10ebfa25f1b09b5fc4ff323c53c71cf71262c85',21),
 ('cdf098-proof-r1','543aba870bfb7237dcd95e2d03fd40e644350b7acbc9aa43cb90c08553a80dda',8),
 ('cdf098-contribution-r1','42befbcdc270f6802d47080dfba86ef105dcd9316a237324eb0a4a5355f4c691',106)]
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

def external_manifest(root,anchor,filename='manifest.json',expected_count=None,replay_exception=False):
    raw=read(root,filename);need(digest(raw)==anchor,'external manifest anchor mismatch')
    m=parse(raw);names=set()
    for e in m['files']:
        n=safe_name(e['path']);need(n not in names and n!=filename,'external duplicate/reserved')
        names.add(n);b=read(root,n)
        need(len(b)==e.get('bytes',e.get('size')) and digest(b)==e['sha256'],'external payload mismatch: '+n)
    ff=set();dd={'.'}
    for base,ds,fs in os.walk(root,followlinks=False):
        if replay_exception and Path(base)==root and '.replays' in ds:
            need(not (root/'.replays').is_symlink(),'replay symlink');ds.remove('.replays')
        for n in ds:
            p=Path(base)/n;need(not p.is_symlink() and p.is_dir(),'external unsafe directory')
            dd.add(safe_name(p.relative_to(root).as_posix(),True))
        for n in fs:
            p=Path(base)/n;need(not p.is_symlink() and stat.S_ISREG(p.lstat().st_mode),'external unsafe file')
            ff.add(safe_name(p.relative_to(root).as_posix()))
    need(ff==names|{filename} and dd==set(m['directories'])|{'.'},'external exact inventory mismatch')
    if expected_count is not None:need(len(names)==expected_count,'external count mismatch')
    return len(names)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--seal-sha256',required=True);args=ap.parse_args()
    sys.addaudithook(audit)
    review=Path(__file__).absolute().parent
    rs,rm=authenticate(review,args.seal_sha256)
    need(rs['status']=='PASS_MANUSCRIPT','review seal status')
    root=review.parent/'cdf098-manuscript-r1';repo=root.parents[3]
    s,m=authenticate(root,'14216c0f3656c05406225a7c5d87f652b8e7ef0d5fb358d3bef480dd5aafd881',(36,7))
    need(s['status']=='CDF098_MANUSCRIPT_R1_REVIEW_READY','status mismatch')
    counts={n:external_manifest(root.parent/n,a,expected_count=c) for n,a,c in EXTERNAL}
    author=root.parent/EXTERNAL[0][0]
    need(digest(read(author,'original-scope.md'))==SCOPE,'scope identity')
    need(digest(read(author,'candidate.md'))=='24c5d7055f19b48bac26451a87896845756865eeeba5d0502e1f7982ccb6f39a','candidate identity')
    source=parse(read(author,'source-receipt.json'));tree=parse(read(author,'family-inventory.json'))
    need(tree['pin']==COMMIT and tree['tree_truncated'] is False,'pinned source inventory')
    blobs={e['path']:e['sha'] for e in tree['entries'] if e['type']=='blob'}
    for e in source:
        b=read(author,e['local'])
        need(digest(b)==e['sha256'] and len(b)==e['bytes'],'source bytes')
        need(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']==blobs[e['path']],'source Git blob')
    fd=parse(read(root,'formal-dependency.json'))
    nf=external_manifest(root.parent/'cdf098-formal-v1',fd['manifest_sha256'],fd['manifest_file'],fd['payloads'],True)
    im=parse(read(root,'input-manifest.json'));seen=set()
    for e in im['files']:
        n=safe_name(e['path']);need(n not in seen,'duplicate external input');seen.add(n)
        b=read(repo,n);need(len(b)==e['bytes'] and digest(b)==e['sha256'],'external input changed: '+n)
    status=parse(read(root,'status.json'))
    need(status['count_change']==0 and status['published'] is False,'count/publication status')
    need(status['independent_manuscript_pass'] is False and status['full_CDF098_formalized'] is False,'review/formal scope')
    br=parse(read(root,'checks/build-receipt.json'));vr=parse(read(root,'checks/visual-review.json'))
    ph=digest(read(root,'output/pdf/doubling-rectifiable-nonembedding-curves.pdf'))
    need(br['source_sha256']==digest(read(root,'main.tex')) and br['formal_support_sha256']==digest(read(root,'formal-support.tex')),'build source linkage')
    need(br['pdf_sha256']==ph==vr['pdf_sha256'],'PDF/QA linkage')
    need(br['pdf_pages']==br['rendered_pages']==len(vr['pages'])==9,'page count')
    need([x['number'] for x in vr['pages']]==list(range(1,10)),'page coverage')
    for e in vr['pages']:need(digest(read(root,e['path']))==e['sha256'] and e['visual_defects']==[],'page QA linkage')
    need(all(br['log_findings'][x]==0 for x in ('overfull_boxes','undefined','rerun')),'typesetting checks')
    seen_review=set()
    for e in parse(read(review,'input-receipts.json')):
        n=safe_name(e['path']);need(n not in seen_review,'duplicate review input');seen_review.add(n)
        b=read(repo,n);need(len(b)==e['size'] and digest(b)==e['sha256'],'review input changed: '+n)
    rv=parse(read(review,'status.json'))
    need(rv['verdict']=='PASS_MANUSCRIPT' and rv['required_repairs']==[] and rv['full_frozen_scope_preserved'] is True,'review verdict')
    need(rv['independent_formal_pass'] is False and rv['full_theorem_formalized'] is False and rv['count_change']==0 and rv['published'] is False,'review boundary')
    for n in ('main.tex','formal-support.tex','support/build.py'):
        need(read(review,'rebuild/'+n)==read(root,n),'rebuild input changed: '+n)
    rb=parse(read(review,'rebuild/checks/build-receipt.json'));qa=parse(read(review,'visual-qa.json'))
    pdf=read(review,'rebuild/output/pdf/doubling-rectifiable-nonembedding-curves.pdf')
    need(digest(pdf)==ph==rb['pdf_sha256']==qa['pdf_sha256'],'rebuilt PDF mismatch')
    need(rb['source_sha256']==digest(read(root,'main.tex')) and rb['formal_support_sha256']==digest(read(root,'formal-support.tex')),'rebuild source linkage')
    need(rb['pdf_pages']==rb['rendered_pages']==9 and qa['all_nine_inspected'] is True,'rebuild page count')
    need([x['number'] for x in qa['pages']]==list(range(1,10)),'review page coverage')
    for e in qa['pages']:
        need(digest(read(review,e['path']))==e['sha256'] and e['defects']==[],'review page linkage')
        need(read(review,e['path'])==read(root,'checks/pages/page-'+str(e['number'])+'.png'),'rendered page identity')
    need(all(rb['log_findings'][x]==0 for x in ('overfull_boxes','undefined','rerun')),'rebuild diagnostics')
    print(json.dumps({'result':'INTEGRITY_ONLY','review_files':rs['owned_files'],'review_directories':rs['owned_directories'],'manuscript_files':s['owned_files'],'external_payloads':counts,'formal_payloads':nf,'review_inputs':len(seen_review),'identical_pdf_pages':9,'writes':0,'mathematical_program_executed':False,'formal_PASS':False,'count_changed':False},sort_keys=True))
if __name__=='__main__':
    try:main()
    except (ValueError,KeyError,OSError,TypeError) as exc:raise SystemExit('REJECT: '+str(exc))
