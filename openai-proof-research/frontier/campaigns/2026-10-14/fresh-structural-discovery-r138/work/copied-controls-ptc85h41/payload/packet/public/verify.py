#!/usr/bin/env python3
"""Read-only r138 artifact verifier; pass three full detached SHA256 anchors.
No network, local imports, subprocess, file writes, or mathematical verdict.
"""
import argparse, hashlib, json, os, stat, sys
from pathlib import Path, PurePosixPath
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TREE='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
PREFIX='frontier/campaigns/2026-10-14/'
OLD={
 'fresh-structural-discovery-r137':{
  'FINAL.json':'9537d5941bfa2408e23195a2bbfb1d2eebbfd1cefedc2b5e9f6eb8b5b6be1962',
  'packet/MANIFEST.json':'5e0d09cfca28d5e402274ce72ed9115c0ab2eab432124c5143cff3d2c6e103fb',
  'REPORT.md':'0c3ef87b9687d093a75d0ec0a08ce2df3dad45ccc307a7ab5a48f00fa52cfaf4'},
 'fresh-structural-discovery-r136':{
  'FINAL.json':'1c53d5afb3d6fb8b72b17d64e1b10e20af857aad7144927f285cb90869ba7dec',
  'packet/MANIFEST.json':'d778dd807176909cfde8721ceccf14b8cf5b7ab7cdd1cf58355b2a9259295e36',
  'REPORT.md':'36c5a124cd535e04a2dbf5098d0376bfeb3c51452b3b19c29cad18b8bb4a29b9'}}
EXCLUDED={'fresh-arithmetic-discovery-r102','t088p133-manuscript-review-r1','t088p133-manuscript-r2','t088p133-manuscript-review-r2'}
def require(ok,msg):
    if not ok:raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def rel(s):
    t=PurePosixPath(s)
    require(not t.is_absolute() and '..' not in t.parts and str(t)==s,'unsafe relative path')
    require(not EXCLUDED.intersection(t.parts),'excluded input path')
    return Path(s)
def regular(p):
    st=p.lstat();require(stat.S_ISREG(st.st_mode) and st.st_nlink==1,'nonregular/symlink/hardlink: '+str(p))
    return p.read_bytes()
def anchored(p,h):
    require(len(h)==64 and all(c in '0123456789abcdef' for c in h),'full SHA256 required')
    b=regular(p);require(sha(b)==h,'detached anchor mismatch: '+str(p));return b
def inventory(p):
    require(p.is_dir() and not p.is_symlink(),'packet directory type')
    ff={};dd={'.':stat.S_IMODE(p.stat().st_mode)}
    for base,dirs,files in os.walk(p,followlinks=False):
        for n in dirs:
            q=Path(base)/n;st=q.lstat();require(stat.S_ISDIR(st.st_mode),'non-directory in packet')
            dd[q.relative_to(p).as_posix()]=stat.S_IMODE(st.st_mode)
        for n in files:
            q=Path(base)/n;b=regular(q);s=q.relative_to(p).as_posix()
            if s!='MANIFEST.json':ff[s]=dict(bytes=len(b),sha256=sha(b),mode=stat.S_IMODE(q.stat().st_mode))
    return ff,dd
def sealed(r,anchors):
    f=json.loads(anchored(r/'FINAL.json',anchors['FINAL.json']))
    m=json.loads(anchored(r/'packet/MANIFEST.json',anchors['packet/MANIFEST.json']))
    anchored(r/'REPORT.md',anchors['REPORT.md'])
    require(f['manifest_sha256']==anchors['packet/MANIFEST.json'] and f['report_sha256']==anchors['REPORT.md'],'FINAL binding')
    require(f['status']=='PREFREEZE/no nominee' and f['scope_frozen'] is False,'status metadata')
    files,dirs=inventory(r/'packet');require(files==m['files'] and dirs==m['directories'],'packet inventory/content/mode mismatch')
    return len(files)
def bind(r,p,regs,allow_observation=False):
    require(len({e['path'] for e in regs})==len(regs),'duplicate named input')
    stable=0
    for e in regs:
        copies=[r/rel(e['copy'])]
        if not allow_observation or e.get('role')!='observation':copies.append(p/rel(e['path']));stable+=1
        for f in copies:
            b=regular(f);require(sha(b)==e['sha256'] and len(b)==e['bytes'],'named input mismatch: '+str(f))
    return stable
def sources(r,entries,items):
    for e in items:
        b=regular(r/rel(e['local']));t=entries[e['path']]
        require(len(b)==e.get('size',e.get('bytes'))==t['size'] and sha(b)==e['sha256'],'source size/SHA256')
        gh=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        require(gh==e['sha']==t['sha'],'source Git blob')
        require(e['url_raw']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+e['path'],'source pinned URL')
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root',required=True,type=Path);ap.add_argument('--project',required=True,type=Path)
    for n in ['final','manifest','report']:ap.add_argument('--'+n+'-sha256',required=True)
    a=ap.parse_args();r=a.root.absolute();p=a.project.absolute();pr=r/'packet/private'
    anchors={'FINAL.json':a.final_sha256,'packet/MANIFEST.json':a.manifest_sha256,'REPORT.md':a.report_sha256}
    count=sealed(r,anchors)
    oldcounts={name:sealed(p/PREFIX/name,anchors) for name,anchors in OLD.items()}
    regs=json.loads(regular(pr/'input-bindings.json'))['files'];stable=bind(r,p,regs,True)
    te=next(e for e in regs if e['path']=='sources/preprints-tree.json')
    tb=regular(r/rel(te['copy']));require(sha(tb)==TREE,'tree SHA256');t=json.loads(tb)
    require(t['truncated'] is False and len(t['tree'])==13223,'tree extent')
    entries={e['path']:e for e in t['tree']};require(len(entries)==13223,'duplicate tree paths')
    sc=json.loads(regular(pr/'source-authentication.json'));sources(r,entries,sc)
    for e in json.loads(regular(pr/'new-primary-authentication.json')):
        b=regular(r/rel(e['local']));require(sha(b)==e['sha256'] and len(b)==e['bytes'],'new primary identity')
    old=p/PREFIX/'fresh-structural-discovery-r137';op=old/'packet/private'
    oldregs=json.loads(regular(op/'input-bindings.json'))['files'];bind(old,p,oldregs)
    osrc=json.loads(regular(op/'source-authentication.json'));sources(old,entries,osrc)
    primaries=json.loads(regular(op/'primary-authentication.json'))
    for e in primaries:
        b=op/'primary'/rel(e['name']);pdf=regular(b.with_suffix('.pdf'));txt=regular(b.with_suffix('.txt'))
        require(len(pdf)==e['bytes'] and sha(pdf)==e['sha256'] and sha(txt)==e['text_sha256'],'r137 primary identity')
    print(json.dumps(dict(artifact_integrity='verified',mathematical_gate='none',payload_files=count,
        original_payloads=oldcounts,stable_named_inputs=stable,archival_observations=len(regs)-stable,
        selected_source_blobs=len(sc),r137_source_blobs=len(osrc),r137_primary_versions=len(primaries),new_primary_versions=1),sort_keys=True))
if __name__=='__main__':
    try:main()
    except (ValueError,OSError,KeyError,TypeError,StopIteration) as e:
        print('VERIFICATION FAILED: '+str(e),file=sys.stderr);sys.exit(1)
