#!/usr/bin/env python3
"""Read-only r137 artifact verifier. Requires three externally supplied SHA256s.
No network, subprocess, local imports, file writes, or mathematical verdict.
Run with python -B.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat
import sys

PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
TREE='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
OLD='frontier/campaigns/2026-10-14/fresh-structural-discovery-r136'
OLD_ANCHORS={
 'FINAL.json':'1c53d5afb3d6fb8b72b17d64e1b10e20af857aad7144927f285cb90869ba7dec',
 'packet/MANIFEST.json':'d778dd807176909cfde8721ceccf14b8cf5b7ab7cdd1cf58355b2a9259295e36',
 'REPORT.md':'36c5a124cd535e04a2dbf5098d0376bfeb3c51452b3b19c29cad18b8bb4a29b9'}
ACTIVE={'t088p133-formal-review-r1','t088p133-manuscript-r1'}


def require(ok, msg):
    if not ok: raise ValueError(msg)


def sha(b):
    return hashlib.sha256(b).hexdigest()


def rel(s):
    p=PurePosixPath(s)
    require(not p.is_absolute() and '..' not in p.parts and str(p)==s,'unsafe path')
    require(not ACTIVE.intersection(p.parts),'active path prohibited')
    return Path(s)


def regular(p):
    st=p.lstat()
    require(stat.S_ISREG(st.st_mode) and st.st_nlink==1,'nonregular/symlink/hardlink: '+str(p))
    return p.read_bytes()


def anchored(p,h):
    require(len(h)==64 and all(c in '0123456789abcdef' for c in h),'full SHA256 required')
    b=regular(p)
    require(sha(b)==h,'detached anchor mismatch: '+str(p))
    return b


def inventory(packet):
    require(packet.is_dir() and not packet.is_symlink(),'packet directory type')
    files={}; dirs={'.':stat.S_IMODE(packet.stat().st_mode)}
    for base,dd,ff in os.walk(packet,followlinks=False):
        for n in dd:
            p=Path(base)/n; st=p.lstat()
            require(stat.S_ISDIR(st.st_mode),'non-directory in tree')
            dirs[p.relative_to(packet).as_posix()]=stat.S_IMODE(st.st_mode)
        for n in ff:
            p=Path(base)/n;s=p.relative_to(packet).as_posix();b=regular(p)
            if s!='MANIFEST.json':
                files[s]={'bytes':len(b),'sha256':sha(b),'mode':stat.S_IMODE(p.stat().st_mode)}
    return files,dirs


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root',type=Path,required=True)
    ap.add_argument('--project',type=Path,required=True)
    for s in ('final','manifest','report'):ap.add_argument('--'+s+'-sha256',required=True)
    a=ap.parse_args();r=a.root.absolute();p=a.project.absolute();pr=r/'packet/private'
    final=json.loads(anchored(r/'FINAL.json',a.final_sha256))
    manifest=json.loads(anchored(r/'packet/MANIFEST.json',a.manifest_sha256))
    anchored(r/'REPORT.md',a.report_sha256)
    require(final['manifest_sha256']==a.manifest_sha256 and final['report_sha256']==a.report_sha256,'FINAL bindings')
    require(final['status']=='PREFREEZE/no nominee' and final['scope_frozen'] is False,'outcome metadata')
    ff,dd=inventory(r/'packet')
    require(ff==manifest['files'] and dd==manifest['directories'],'packet inventory/content/mode mismatch')
    for name,h in OLD_ANCHORS.items():anchored(p/OLD/rel(name),h)
    oldm=json.loads(regular(p/OLD/'packet/MANIFEST.json'))
    of,od=inventory(p/OLD/'packet')
    require(of==oldm['files'] and od==oldm['directories'],'original r136 sealed packet changed')
    regs=json.loads(regular(pr/'input-bindings.json'))['files']
    require(len({e['path'] for e in regs})==len(regs),'duplicate input binding')
    for e in regs:
        for f in (p/rel(e['path']),r/rel(e['copy'])):
            b=regular(f);require(sha(b)==e['sha256'] and len(b)==e['bytes'],'bound input mismatch: '+str(f))
    tdata=regular(pr/'inputs/02-preprints-tree.json')
    require(sha(tdata)==TREE,'complete tree SHA256')
    tree=json.loads(tdata)
    require(tree['truncated'] is False and len(tree['tree'])==13223,'complete tree extent')
    entries={e['path']:e for e in tree['tree']}
    sources=json.loads(regular(pr/'source-authentication.json'))
    for e in sources:
        b=regular(r/rel(e['local']));tt=entries[e['path']]
        require(len(b)==e['size']==tt['size'] and sha(b)==e['sha256'],'source size/SHA256')
        blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        require(blob==e['sha']==tt['sha'],'source Git blob')
        require(e['url_raw']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+e['path'],'source pinned URL')
    primaries=json.loads(regular(pr/'primary-authentication.json'))
    for e in primaries:
        base=pr/'primary'/rel(e['name']);pdf=regular(base.with_suffix('.pdf'));txt=regular(base.with_suffix('.txt'))
        require(len(pdf)==e['bytes'] and sha(pdf)==e['sha256'] and sha(txt)==e['text_sha256'],'primary byte identity')
    print(json.dumps({'artifact_integrity':'verified','payload_files':len(ff),
        'stable_named_inputs':len(regs),'original_r136_payloads':len(of),
        'pinned_source_blobs':len(sources),'primary_versions':len(primaries),
        'mathematical_gate':'none'},sort_keys=True))


if __name__=='__main__':
    try:main()
    except (ValueError,OSError,KeyError,TypeError) as e:
        print('VERIFICATION FAILED: '+str(e),file=sys.stderr);sys.exit(1)
