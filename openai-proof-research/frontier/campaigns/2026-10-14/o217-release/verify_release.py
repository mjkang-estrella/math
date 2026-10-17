#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT.
"""Read-only outer preparation seal, including the portable ZIP and test receipts."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat
import sys
sys.dont_write_bytecode=True
import zipfile

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

def audit(event,args):
    if event=='open':
        mode,flags=args[1:3]
        need(not isinstance(mode,str) or not any(c in mode for c in 'wax+'),'write forbidden')
        need(not isinstance(flags,int) or not flags & (os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND),'write flags forbidden')
    need(event not in {'os.remove','os.rename','os.mkdir','os.rmdir','os.chmod','os.symlink','os.link','os.truncate','subprocess.Popen','os.system'},'mutation/execution forbidden')
    need(not event.startswith('socket.'),'network forbidden')

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--seal-sha256',required=True);a=ap.parse_args()
    sys.addaudithook(audit)
    root=Path(__file__).absolute().parent
    for p in [root,*root.parents]:need(not p.is_symlink(),'symlink ancestor')
    nodes=list(root.rglob('*'));need(not any(p.is_symlink() for p in nodes),'symlink entry')
    need(all(stat.S_ISREG(p.lstat().st_mode) or p.is_dir() for p in nodes),'special entry')
    read=lambda n:(root/safe(n)).read_bytes()
    sb=read('seal.json');need(sha(sb)==a.seal_sha256,'external seal mismatch');s=parse(sb)
    mb=read('manifest.json');need(sha(mb)==s['manifest_sha256'],'manifest mismatch');m=parse(mb)
    names=set();dirs={str(p.relative_to(root)) for p in nodes if p.is_dir()}
    for row in m['files']:
        n=safe(row['path']);need(n not in names and n not in ('manifest.json','seal.json'),'duplicate/reserved file');names.add(n)
        b=read(n);need(len(b)==row['bytes'] and sha(b)==row['sha256'],'payload mismatch: '+n)
    need({str(p.relative_to(root)) for p in nodes if p.is_file()}==names|{'manifest.json','seal.json'},'exact file membership')
    need(dirs==set(m['directories']) and len(dirs)==len(m['directories']),'exact directory membership')
    need(s['status']=='RELEASE_PREPARATION_COMPLETE' and len(names)==s['payloads'],'seal status/count')
    receipt=parse(read('checks/release-receipt.json'))
    need(receipt['accepted'] is False and receipt['published'] is False and receipt['count_change']==0 and receipt['full_O217_formalized'] is False,'scope boundary')
    archive=read(receipt['archive']);need(sha(archive)==receipt['archive_sha256'] and len(archive)==receipt['archive_bytes'],'archive identity')
    # Import only locally authenticated helper bytes, after outer authentication.
    sys.path.insert(0,str(root))
    from verify_bundle import verify
    from bundle_common import safe as bundle_safe
    with zipfile.ZipFile(root/receipt['archive']) as z:
        zs=z.namelist();need(len(zs)==len(set(zs)),'duplicate ZIP')
        for info in z.infolist():bundle_safe(info.filename);need(stat.S_ISREG(info.external_attr>>16),'ZIP special entry')
        count=verify(z.read,zs,receipt['bundle_manifest_sha256'],receipt['gate_sha256'])
        need(count==receipt['bundle_files'] and count>140,'bundle count')
        need(z.read('FINAL-GATE.json')==read('FINAL-GATE.json'),'local gate drift')
        # Release helpers/docs included at the ZIP root must still match local preparation bytes.
        for n in zs:
            if '/' not in n and n!='BUNDLE-MANIFEST.json':need(z.read(n)==read(n),'local release file drift: '+n)
    rb=read(receipt['release_checks']);need(sha(rb)==receipt['release_checks_sha256'],'test receipt identity');tests=parse(rb)
    need(tests['status']=='PASS_RELEASE_CHECKS' and tests['archive_sha256']==receipt['archive_sha256'],'tested archive mismatch')
    need(tests['manifest_sha256']==receipt['bundle_manifest_sha256'] and tests['gate_sha256']==receipt['gate_sha256'],'test anchors')
    need(tests['deterministic_reassembly_byte_identical'] is True and tests['Lean_rebuilt'] is False,'test scope')
    need(len(tests['cases'])==receipt['cases']==20,'test count')
    for c in tests['cases']:
        need((c['exit_code']==0)==(c['expected']=='ACCEPT'),'test exit contract')
        for ext in ['stdout','stderr']:
            data=read('output/release-checks/'+c['case']+'.'+ext)
            need(sha(data)==c[ext+'_sha256'],'test output drift')
        if c['reason_checked']:
            text=read('output/release-checks/'+c['case']+'.stdout')+read('output/release-checks/'+c['case']+'.stderr')
            need(c['reason_checked'].encode() in text,'failure reason missing')
    need(len(tests['fresh_render_pages'])==receipt['pdf_pages']>0 and all(e['identical_to_reviewed_page'] for e in tests['fresh_render_pages']),'page evidence')
    need(tests['fresh_pdf_sha256']==receipt['fresh_pdf_sha256'],'PDF identity')
    print(json.dumps({'result':'INTEGRITY_ONLY','release_payloads':len(names),'bundle_files':count,'cases':20,'pdf_pages_identical':True,'accepted':False,'published':False,'count_change':0,'writes':0},sort_keys=True))

if __name__=='__main__':
    try:main()
    except (OSError,ValueError,TypeError,KeyError,zipfile.BadZipFile) as e:raise SystemExit('REJECT: '+str(e))
