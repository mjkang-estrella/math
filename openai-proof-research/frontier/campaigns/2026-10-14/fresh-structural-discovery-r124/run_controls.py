#!/usr/bin/env python3
"""Original copied integrity controls. Not mathematical tests."""
import sys
sys.dont_write_bytecode=True
import argparse, hashlib, json, os, shutil, stat, subprocess
from pathlib import Path

def sha(b):return hashlib.sha256(b).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def snapshot(root,exclude=None):
    out={}
    for q in [root,*root.rglob('*')]:
        if exclude and (q==exclude or exclude in q.parents):continue
        t=q.lstat();item={'mode':t.st_mode,'links':t.st_nlink}
        if stat.S_ISREG(t.st_mode):item['sha256']=sha(q.read_bytes())
        elif stat.S_ISLNK(t.st_mode):item['target']=os.readlink(q)
        out[q.relative_to(root).as_posix()]=item
    # Root directory link count changes upon adding the designated output child.
    if exclude:out['.'].pop('links',None)
    return out

def reseal(root):
    p=root/'packet';m=json.loads((p/'MANIFEST.json').read_text())
    m['files']=[];m['directories']=[]
    for q in sorted(p.rglob('*')):
        rel=q.relative_to(p).as_posix();t=q.lstat()
        if stat.S_ISDIR(t.st_mode):m['directories'].append({'path':rel,'mode':stat.S_IMODE(t.st_mode)})
        elif rel!='MANIFEST.json':m['files'].append({'path':rel,'size':t.st_size,'sha256':sha(q.read_bytes()),'mode':stat.S_IMODE(t.st_mode)})
    dump(p/'MANIFEST.json',m)
    f=json.loads((root/'FINAL.json').read_text());f['manifest_sha256']=sha((p/'MANIFEST.json').read_bytes());dump(root/'FINAL.json',f)
    return sha((root/'FINAL.json').read_bytes())

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',required=True);ap.add_argument('--finalhash',required=True);ap.add_argument('--reporthash',required=True);ap.add_argument('--output',required=True);a=ap.parse_args()
    root=Path(a.root).absolute();out=Path(a.output)
    if not out.is_absolute():out=root/out
    out=out.absolute()
    if out.parent!=root or out.exists() or out.name in {'packet','.','..'}:raise ValueError('output must be fresh direct OWN-root child')
    for p in [root,*root.parents]:
        if p.is_symlink():raise ValueError('symlink root')
    # Authenticate the original before any copying.
    cmd=[sys.executable,'-B',str(root/'verify.py'),'--root',str(root),'--finalhash',a.finalhash,'--reporthash',a.reporthash]
    check=subprocess.run(cmd,capture_output=True,text=True)
    if check.returncode:raise RuntimeError('original authentication failed: '+check.stderr)
    before=snapshot(root,out);out.mkdir()
    rows=[]
    payload='packet/public/packing-feasibility.md'
    cases=[('baseline',True,None),('wrong-final',False,'detached FINAL'),('wrong-report',False,'detached REPORT'),('missing-final-argument',False,'required'),('changed-payload',False,'payload identity'),('missing-payload',False,'membership'),('extra-payload',False,'membership'),('extra-directory',False,'directory membership'),('payload-symlink',False,'not regular'),('directory-symlink',False,'symlink directory'),('fifo',False,'not regular'),('hardlink',False,'hardlink'),('changed-report',False,'detached REPORT'),('changed-final',False,'detached FINAL'),('changed-manifest',False,'manifest binding'),('changed-verifier',False,'verifier binding'),('changed-controls',False,'control program binding'),('root-symlink',False,'root/ancestor symlink'),('denial-write',False,'DENIED write'),('denial-process',False,'DENIED mutation/process'),('NEW-TEST-source-url',False,'pinned raw URL'),('NEW-TEST-full-record',False,'FULL canonical record'),('NEW-TEST-primary-receipt',False,'primary artifact'),('NEW-TEST-unsafe-path',False,'unsafe path'),('NEW-TEST-duplicate-file',False,'duplicate/reserved'),('NEW-TEST-tree',False,'complete tree bytes')]
    for name,want,reason in cases:
        case=out/name;case.mkdir();copy=case/'root';copy.mkdir()
        shutil.copytree(root/'packet',copy/'packet')
        for n in ['FINAL.json','REPORT.md','verify.py','run_controls.py']:shutil.copyfile(root/n,copy/n)
        fhash=a.finalhash;rhash=a.reporthash;rootarg=copy;extra=[];missing=False
        target=copy/payload
        if name=='wrong-final':fhash='0'*64
        elif name=='wrong-report':rhash='0'*64
        elif name=='missing-final-argument':missing=True
        elif name=='changed-payload':target.write_bytes(target.read_bytes()+b'\nchanged\n')
        elif name=='missing-payload':target.unlink()
        elif name=='extra-payload':(copy/'packet/public/EXTRA').write_text('x')
        elif name=='extra-directory':(copy/'packet/public/EXTRA').mkdir()
        elif name=='payload-symlink':target.unlink();target.symlink_to('report.md')
        elif name=='directory-symlink':
            (copy/'packet/public').rename(copy/'holding');(copy/'packet/public').symlink_to('../holding',target_is_directory=True)
        elif name=='fifo':target.unlink();os.mkfifo(target)
        elif name=='hardlink':os.link(target,copy/'second-link')
        elif name=='changed-report':(copy/'REPORT.md').write_text('changed')
        elif name=='changed-final':(copy/'FINAL.json').write_bytes((copy/'FINAL.json').read_bytes()+b' ')
        elif name=='changed-manifest':(copy/'packet/MANIFEST.json').write_bytes((copy/'packet/MANIFEST.json').read_bytes()+b' ')
        elif name=='changed-verifier':(copy/'verify.py').write_bytes((copy/'verify.py').read_bytes()+b'\n# changed\n')
        elif name=='changed-controls':(copy/'run_controls.py').write_bytes((copy/'run_controls.py').read_bytes()+b'\n# changed\n')
        elif name=='root-symlink':rootarg=case/'alias';rootarg.symlink_to('root',target_is_directory=True)
        elif name.startswith('denial-'):extra=['--probe',name.split('-')[1]]
        elif name in {'NEW-TEST-source-url','NEW-TEST-full-record'}:
            q=copy/'packet/private/canonical.json';data=json.loads(q.read_text());x=next(x for x in data if x['retained'])
            if name=='NEW-TEST-source-url':x['url']=x['url'].replace('fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','0000000000000000000000000000000000000000')
            else:x['record']['mode']='100755'
            for n in ['private/canonical.json','public/source-register.json']:dump(copy/'packet'/n,data)
            fhash=reseal(copy)
        elif name=='NEW-TEST-primary-receipt':
            data=json.loads((copy/'packet/private/primary/acquisition.json').read_text());next(x for x in data if x.get('retained') and 'pdf' in x)['text_sha256']='0'*64
            for n in ['private/primary/acquisition.json','public/primary-register.json']:dump(copy/'packet'/n,data)
            fhash=reseal(copy)
        elif name in {'NEW-TEST-unsafe-path','NEW-TEST-duplicate-file'}:
            q=copy/'packet/MANIFEST.json';m=json.loads(q.read_text())
            if name=='NEW-TEST-unsafe-path':m['files'][0]['path']='../outside'
            else:m['files'].append(m['files'][0])
            dump(q,m);f=json.loads((copy/'FINAL.json').read_text());f['manifest_sha256']=sha(q.read_bytes());dump(copy/'FINAL.json',f);fhash=sha((copy/'FINAL.json').read_bytes())
        elif name=='NEW-TEST-tree':
            q=copy/'packet/private/context/sources/preprints-tree.json';t=json.loads(q.read_text());t['truncated']=True;dump(q,t);fhash=reseal(copy)
        inputs_before=snapshot(case)
        command=[sys.executable,'-B',str(copy/'verify.py'),'--root',str(rootarg),'--reporthash',rhash]
        if not missing:command+=['--finalhash',fhash]
        command+=extra
        result=subprocess.run(command,capture_output=True,text=True,timeout=40)
        unchanged=inputs_before==snapshot(case)
        passed=(result.returncode==0)==want and unchanged and (reason is None or reason in result.stderr)
        rows.append({'case':name,'expected_accept':want,'returncode':result.returncode,'stderr':result.stderr.strip(),'stdout':result.stdout.strip(),'input_unchanged':unchanged,'expected_result_observed':passed,'anchor_kind':'deliberate NEW TEST anchor' if name.startswith('NEW-TEST') else 'original detached anchors (or specified missing/wrong anchor)'} )
        shutil.rmtree(case)
        if not passed:raise RuntimeError('control failed: '+json.dumps(rows[-1]))
    after=snapshot(root,out);unchanged=before==after
    receipt={'purpose':'integrity only; no mathematical gate','cases':rows,'case_count':len(rows),'all_expected':all(x['expected_result_observed'] for x in rows),'original_unchanged':unchanged,'original_snapshot_sha256':sha(json.dumps(before,sort_keys=True).encode()),'final_sha256':a.finalhash,'report_sha256':a.reporthash,'limits':'Snapshot excludes only this fresh output child and the root directory link count affected by creating it. Directory/file modes, existing link counts and bytes otherwise compared. Audit probes are ordinary Python denials, not security sandbox proofs. NEW TEST anchors are not authentic-archive claims.'}
    dump(out/'receipt.json',receipt)
    if not unchanged:raise RuntimeError('original root changed')
    print(json.dumps({'case_count':len(rows),'all_expected':True,'original_unchanged':True,'receipt':str(out/'receipt.json'),'receipt_sha256':sha((out/'receipt.json').read_bytes())}))

if __name__=='__main__':main()
