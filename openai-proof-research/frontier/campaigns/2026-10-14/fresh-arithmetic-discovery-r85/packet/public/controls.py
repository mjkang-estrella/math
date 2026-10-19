#!/usr/bin/env python3
"""MIT. Mutations on disposable owned copies; integrity only."""
import argparse,hashlib,json,os,shutil,stat,subprocess,sys,tempfile
from pathlib import Path

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def snapshot(root):
    out={}
    for p in sorted(root.rglob('*')):
        r=p.relative_to(root)
        if r.parts[0]=='controls-work' or r.as_posix()=='controls.json':continue
        s=p.lstat();v=[stat.S_IFMT(s.st_mode),stat.S_IMODE(s.st_mode),s.st_nlink]
        if p.is_symlink():v.append(os.readlink(p))
        elif p.is_file():v.extend([s.st_size,sha(p)])
        out[r.as_posix()]=v
    return out

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',required=True,type=Path);ap.add_argument('--tree',required=True,type=Path)
    ap.add_argument('--finalhash',required=True);ap.add_argument('--reporthash',required=True);a=ap.parse_args()
    root=a.root.resolve();verifier=root/'packet/public/verify.py';before=snapshot(root)
    scratch=root/'controls-work';scratch.mkdir(exist_ok=True);results=[]
    names=['baseline','wrong-final','wrong-report','missing-final-option','extra-file','extra-directory','missing-payload','changed-payload','symlink','hardlink','changed-manifest','changed-report','changed-verifier','wrong-external-tree','coherent-reseal','changed-final']
    for name in names:
        with tempfile.TemporaryDirectory(prefix='case-',dir=scratch) as tmp:
            q=Path(tmp)/'copy';q.mkdir();shutil.copytree(root/'packet',q/'packet')
            for fn in ['FINAL.json','MANIFEST.json','REPORT.md']:shutil.copyfile(root/fn,q/fn)
            fh=a.finalhash;rh=a.reporthash;tree=a.tree;expect=''
            target=q/'packet/public/report.md'
            if name=='wrong-final':fh='0'*64;expect='FINAL anchor mismatch'
            elif name=='wrong-report':rh='0'*64;expect='REPORT anchor mismatch'
            elif name=='missing-final-option':expect='--finalhash'
            elif name=='extra-file':(q/'packet/extra.txt').write_text('extra');expect='packet files/hash/size mismatch'
            elif name=='extra-directory':(q/'packet/extra').mkdir();expect='packet directory membership mismatch'
            elif name=='missing-payload':target.unlink();expect='packet files/hash/size mismatch'
            elif name=='changed-payload':target.write_bytes(target.read_bytes()+b'changed');expect='packet files/hash/size mismatch'
            elif name=='symlink':target.unlink();target.symlink_to('screens.md');expect='symlink'
            elif name=='hardlink':target.unlink();os.link(q/'packet/public/screens.md',target);expect='hardlink'
            elif name=='changed-manifest':(q/'MANIFEST.json').write_bytes((q/'MANIFEST.json').read_bytes()+b' ');expect='manifest anchor mismatch'
            elif name=='changed-report':(q/'REPORT.md').write_bytes((q/'REPORT.md').read_bytes()+b' ');expect='REPORT anchor mismatch'
            elif name=='changed-verifier':(q/'packet/public/verify.py').write_text('print("forged success")\n');expect='packet files/hash/size mismatch'
            elif name=='wrong-external-tree':tree=Path(tmp)/'tree.json';tree.write_text('{"truncated":true,"tree":[]}');expect='external tree anchor mismatch'
            elif name=='coherent-reseal':
                target.write_bytes(target.read_bytes()+b'changed')
                m=json.loads((q/'MANIFEST.json').read_text());m['files']['public/report.md']={'sha256':sha(target),'bytes':target.stat().st_size}
                (q/'MANIFEST.json').write_text(json.dumps(m))
                f=json.loads((q/'FINAL.json').read_text());f['manifest_sha256']=sha(q/'MANIFEST.json');(q/'FINAL.json').write_text(json.dumps(f));expect='FINAL anchor mismatch'
            elif name=='changed-final':(q/'FINAL.json').write_bytes((q/'FINAL.json').read_bytes()+b' ');expect='FINAL anchor mismatch'
            cmd=[sys.executable,'-B',str(verifier),'--root',str(q),'--reporthash',rh,'--tree',str(tree)]
            if name!='missing-final-option':cmd+=['--finalhash',fh]
            r=subprocess.run(cmd,capture_output=True,text=True);combined=r.stdout+r.stderr
            ok=(r.returncode==0) if name=='baseline' else (r.returncode!=0 and expect in combined)
            results.append({'case':name,'expected':'accept' if name=='baseline' else 'reject','exit':r.returncode,'expected_diagnostic':expect,'matched':ok,'output':combined.strip()})
            if not ok:raise RuntimeError('control failed '+name+': '+combined)
    after=snapshot(root)
    if before!=after:raise RuntimeError('original root changed')
    receipt={'controls':results,'original_root_unchanged':True,'snapshot_exclusions':['controls-work/','controls.json'],'snapshot_sha256':hashlib.sha256(json.dumps(before,sort_keys=True).encode()).hexdigest(),'final_sha256':a.finalhash,'report_sha256':a.reporthash,'verifier_sha256':sha(verifier),'mathematical_gate':None,'note':'Wrong-tree is rejected by anchored SHA first, not isolated tree parser coverage. Mutated verifier is never executed. No original anchor is recomputed for a copy.'}
    (root/'controls.json').write_text(json.dumps(receipt,indent=2)+'\n')
    scratch.rmdir()
    print(json.dumps({'controls':len(results),'matched':True,'original_root_unchanged':True,'receipt_sha256':sha(root/'controls.json')}))
if __name__=='__main__':main()
