#!/usr/bin/env python3
"""Run the COPIED verifier on disposable OWN-root copies; integrity only."""
import argparse,hashlib,json,os,shutil,stat,subprocess,sys
from pathlib import Path

def digest(b):return hashlib.sha256(b).hexdigest()
def snapshot(root):
    out={}
    for p in sorted(root.rglob('*')):
        s=p.lstat();rel=p.relative_to(root).as_posix()
        if p.is_symlink(): val=['symlink',os.readlink(p)]
        elif stat.S_ISREG(s.st_mode):val=['file',digest(p.read_bytes())]
        elif stat.S_ISDIR(s.st_mode):val=['dir']
        else:val=['special']
        out[rel]=[stat.S_IMODE(s.st_mode),s.st_nlink,*val]
    return out

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',required=True);ap.add_argument('--out',required=True);ap.add_argument('--finalhash',required=True);ap.add_argument('--reporthash',required=True);a=ap.parse_args()
    root=Path(a.root).absolute();out=Path(a.out).absolute()
    if Path(__file__).absolute()!=root/'run_controls.py':raise ValueError('must execute OWN runner')
    if out.exists() or root not in out.parents:raise ValueError('fresh output inside owned root required')
    before=snapshot(root);out.mkdir();cases=[]
    names=['baseline','deny-write','deny-process','missing-anchor','wrong-final','wrong-report','changed-report','changed-payload','missing-payload','extra-file','extra-directory','symlink','fifo','hardlink','manifest-change','changed-verifier','changed-runner','coherent-reseal-old-anchor','root-link','testanchor-source-url','testanchor-source-record','testanchor-primary-binding','testanchor-unsafe-path']
    for i,name in enumerate(names):
        c=out/f'{i:02d}-{name}';c.mkdir()
        for f in ['packet','FINAL.json','REPORT.md','MANIFEST.json','verify.py','run_controls.py']:
            src=root/f;dst=c/f
            if src.is_dir():shutil.copytree(src,dst)
            else:shutil.copyfile(src,dst)
        anchor=a.finalhash;report=a.reporthash;extra=[];actualroot=c
        target=c/'packet/public/report.md'
        if name=='deny-write':extra=['--probe','write']
        elif name=='deny-process':extra=['--probe','process']
        elif name=='wrong-final':anchor='0'*64
        elif name=='wrong-report':report='0'*64
        elif name=='changed-report':(c/'REPORT.md').write_text('changed')
        elif name=='changed-payload':target.write_bytes(target.read_bytes()+b'\nchanged')
        elif name=='missing-payload':target.unlink()
        elif name=='extra-file':(c/'packet/extra').write_text('extra')
        elif name=='extra-directory':(c/'packet/empty-extra').mkdir()
        elif name=='symlink':target.unlink();target.symlink_to(c/'REPORT.md')
        elif name=='fifo':target.unlink();os.mkfifo(target)
        elif name=='hardlink':target.unlink();os.link(c/'REPORT.md',target)
        elif name=='manifest-change':(c/'MANIFEST.json').write_bytes((c/'MANIFEST.json').read_bytes()+b' ')
        elif name=='changed-verifier':(c/'verify.py').write_bytes((c/'verify.py').read_bytes()+b'\n# mutation\n')
        elif name=='changed-runner':(c/'run_controls.py').write_bytes((c/'run_controls.py').read_bytes()+b'\n# mutation\n')
        elif name=='coherent-reseal-old-anchor':
            target.write_bytes(target.read_bytes()+b'\nchanged');m=json.loads((c/'MANIFEST.json').read_bytes());m['files']['public/report.md']['sha256']=digest(target.read_bytes());m['files']['public/report.md']['bytes']=target.stat().st_size;(c/'MANIFEST.json').write_text(json.dumps(m,indent=2)+'\n')
            f=json.loads((c/'FINAL.json').read_bytes());f['manifest_sha256']=digest((c/'MANIFEST.json').read_bytes());f['public_report_sha256']=digest(target.read_bytes());(c/'FINAL.json').write_text(json.dumps(f,indent=2)+'\n')
        elif name=='root-link':actualroot=out/'root-link-alias';actualroot.symlink_to(c,target_is_directory=True)
        if name.startswith('testanchor-'):
            if name in ['testanchor-source-url','testanchor-source-record']:
                f=c/'packet/public/source-register.json';rs=json.loads(f.read_bytes())
                if name=='testanchor-source-url':rs[0]['url']='https://example.invalid/wrong'
                else:rs[0]['canonical_record']['sha']='0'*40
                f.write_text(json.dumps(rs,indent=2)+'\n')
            elif name=='testanchor-primary-binding':
                f=c/'packet/public/primary-register.json';rs=json.loads(f.read_bytes());next(r for r in rs if r['artifacts'])['artifacts'][0]['sha256']='0'*64;f.write_text(json.dumps(rs,indent=2)+'\n')
            m=json.loads((c/'MANIFEST.json').read_bytes())
            for rel,entry in m['files'].items():
                b=(c/'packet'/rel).read_bytes();entry['sha256']=digest(b);entry['bytes']=len(b)
            if name=='testanchor-unsafe-path':m['files']['../escape']={'sha256':'0'*64,'bytes':0,'mode':420}
            (c/'MANIFEST.json').write_text(json.dumps(m,indent=2)+'\n')
            f=json.loads((c/'FINAL.json').read_bytes());f['manifest_sha256']=digest((c/'MANIFEST.json').read_bytes());(c/'FINAL.json').write_text(json.dumps(f,indent=2)+'\n');anchor=digest((c/'FINAL.json').read_bytes())
        cmd=[sys.executable,'-B',str(c/'verify.py'),'--root',str(actualroot),'--reporthash',report]
        if name!='missing-anchor':cmd+=['--finalhash',anchor]
        cmd+=extra
        pre=snapshot(c);r=subprocess.run(cmd,capture_output=True,text=True,timeout=20);post=snapshot(c)
        expected=name in ['baseline','deny-write','deny-process']
        okay=((r.returncode==0)==expected and pre==post)
        cases.append({'name':name,'expected_accept':expected,'returncode':r.returncode,'copied_input_unchanged':pre==post,'expected_result':okay,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
        if actualroot!=c:actualroot.unlink()
        shutil.rmtree(c)
    after={k:v for k,v in snapshot(root).items() if k!=out.relative_to(root).as_posix() and not k.startswith(out.relative_to(root).as_posix()+'/')}
    unchanged=before==after
    receipt={'cases':cases,'original_root_unchanged':unchanged,'integrity_only':True,'all_expected':unchanged and all(x['expected_result'] for x in cases)}
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
    if not receipt['all_expected']:raise SystemExit(1)
if __name__=='__main__':main()
