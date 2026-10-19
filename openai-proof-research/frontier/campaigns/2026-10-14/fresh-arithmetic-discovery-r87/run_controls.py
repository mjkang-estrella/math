#!/usr/bin/env python3
"""Original r87 disposable-copy integrity controls. MIT. No mathematics tests."""
import sys
sys.dont_write_bytecode=True
import argparse,hashlib,json,os,shutil,stat,subprocess
from pathlib import Path
sha=lambda b:hashlib.sha256(b).hexdigest()
def snapshot(root,exclude=None):
    out={}
    for base,ds,fs in os.walk(root,followlinks=False):
        if exclude is not None and Path(base)==root:ds[:]=[d for d in ds if d!=exclude]
        for n in ds+fs:
            p=Path(base)/n;s=p.lstat();r=str(p.relative_to(root));x={'mode':s.st_mode,'nlink':s.st_nlink}
            if stat.S_ISREG(s.st_mode):x.update(sha256=sha(p.read_bytes()),bytes=s.st_size)
            elif stat.S_ISLNK(s.st_mode):x['target']=os.readlink(p)
            out[r]=x
    return out
def write(p,x):p.write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
def bump(p):p.write_bytes(p.read_bytes()+b'\n')
def spec(p):b=p.read_bytes();return {'sha256':sha(b),'bytes':len(b),'mode':stat.S_IMODE(p.stat().st_mode)}
def main():
    ap=argparse.ArgumentParser();ap.add_argument('root',type=Path);ap.add_argument('--finalhash',required=True);ap.add_argument('--reporthash',required=True);ap.add_argument('--tree',required=True,type=Path);a=ap.parse_args();root=a.root.resolve();out=root/'controls';out.mkdir(exist_ok=True)
    if any(out.iterdir()):raise RuntimeError('controls output must be empty')
    before=snapshot(root,'controls');write(out/'original-before.json',before);receipt=[]
    cases=[('baseline','INTEGRITY_ONLY_VERIFIED'),('write-probe','READ_ONLY_WRITE_DENIED'),('process-probe','READ_ONLY_PROCESS_DENIED'),('missing-finalhash','required'),('wrong-finalhash','FINAL_ANCHOR_MISMATCH'),('wrong-reporthash','REPORT_ANCHOR_MISMATCH'),('payload-change','PAYLOAD_MISMATCH'),('payload-delete','FILE_MEMBERSHIP_MISMATCH'),('extra-file','FILE_MEMBERSHIP_MISMATCH'),('extra-directory','DIRECTORY_MEMBERSHIP_MISMATCH'),('symlink','NONREGULAR_FILE'),('hardlink','HARDLINK'),('fifo','NONREGULAR_FILE'),('directory-mode','DIRECTORY_MODE_MISMATCH'),('report-change','OUTSIDE_BINDING_MISMATCH'),('manifest-change','OUTSIDE_BINDING_MISMATCH'),('verifier-change','OUTSIDE_BINDING_MISMATCH'),('runner-change','OUTSIDE_BINDING_MISMATCH'),('wrong-tree','TREE_ANCHOR_MISMATCH'),('coherent-reseal-old-anchor','FINAL_ANCHOR_MISMATCH')]
    for name,wanted in cases:
        c=out/('copy-'+name);c.mkdir()
        for p in root.iterdir():
            if p.name=='controls':continue
            if p.is_dir():shutil.copytree(p,c/p.name)
            else:shutil.copy2(p,c/p.name)
        target=c/'packet/public/cancellation.md';tree=a.tree.resolve();fh=a.finalhash;rh=a.reporthash;extra=[]
        if name=='write-probe':extra=['--probe-write']
        elif name=='process-probe':extra=['--probe-process']
        elif name=='wrong-finalhash':fh='0'*64
        elif name=='wrong-reporthash':rh='0'*64
        elif name=='payload-change':bump(target)
        elif name=='payload-delete':target.unlink()
        elif name=='extra-file':(c/'packet/unexpected').write_text('extra')
        elif name=='extra-directory':(c/'packet/unexpected-directory').mkdir()
        elif name=='symlink':target.unlink();target.symlink_to('report.md')
        elif name=='hardlink':target.unlink();os.link(c/'packet/public/report.md',target)
        elif name=='fifo':target.unlink();os.mkfifo(target)
        elif name=='directory-mode':(c/'packet/public').chmod(0o700)
        elif name=='report-change':bump(c/'REPORT.md')
        elif name=='manifest-change':bump(c/'MANIFEST.json')
        elif name=='verifier-change':
            with (c/'verify.py').open('a') as f:f.write('\n# copied mutation\n')
        elif name=='runner-change':bump(c/'run_controls.py')
        elif name=='wrong-tree':tree=c/'WRONG-TREE.json';tree.write_text('{}\n')
        elif name=='coherent-reseal-old-anchor':
            bump(target);m=json.loads((c/'MANIFEST.json').read_text());m['files']['public/cancellation.md']=spec(target);write(c/'MANIFEST.json',m);f=json.loads((c/'FINAL.json').read_text());f['outside']['MANIFEST.json']=spec(c/'MANIFEST.json');write(c/'FINAL.json',f)
        args=[sys.executable,'-B',str(c/'verify.py'),str(c),'--reporthash',rh,'--tree',str(tree),*extra]
        if name!='missing-finalhash':args+=['--finalhash',fh]
        copy_before=snapshot(c);proc=subprocess.run(args,capture_output=True,text=True,timeout=20);copy_after=snapshot(c);text=proc.stdout+proc.stderr
        expected_rc=0 if name=='baseline' else (2 if name=='missing-finalhash' else 1)
        ok=proc.returncode==expected_rc and wanted in text and copy_before==copy_after
        receipt.append({'case':name,'returncode':proc.returncode,'expected_diagnostic':wanted,'matched':ok,'copied_inputs_unchanged':copy_before==copy_after,'stdout':proc.stdout,'stderr':proc.stderr})
        if not ok:
            write(out/'receipt.json',{'status':'CONTROL_FAILURE','cases':receipt});raise RuntimeError(name+': '+text)
        shutil.rmtree(c)
    after=snapshot(root,'controls');write(out/'original-after.json',after);require=before==after
    result={'status':'INTEGRITY_CONTROLS_ONLY','case_count':len(receipt),'original_root_unchanged_except_controls_output':require,'cases':receipt,'final_sha256':a.finalhash,'report_sha256':a.reporthash}
    write(out/'receipt.json',result)
    if not require:raise RuntimeError('original root changed')
    print(json.dumps({'status':result['status'],'cases':len(receipt),'all_expected':all(x['matched'] for x in receipt),'original_unchanged':require,'receipt_sha256':sha((out/'receipt.json').read_bytes())},sort_keys=True))
if __name__=='__main__':main()
