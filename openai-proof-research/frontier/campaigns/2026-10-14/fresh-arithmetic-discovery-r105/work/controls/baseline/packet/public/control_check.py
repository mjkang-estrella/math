#!/usr/bin/env python3
"""Copied artifact controls. Writes only under the assigned r105 work directory."""
import argparse,hashlib,json,os,shutil,stat,subprocess
from pathlib import Path

def sha(b):return hashlib.sha256(b).hexdigest()
def snap(root):
    out={}
    for base,ds,fs in os.walk(root,followlinks=False):
        for n in ds+fs:
            p=Path(base)/n;s=p.lstat();r=str(p.relative_to(root))
            out[r]=[s.st_mode,s.st_nlink,os.readlink(p) if p.is_symlink() else (sha(p.read_bytes()) if p.is_file() else None)]
    return out

def main():
    p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True)
    for k in ['final','manifest','report']:p.add_argument('--'+k+'-sha256',required=True)
    a=p.parse_args();root=a.root.resolve();require_name='fresh-arithmetic-discovery-r105'
    assert root.name==require_name
    args=sum([['--'+k+'-sha256',getattr(a,k+'_sha256')] for k in ['final','manifest','report']],[])
    fixtures=root/'work/controls';assert not fixtures.exists();fixtures.mkdir(parents=True)
    original=snap(root/'packet');report=(root/'REPORT.md').read_bytes();results=[]
    verifier=root/'packet/public/verify.py'
    for case in ['baseline','payload','missing','extra-file','extra-directory','symlink','report','forged-reseal','wrong-anchor']:
        q=fixtures/case;q.mkdir();shutil.copytree(root/'packet',q/'packet');shutil.copy2(root/'REPORT.md',q/'REPORT.md')
        target=q/'packet/public/DERIVATION.md';callargs=args.copy()
        if case=='payload':target.write_bytes(target.read_bytes()+b'\nmutation\n')
        if case=='missing':target.unlink()
        if case=='extra-file':(q/'packet/extra').write_text('extra')
        if case=='extra-directory':(q/'packet/extra').mkdir()
        if case=='symlink':target.unlink();target.symlink_to('READINGS.md')
        if case=='report':(q/'REPORT.md').write_text('changed')
        if case=='forged-reseal':
            target.write_bytes(target.read_bytes()+b'\nmutation\n')
            m=q/'packet/MANIFEST.json';j=json.loads(m.read_text());j['files']['public/DERIVATION.md']['size']=target.stat().st_size;j['files']['public/DERIVATION.md']['sha256']=sha(target.read_bytes());m.write_text(json.dumps(j,indent=2)+'\n')
            f=q/'packet/FINAL.json';v=json.loads(f.read_text());v['manifest_sha256']=sha(m.read_bytes());f.write_text(json.dumps(v,indent=2)+'\n')
        if case=='wrong-anchor':callargs[1]='0'*64
        before=snap(q)
        c=subprocess.run(['python','-B',str(verifier),'--root',str(q),*callargs],capture_output=True,text=True)
        assert snap(q)==before,'verifier changed fixture'
        assert (c.returncode==0)==(case=='baseline'),(case,c.stdout,c.stderr)
        results.append(dict(case=case,returncode=c.returncode,fixture_unchanged=True,output=c.stdout.strip()))
    assert snap(root/'packet')==original and (root/'REPORT.md').read_bytes()==report,'original sealed bytes changed'
    print(json.dumps(dict(label='copied artifact controls only',original_packet_report_unchanged=True,cases=results),indent=2))
if __name__=='__main__':main()
