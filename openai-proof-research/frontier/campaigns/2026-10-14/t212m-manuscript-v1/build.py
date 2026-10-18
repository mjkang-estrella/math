#!/usr/bin/env python3
"""Build original T212M article in a new directory. Myeongjin Kang; MIT."""
import argparse, hashlib, json, os, shutil, subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--tectonic',type=Path,default=Path('/tmp/frontier-typeset/tectonic'))
    a=ap.parse_args();out=a.output.resolve();out.mkdir(parents=True,exist_ok=False)
    for src in (HERE/'public').rglob('*.tex'):
        dest=out/src.relative_to(HERE/'public');dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dest)
    env=os.environ.copy();env['SOURCE_DATE_EPOCH']='1792281600'
    run=subprocess.run([str(a.tectonic),'--only-cached','--untrusted','--keep-logs','--keep-intermediates','--reruns','2','main.tex'],cwd=out,env=env,text=True,capture_output=True)
    (out/'build-console.log').write_text(run.stdout+run.stderr)
    receipt={'role':'author compilation, not mathematical verification','exit_code':run.returncode,'source_date_epoch':env['SOURCE_DATE_EPOCH'],'tectonic_sha256':sha(a.tectonic),'sources':{str(p.relative_to(HERE)):sha(p) for p in sorted((HERE/'public').rglob('*.tex'))}}
    if run.returncode==0:
        receipt['pdf_sha256']=sha(out/'main.pdf');subprocess.run(['pdftotext','-layout',str(out/'main.pdf'),str(out/'main.txt')],check=True)
        (out/'pdfinfo.txt').write_text(subprocess.check_output(['pdfinfo',str(out/'main.pdf')],text=True))
    (out/'build-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(run.stdout+run.stderr);raise SystemExit(run.returncode)
if __name__=='__main__': main()
