#!/usr/bin/env python3
"""Fresh T117Q manuscript build; original code Myeongjin Kang, MIT."""
import argparse, hashlib, json, os, shutil, subprocess
from pathlib import Path
HERE=Path(__file__).absolute().parent

def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--tectonic',type=Path,default=Path('/tmp/frontier-typeset/tectonic'))
    args=parser.parse_args(); out=args.output.absolute();out.mkdir(parents=True,exist_ok=False)
    source=HERE/'main.tex';shutil.copyfile(source,out/'main.tex')
    env=os.environ.copy();env['SOURCE_DATE_EPOCH']='1792281600'
    version=subprocess.check_output([str(args.tectonic),'--version'],text=True).strip()
    run=subprocess.run([str(args.tectonic),'--keep-logs','main.tex'],cwd=out,env=env,text=True,capture_output=True)
    (out/'build-console.log').write_text(run.stdout+run.stderr)
    receipt={'role':'author-side build, not mathematical review','source_sha256':digest(source),
             'tectonic':version,'tectonic_binary_sha256':digest(args.tectonic),
             'exit_code':run.returncode,'source_date_epoch':env['SOURCE_DATE_EPOCH']}
    if run.returncode==0:
        subprocess.run(['pdftotext','-layout',str(out/'main.pdf'),str(out/'main.txt')],check=True)
        info=subprocess.check_output(['pdfinfo',str(out/'main.pdf')],text=True)
        (out/'pdfinfo.txt').write_text(info)
        receipt['pdf_sha256']=digest(out/'main.pdf')
    (out/'build-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(run.stdout+run.stderr)
    raise SystemExit(run.returncode)
if __name__=='__main__':main()
