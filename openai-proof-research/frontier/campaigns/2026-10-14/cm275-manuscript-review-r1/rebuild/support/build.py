#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT.
"""Build in this package's temporary directory; render every final PDF page.
Use a working copy when rebuilding an already sealed package.
"""
import argparse, hashlib, json, os, re, shutil, subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--tectonic',default='tectonic');ap.add_argument('--allow-network',action='store_true');args=ap.parse_args()
 compiler=shutil.which(args.tectonic);assert compiler,'Tectonic not found'
 work=ROOT/'tmp/pdfs';out=ROOT/'output/pdf';checks=ROOT/'checks';pages=checks/'pages'
 for p in (work,pages):
  if p.exists():shutil.rmtree(p)
  p.mkdir(parents=True)
 out.mkdir(parents=True,exist_ok=True);checks.mkdir(exist_ok=True)
 
 for source in ('main.tex','formal-support.tex'):
  shutil.copyfile(ROOT/source,work/source)
 env=dict(os.environ);env['SOURCE_DATE_EPOCH']='1792108800'
 cmd=[compiler,'--keep-logs']+([] if args.allow_network else ['--only-cached'])+['main.tex']
 run=subprocess.run(cmd,cwd=work,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (checks/'compiler.txt').write_bytes(run.stdout)
 if (work/'main.log').exists():shutil.copyfile(work/'main.log',checks/'main.log')
 if run.returncode:raise SystemExit(run.stdout.decode(errors='replace'))
 log=(checks/'main.log').read_text(errors='replace')
 findings={k:len(re.findall(p,log,re.I|re.M)) for k,p in {'overfull_boxes':r'^Overfull','underfull_boxes':r'^Underfull','undefined':r'undefined','rerun':r'Rerun to get','missing_glyphs':r'Missing character:'}.items()}
 pdf=out/'continuum-coulomb-qma.pdf';shutil.copyfile(work/'main.pdf',pdf)
 subprocess.run(['pdftoppm','-r','110','-png',str(pdf),str(pages/'page')],check=True)
 subprocess.run(['pdftotext','-layout',str(pdf),str(checks/'extracted.txt')],check=True)
 info=subprocess.check_output(['pdfinfo',str(pdf)]).decode();(checks/'pdfinfo.txt').write_text(info)
 receipt={'compiler':subprocess.check_output([compiler,'--version']).decode().strip(),'compiler_sha256':sha(Path(compiler)),'source_date_epoch':env['SOURCE_DATE_EPOCH'],'source_sha256':sha(ROOT/'main.tex'),'formal_support_sha256':sha(ROOT/'formal-support.tex'),'pdf_sha256':sha(pdf),'pdf_pages':int(re.search(r'Pages:\s+(\d+)',info).group(1)),'rendered_pages':len(list(pages.glob('page-*.png'))),'log_findings':findings,'command':[Path(compiler).name,*cmd[1:]],'visual_inspection':'separate checks/visual-review.json'}
 (checks/'build-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
 shutil.rmtree(work);(ROOT/'tmp').rmdir()
 print(json.dumps(receipt,indent=2))
 if findings['overfull_boxes'] or findings['undefined'] or findings['rerun'] or findings['missing_glyphs']:raise SystemExit('Build requires correction')
if __name__=='__main__':main()
