"""Rebuild and render the paper. Original code MIT."""
from pathlib import Path
import argparse,hashlib,json,os,subprocess
R=Path(__file__).resolve().parents[1]
p=argparse.ArgumentParser();p.add_argument('--tectonic',default='tectonic');p.add_argument('--only-cached',action='store_true');args=p.parse_args()
out=R/'output/pdf';out.mkdir(parents=True,exist_ok=True)
env=dict(os.environ,SOURCE_DATE_EPOCH='1792108800')
cmd=[args.tectonic,'--keep-logs','--outdir',str(out)]+(['--only-cached'] if args.only_cached else [])+[str(R/'main.tex')]
a=subprocess.run(cmd,env=env,capture_output=True,text=True)
(R/'checks/build-output.txt').write_text(a.stdout+a.stderr)
if a.returncode:raise RuntimeError(a.stdout+a.stderr)
log=(out/'main.log').read_text()
for forbidden in ['Overfull','Underfull','undefined references','undefined citations','Rerun to get']:
    if forbidden in log:raise RuntimeError('Unresolved TeX diagnostic: '+forbidden)
subprocess.run(['pdftotext',str(out/'main.pdf'),str(R/'checks/manuscript.txt')],check=True)
pages=R/'tmp/pdfs/pages';pages.mkdir(parents=True,exist_ok=True)
for old in pages.glob('page-*.png'):old.unlink()
subprocess.run(['pdftoppm','-scale-to','1400','-png',str(out/'main.pdf'),str(pages/'page')],check=True)
info=subprocess.check_output(['pdfinfo',str(out/'main.pdf')],text=True)
(R/'checks/pdfinfo.txt').write_text(info)
(R/'checks/build-receipt.json').write_text(json.dumps({'status':'BUILD_AND_RENDER_PASS_VISUAL_REVIEW_SEPARATE','tex_sha256':hashlib.sha256((R/'main.tex').read_bytes()).hexdigest(),'formal_coverage_sha256':hashlib.sha256((R/'formal-coverage.tex').read_bytes()).hexdigest(),'pdf_sha256':hashlib.sha256((out/'main.pdf').read_bytes()).hexdigest(),'rendered_pages':len(list(pages.glob('page-*.png'))),'engine':'tectonic','source_date_epoch':env['SOURCE_DATE_EPOCH']},indent=2)+'\n')
print(info)
