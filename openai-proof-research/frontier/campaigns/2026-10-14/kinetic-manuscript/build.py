"""Portable standalone TeX build and all-page rendering.
Copyright (c) 2026 Myeongjin Kang. MIT License.
"""
from pathlib import Path
import argparse,os,shutil,subprocess
HERE=Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('--tectonic',default=os.environ.get('TECTONIC'));a=p.parse_args()
engine=a.tectonic or shutil.which('tectonic')
if not engine and Path('/tmp/frontier-typeset/tectonic').is_file():
    engine='/tmp/frontier-typeset/tectonic'
if not engine: raise SystemExit('Install Tectonic or pass --tectonic /path/to/tectonic')
(HERE/'output/pdf').mkdir(parents=True,exist_ok=True);(HERE/'qa').mkdir(exist_ok=True)
subprocess.run([engine,'--keep-logs','--outdir','output/pdf','main.tex'],cwd=HERE,check=True)
subprocess.run(['pdftotext','-layout','output/pdf/main.pdf','qa/main.txt'],cwd=HERE,check=True)
subprocess.run(['pdftoppm','-r','105','-png','output/pdf/main.pdf','qa/page'],cwd=HERE,check=True)
print('Build and renders complete; visual inspection and verify.py remain separate.')
