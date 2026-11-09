from pathlib import Path
import subprocess,os
L=Path(__file__).resolve().parents[1]
os.environ.update(TMPDIR=str(L/'tmp'),TMP=str(L/'tmp'),TEMP=str(L/'tmp'),XDG_CACHE_HOME=str(L/'tmp/cache'))
with (L/'paper.ps').open('wb') as out:
 subprocess.run(['groff','-Kutf8','-e','-t',str(L/'scripts/layout.tmac'),'-Tps',str(L/'paper.ms')],stdout=out,check=True,cwd=L)
subprocess.run(['gs','-q','-dBATCH','-dNOPAUSE','-sDEVICE=pdfwrite','-sPAPERSIZE=letter','-sOutputFile='+str(L/'paper.pdf'),'-c','<</BeginPage {pop 0.90 0.90 scale 34 44 translate}>> setpagedevice','-f',str(L/'paper.ps')],check=True,cwd=L)
subprocess.run(['pdfinfo',str(L/'paper.pdf')],check=True)
subprocess.run(['pdftotext','-layout',str(L/'paper.pdf'),str(L/'paper.txt')],check=True)
subprocess.run(['pdftoppm','-scale-to','1400','-png',str(L/'paper.pdf'),str(L/'qa/approved-page')],check=True)
