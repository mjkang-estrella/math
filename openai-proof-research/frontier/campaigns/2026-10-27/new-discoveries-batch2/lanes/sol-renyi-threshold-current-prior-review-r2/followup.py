import pathlib
L=pathlib.Path(__file__).resolve().parent
s=(L/'fetch.py').read_text();exec(compile(s.split('for name,url in jobs:')[0],'init','exec'))
jobs=[('rs-abs.html','https://arxiv.org/abs/2610.15716'),('rs.html','https://arxiv.org/html/2610.15716'),('rs.pdf','https://arxiv.org/pdf/2610.15716')]
exec(compile('for name,url in jobs:'+s.split('for name,url in jobs:')[1],'loop','exec'))
import subprocess
if (L/'rs.pdf').exists():subprocess.run(['pdftotext','-layout',str(L/'rs.pdf'),str(L/'rs.txt')],check=True)
