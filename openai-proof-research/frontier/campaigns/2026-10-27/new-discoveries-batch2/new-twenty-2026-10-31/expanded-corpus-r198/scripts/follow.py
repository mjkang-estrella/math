import pathlib,sys,subprocess
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from fetch import fetch,D
for label,url in [('keith-cv','https://pages.mtu.edu/~wjkeith/CVOct2026.pdf'),('tenner-journal','https://doi.org/10.1007/s11139-020-00249-y')]:
 z=fetch(url,label);print(z['status'])
 if z['status']==200 and pathlib.Path(z['body']).read_bytes().startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',z['body'],str(D/'outputs'/f'{label}.txt')])
