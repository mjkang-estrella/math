import pathlib,sys,subprocess
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from fetch import fetch,D
for label,url in [('tenner-refutation','https://math.colgate.edu/~integers/x9/x9.pdf'),('treelike','https://arxiv.org/pdf/2201.11082'),('sync','https://arxiv.org/abs/2412.00622')]:
 z=fetch(url,label);print(label,z['status'],flush=True)
 if z['status']==200 and pathlib.Path(z['body']).read_bytes().startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',z['body'],str(D/'outputs'/f'{label}.txt')])
