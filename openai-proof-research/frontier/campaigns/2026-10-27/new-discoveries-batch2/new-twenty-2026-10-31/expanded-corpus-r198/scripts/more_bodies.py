import pathlib,sys,subprocess
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from fetch import fetch,D
items=[('sync-correct','https://arxiv.org/pdf/2404.01783'),('ballot-proof','https://arxiv.org/pdf/2009.05973'),('glt-vor','https://orbi.umons.ac.be/bitstream/20.500.12907/54217/1/GLT%20SEQUENCES%20AND%20NORMAL%20MATRICES.pdf'),('csp-eccc','https://eccc.weizmann.ac.il/report/2019/013/download/')]
for label,url in items:
 z=fetch(url,label);print(label,z['status'],flush=True)
 if z['status']==200 and pathlib.Path(z['body']).read_bytes().startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',z['body'],str(D/'outputs'/f'{label}.txt')])
