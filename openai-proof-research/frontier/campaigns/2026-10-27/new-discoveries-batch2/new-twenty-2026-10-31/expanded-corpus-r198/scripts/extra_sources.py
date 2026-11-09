import pathlib,sys,subprocess,json
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from fetch import fetch,D
urls=[('tenner-seminar','https://pages.mtu.edu/~wjkeith/PartitionsSpecialtySeminar/William-Keith-Apr2021.pdf'),('keith-home','https://pages.mtu.edu/~wjkeith/'),('tenner-citer','https://pdfs.semanticscholar.org/acbf/35ac618195f19c32c694fc192dc99e28c01d.pdf'),('lev-vor','https://math.haifa.ac.il/seva/Papers/DeF.pdf'),('bressoud-II','https://cam.tju.edu.cn/~ji/papers/24OBreConj-s-2.pdf'),('kreweras-vor','https://par.nsf.gov/servlets/purl/10353965'),('nunge-vor','https://zhangbiaomath.github.io/papers/2019-eujc-segmented_permutations.pdf'),('csp-vor','https://epubs.siam.org/doi/pdf/10.1137/19M1291054')]
for label,url in urls:
 z=fetch(url,label);print(label,z['status'],flush=True)
 if z['status']==200 and pathlib.Path(z['body']).read_bytes().startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',z['body'],str(D/'outputs'/f'{label}.txt')])
