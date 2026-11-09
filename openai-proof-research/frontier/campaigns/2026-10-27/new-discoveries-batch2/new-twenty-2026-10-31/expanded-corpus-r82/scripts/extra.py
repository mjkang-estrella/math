from fetch import get,D
import json,subprocess
items=[('lp-later.pdf','https://arxiv.org/pdf/2610.17441'),('astala-later.pdf','https://arxiv.org/pdf/1511.07240'),('stern-later.pdf','https://publi.math.unideb.hu/paper/2146/download/10_5486_PMD_2017_7620.pdf'),('farhi-journal.pdf','https://www.maths.tcd.ie/EMIS/journals/JIS/VOL15/Farhi/farhi3.pdf'),('agrawal-primary.pdf','https://www.cse.iitk.ac.in/users/manindra/algebra/primality_v6.pdf'),('omega-tree.json','https://api.github.com/repos/the-omega-institute/trureturing/git/trees/'+json.loads((D/'sources/omega-head.json').read_text())['sha']+'?recursive=1')]
for it in items:
 print(get(it),flush=True)
 if it[0].endswith('.pdf') and (D/'sources'/it[0]).exists():subprocess.run(['pdftotext','-layout',str(D/'sources'/it[0]),str(D/'sources'/it[0]).replace('.pdf','.txt')])
