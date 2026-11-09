from pathlib import Path
import subprocess
L=Path(__file__).parent
exec((L/'retrieve.py').read_text().split('for name,url in queries:')[0])
queries=[('negative-dependence','https://arxiv.org/pdf/2204.11438v4'),('joint2016','https://arxiv.org/pdf/1411.2014'),('precise-search','https://export.arxiv.org/api/query?search_query='+urllib.parse.quote('all:"quantile" AND all:"aggregation" AND (all:"mixtures" OR all:"mixability")')+'&max_results=40')]
exec('for name,url in queries:'+ (L/'retrieve.py').read_text().split('for name,url in queries:')[1])
for name in ['convolution','negative-dependence','joint2016']:
 p=L/'sources'/name
 if p.exists() and p.read_bytes().startswith(b'%PDF'):
  subprocess.run(['pdftotext','-layout',str(p),str(p)+'.txt'],check=True)
