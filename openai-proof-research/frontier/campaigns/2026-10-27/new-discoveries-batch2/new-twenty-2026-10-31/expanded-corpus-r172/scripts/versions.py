import sys,pathlib,json,re
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from fetch import D,fetch
for p in (D/'sources').glob('abs-*.html'):
 a=p.stem[4:];s=p.read_text();j=s.find('Submission history');history=s[j:s.find('</div>',j)];versions=re.findall(r'\[v(\d+)\]',history)
 for v in versions[:-1]:fetch('https://arxiv.org/html/'+a+'v'+v,'arxiv-'+a+'v'+v+'.html')
