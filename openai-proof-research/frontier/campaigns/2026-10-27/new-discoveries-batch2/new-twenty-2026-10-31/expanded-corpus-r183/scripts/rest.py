import sys,pathlib,json,subprocess
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from fetch import D,get
for o in json.loads((D/'extracted.json').read_text()).values():
 a=o['source_url'].rsplit('/',1)[-1]
 if not (D/f'sources/{a}.pdf').exists():
  get(a+'.abs.html','https://arxiv.org/abs/'+a);get(a+'.pdf','https://arxiv.org/pdf/'+a)
for a in ['2510.09219','2202.07279','2202.03516','2205.00854']:
 get(a+'.abs.html','https://arxiv.org/abs/'+a);get(a+'.pdf','https://arxiv.org/pdf/'+a)
for p in (D/'sources').glob('*.pdf'):
 subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=False)
