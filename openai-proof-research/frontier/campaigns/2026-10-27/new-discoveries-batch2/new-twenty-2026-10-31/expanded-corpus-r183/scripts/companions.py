import sys,pathlib,subprocess
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from fetch import D,get
for a in ['2609.35191','2502.06032','2610.21866','2412.06467']:
 get(a+'.abs.html','https://arxiv.org/abs/'+a);get(a+'.pdf','https://arxiv.org/pdf/'+a)
for p in (D/'sources').glob('*.pdf'):
 if not p.with_suffix('.txt').exists():subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))])
