import sys,pathlib,json,subprocess
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));from fetch import get,D
for key,vs in json.loads((D/'versions.json').read_text()).items():
 a=key.split('.abs')[0]
 for v in vs[:-1]:
  tag=a+'v'+v;print(get(tag+'.pdf','https://arxiv.org/pdf/'+tag),flush=True)
  p=D/'sources'/f'{tag}.pdf'
  if p.exists():subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))])
