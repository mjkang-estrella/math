import pathlib,json,sys,subprocess,re
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));from fetch import get,D
for o in json.loads((D/'extracted.json').read_text()).values():
 a=o['source_url'].rsplit('/',1)[-1]
 print(get(a+'.pdf','https://arxiv.org/pdf/'+a),flush=True)
 p=D/'sources'/f'{a}.pdf'
 if p.exists():subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=False)
