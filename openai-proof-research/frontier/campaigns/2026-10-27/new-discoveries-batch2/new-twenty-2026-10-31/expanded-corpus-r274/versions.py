from pathlib import Path
import re,json,subprocess,sys
p=Path(__file__).resolve().parent
v={};urls=[]
for f in (p/'sources').glob('*_abs_*'):
 if f.name.endswith('json'):continue
 s=f.read_text(); a=f.name.replace('arxiv.org_abs_','').replace('math_','math/').replace('cond-mat_','cond-mat/'); vv=re.findall(r'\[v(\d+)\]',s); v[a]=vv
 urls += ['https://arxiv.org/pdf/'+a+'v'+x for x in vv]
(p/'versions.json').write_text(json.dumps(v,indent=2)+'\n')
subprocess.run([sys.executable,'-I','-B',str(p/'fetch.py'),*urls],check=True)
