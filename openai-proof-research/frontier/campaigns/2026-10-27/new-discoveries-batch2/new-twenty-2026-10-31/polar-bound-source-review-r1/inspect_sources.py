from pathlib import Path
import json, resource
resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
o=Path(__file__).resolve().parent;r=o.parent/'expanded-corpus-r255'
j=json.loads((r/'polar-web-retrieval.json').read_text())
print('TYPE',type(j).__name__)
def walk(x,path=''):
 if isinstance(x,str) and len(x)>1000:
  p=o/('retrieval-'+path.replace('/','-')+'.txt');p.write_text(x); print(p.name,len(x))
 elif isinstance(x,dict):
  for k,v in x.items():walk(v,path+'-'+k)
 elif isinstance(x,list):
  for k,v in enumerate(x):walk(v,path+'-'+str(k))
walk(j)
for f in ['2303.17055v1-pdf.txt','2303.17055v2-pdf.txt']:
 t=(r/f).read_text(); print(f,len(t)); print(t[:3500]);
