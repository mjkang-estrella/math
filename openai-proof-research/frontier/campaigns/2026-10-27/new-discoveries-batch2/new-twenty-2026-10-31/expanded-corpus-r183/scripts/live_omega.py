import sys,pathlib,json
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from fetch import D,get
h=json.loads((D/'sources/omega-head.json').read_text())['sha'];base=f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/'
get('omega-root.json',base+h)
t=json.loads((D/'sources/omega-root.json').read_text())['tree']
for name in ['D5','Problems']:
 s=next(x['sha'] for x in t if x['path']==name);get('omega-'+name+'.json',base+s+'?recursive=1')
 if (D/f'sources/omega-{name}.json').exists():
  o=json.loads((D/f'sources/omega-{name}.json').read_text());paths=[x['path'] for x in o.get('tree',[])];(D/f'outputs/omega-{name}.paths').write_text('\n'.join(paths)+'\n');print(name,len(paths),o.get('truncated'))
