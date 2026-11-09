import sys,json
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
from verify import verify,complement
known={16:{False:{},True:{}},32:{False:{},True:{}}}
paths=list(Path('outputs').glob('*.json'))+[Path('../expanded-corpus-r90/outputs/'+f) for f in ['xor-16-5.json','xor-16-7.json','xor-32-9.json']]
for p in paths:
 g=json.loads(p.read_text())
 if not isinstance(g,dict) or 'edges' not in g or g.get('N') not in known:continue
 g.setdefault('closed',False)
 for h,c in [(g,False),(complement(g),True)]:
  verify(h);known[h['N']][h['closed']][h['d']]={'file':str(p),'complement':c}
r={}
for N in [16,32]:
 r[N]={}
 for closed in [False,True]:
  target=range(4,N-5,2) if closed else range(5,N-4,2)
  assert all(d in known[N][closed] for d in target)
  r[N]['closed' if closed else 'open']={d:known[N][closed][d] for d in target}
Path('outputs/base-coverage.json').write_text(json.dumps(r,indent=2));print('All corrected base degrees at N=16 and N=32 exactly verified, including complement connectivity.')
