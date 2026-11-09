import sys,json,copy
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
from verify import verify
base=json.loads(Path('outputs/base-32-8-1.json').read_text());tests={}
a=copy.deepcopy(base);a['edges'].pop();tests['deleted_edge']=a
a=copy.deepcopy(base);a['edges'].append(a['edges'][0]);tests['duplicate_edge']=a
a=copy.deepcopy(base);a['edges'][0]=[0,0];tests['loop']=a
a=copy.deepcopy(base);a['closed']=False;tests['wrong_neighbourhood_type']=a
r={}
for name,g in tests.items():
 try:verify(g);r[name]='FAIL accepted'
 except AssertionError:r[name]='PASS rejected'
assert all(x=='PASS rejected' for x in r.values());Path('outputs/negative-controls.json').write_text(json.dumps(r,indent=2));print(r)
