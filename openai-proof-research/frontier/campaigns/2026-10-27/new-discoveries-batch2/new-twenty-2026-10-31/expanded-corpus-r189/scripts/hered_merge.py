import json,sys,pathlib
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from hered import Store
S=pathlib.Path(sys.argv[1]); n=int(sys.argv[2]); st=Store(); out=[]
for f in sorted(S.glob(f'l{n}-forb-*.json')):
    for g in json.loads(f.read_text())['minimal_forbidden']:
        if st.add(list(g),n): out.append(g)
(S/f'level-{n}-forbidden-merged.json').write_text(json.dumps(out))
print('n',n,'distinct minimal forbidden',len(out))
