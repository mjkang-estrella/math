import re,json,subprocess,hashlib
from pathlib import Path
p=next(Path('logs').glob('*_independent_deep_v3.log'))
def validate(lines):
    dags=nodes=0; ids={}; pending=''; actual={}; current=None; stage=0
    def node(record):
        nonlocal nodes
        m=re.fullmatch(r'NODE (\d+) (.*?) CHILDREN #\[(.*?)\]\s*',record,re.S)
        assert m,record[:200]
        i=int(m[1]); assert i not in ids
        children=[int(x.strip()) for x in m[3].split(',') if x.strip()]
        kind=m[2].split()[0]
        arity={'bvar':0,'fvar':0,'mvar':0,'sort':0,'const':0,'app':2,'lam':2,'forall':2,'let':3,'literal':0,'mdata':1,'proj':1}
        assert kind in arity and len(children)==arity[kind]
        assert kind not in ('fvar','mvar')
        ids[i]=children; nodes+=1
    for line in lines:
        if line.startswith(('NODE ','DAG_COMPLETE ')):
            if pending: node(pending);pending=''
            if line.startswith('NODE '):pending=line.rstrip('\n');continue
            n=int(line.split()[-1]);assert set(ids)==set(range(n)) and n>0
            assert all(c in ids for cs in ids.values() for c in cs)
            reached=set();todo=[0]
            while todo:
                k=todo.pop()
                if k in reached:continue
                reached.add(k);todo.extend(ids[k])
            assert len(reached)==n
            ids={};dags+=1;stage+=1
        elif pending:
            pending+='\n'+line.rstrip('\n')
        elif line.startswith('ACTUAL '):
            if current:assert stage in (1,2)
            current=line.split(' ORIGIN ')[0][7:];assert current not in actual
            actual[current]=line.rstrip();stage=0
        elif line.startswith('AUDIT_COMPLETE '):
            assert stage in (1,2); assert len(actual)==13203
    assert not pending and not ids
    return {'declarations':len(actual),'DAGs':dags,'nodes':nodes,'log':str(p),'log_sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
with p.open() as f:r=validate(f)
# Structural negative control: delete root NODE from the first DAG, retaining its completion.
with p.open() as f:
    first=[]
    for l in f:
        if l.startswith('DAG_COMPLETE'):first.append(l);break
        if not l.startswith('NODE 0 '):first.append(l)
try: validate(iter(first))
except AssertionError:r['deleted_root_rejected']=True
else:raise AssertionError('vacuous validator')
print(json.dumps(r,indent=2))
subprocess.run(['python3','-I','-B','write_lane.py','results/dag-validation.json'],input=json.dumps(r,indent=2),text=True,check=True)
