from pathlib import Path
import sys,re,json,hashlib
L=Path(__file__).resolve().parent;F=L/'frozen'
s=(F/'inspect.py').read_text();s=s[s.index('def parse(s):'):s.index('start=time.monotonic()')]
e=dict(sys=sys,re=re);exec(s,e);sys.setrecursionlimit(12000)
original=(F/'frozen/z3-proof.sexpr').read_text()
assert original.startswith('(let ((a!1 (<= (+ m (* (- 1) a) (* (- 1) c)) 0))')
mut=original.replace('(let ((a!1 (<= (+ m (* (- 1) a) (* (- 1) c)) 0))','(let ((a!1 (<= (+ m (* (- 1) a) (* (- 1) c)) 1))',1)
root=e['resolve'](e['parse'](mut)[0],e['Env']())
expected=[]
for line in (F/'dag.jsonl').read_text().splitlines():
 d=json.loads(line);expected.append(d.get('atom',tuple(d.get('args',[]))))
assert e['nodes']!=expected
p=L/'mutations/scope/changed.sexpr';p.write_text(mut)
out={'rejected':True,'mechanism':'actual parser reconstructs altered binding RHS into DAG different from certified DAG','original_sha256':hashlib.sha256(original.encode()).hexdigest(),'mutant_sha256':hashlib.sha256(mut.encode()).hexdigest(),'same_root_id':root==22671}
(L/'scope-mutation.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
