from pathlib import Path
import json,re,collections
L=Path(__file__).resolve().parent
D=[json.loads(s) for s in (L/'frozen/references/dag.jsonl').open()]
N=[d['atom'] if 'atom' in d else d['args'] for d in D]
def op(i):
 x=N[i]
 return x if isinstance(x,str) else op(x[0])
I=json.loads((L/'frozen/assembly-inventory.json').read_text())
fresh={}
for d in I:
 if d['rule']=='intro-def':
  c=N[d['node']][-1];left,right=N[c][1:];neg,eq=N[left][1:];cond,eq2=N[right][1:];z,t=N[eq][1:];z2,f=N[eq2][1:]
  assert z==z2 and N[neg][1]==cond and z not in fresh
  assert isinstance(N[z],str) and N[z].startswith('z3name!')
  fresh[z]=(cond,t,f)
assert len(fresh)==128
defs={}
for p in sorted((L/'replay').glob('Sem[0-9]*.lean')):
 for line in p.read_text().splitlines():
  q=re.fullmatch(r'def e(\d+) \(_v : Vars\) : (ℤ|Prop) := (.+)',line)
  if q:defs[int(q[1])]=(q[2],q[3])
ref=lambda i:f'(e{i} _v)'
def expected(i):
 x=N[i]
 if i in fresh:
  c,t,f=fresh[i];return f'(if {ref(c)} then {ref(t)} else {ref(f)})'
 if isinstance(x,str):
  if x in ['true','false']:return {'true':'True','false':'False'}[x]
  if re.fullmatch('-?[0-9]+',x):return f'({x} : ℤ)'
  assert x in ['m','H','t','a','b','c','d'],x
  return '_v.'+x
 a=x[1:];es=list(map(ref,a));o=op(i)
 if o in ['+','*','and','or']:
  return '('+{'+':' + ','*':' * ','and':' ∧ ','or':' ∨ '}[o].join(es)+')'
 if o=='-':return '(-'+es[0]+')' if len(es)==1 else '('+' - '.join(es)+')'
 if o in ['=','~','<=','>=','<','>']:
  s='↔' if o in ['=','~'] and defs[a[0]][0]=='Prop' else {'=':'=','~':'=','<=':'≤','>=':'≥','<':'<','>':'>'}[o]
  return f'({es[0]} {s} {es[1]})'
 if o=='not':return f'(¬ {es[0]})'
 assert o=='ite',o
 return f'(if {es[0]} then {es[1]} else {es[2]})'
for i,(_,body) in defs.items():assert body==expected(i),(i,body,expected(i))
# Reconstruct reachability directly, rather than trusting inventory coverage.
reachable=set();todo=[22671]
while todo:
 i=todo.pop()
 if i in reachable:continue
 reachable.add(i)
 if isinstance(N[i],list):todo.extend(N[i])
rules=set(d['rule'] for d in I)
actual={i for i in reachable if isinstance(N[i],list) and op(i) in rules}
assert actual=={d['node'] for d in I}
for d in I:assert op(d['node'])==d['rule'] and N[d['node']][-1]==d['conclusion']
assert {i for i in defs if isinstance(N[i],str) and N[i].startswith('z3name!')}==set(fresh)
assert len(re.findall(r'^theorem node_\d+ ', '\n'.join(p.read_text() for p in (L/'replay/generated').glob('th_lemma_*.lean')),re.M))==1329
out=dict(actual_DAG_nodes=len(D),reachable_rules=len(actual),fresh_actual_ite_definitions=len(fresh),all_semantic_bodies_match_actual_DAG=len(defs),inherited_arithmetic_implications=1329,trust_boundary='DAG/proof binding inherited from frozen computational review; final theorem does not depend on parser correctness')
(L/'semantic-review.json').write_text(json.dumps(out,indent=2));print(out)
