from pathlib import Path
import json,collections
L=Path(__file__).resolve().parent
N=[d.get('atom',tuple(d.get('args',[]))) for d in map(json.loads,(L/'frozen/sol-floor-sums-certificate-r2/dag.jsonl').open())]
rules={'rewrite','asserted','mp','hypothesis','monotonicity','intro-def','trans','def-axiom','unit-resolution','th-lemma','lemma','apply-def','not-or-elim'}
def head(i):return N[i] if isinstance(N[i],str) else head(N[i][0])
P={i for i,x in enumerate(N) if isinstance(x,tuple) and head(i) in rules}
used=set();todo=[22671]
while todo:
 i=todo.pop()
 if i in used:continue
 used.add(i)
 if isinstance(N[i],tuple):todo.extend(N[i])
P&=used
sort={}
for i,x in enumerate(N):
 if isinstance(x,str):
  if x in ['true','false']:sort[i]='Prop'
  elif x in ['m','H','t','a','b','c','d'] or x.startswith('z3name!') or x.lstrip('-').isdigit():sort[i]='Int'
 elif head(i) in rules:sort[i]='Proof'
 elif head(i) in ['+','-','*']:sort[i]='Int'
 elif head(i)=='ite':sort[i]=sort[x[2]]
 else:sort[i]='Prop'
fresh={}
for i in sorted(P):
 if head(i)=='intro-def':
  c=N[i][-1];u,w=N[c][1:];np,eq=N[u][1:];p,eq2=N[w][1:];z,t=N[eq][1:];zz,f=N[eq2][1:]
  assert z==zz and N[np][1]==p and z not in fresh
  fresh[z]=(p,t,f)
def deps(i):
 if i in fresh:return list(fresh[i])
 return list(N[i][1:]) if isinstance(N[i],tuple) else []
order=[];done=set();active=set()
def visit(i):
 if i in done:return
 assert i not in active,('cycle',i)
 active.add(i)
 for j in deps(i):visit(j)
 active.remove(i);done.add(i);order.append(i)
for i in sorted(used):
 if sort.get(i) in ['Int','Prop']:visit(i)
def ref(i):return f'(e{i} _v)'
def expr(i,rec=ref,abstract=False):
 x=N[i]
 if i in fresh and not abstract:
  p,t,f=fresh[i];return f'(if {rec(p)} then {rec(t)} else {rec(f)})'
 if isinstance(x,str):
  if x=='true':return 'True'
  if x=='false':return 'False'
  if x.lstrip('-').isdigit():return f'({x} : ℤ)'
  return f'_v.{x}'
 op=head(i);a=x[1:];e=[rec(j) for j in a]
 if op in ['+','*','and','or']:return '('+{'+':' + ','*':' * ','and':' ∧ ','or':' ∨ '}[op].join(e)+')'
 if op=='-':return '(-'+e[0]+')' if len(e)==1 else '('+' - '.join(e)+')'
 if op in ['=','~','<=','>=','<','>']:
  sym={'=':'↔' if sort[a[0]]=='Prop' else '=', '~':'↔' if sort[a[0]]=='Prop' else '=', '<=':'≤','>=':'≥','<':'<','>':'>'}[op]
  return f'({e[0]} {sym} {e[1]})'
 if op=='not':return f'(¬ {e[0]})'
 if op=='ite':return f'(if {e[0]} then {e[1]} else {e[2]})'
 raise ValueError((i,op))
base=['import Mathlib.Data.Int.Basic','import Mathlib.Tactic.Tauto','import Lean.Elab.Tactic.Omega','set_option autoImplicit false','set_option warningAsError true','set_option maxRecDepth 20000','set_option maxHeartbeats 1500000','namespace Assembly','structure Vars where','  (m H t a b c d : ℤ)']
(L/'SemBase.lean').write_text('\n'.join(base)+'\nend Assembly\n')
modules=[]
for k in range(0,len(order),150):
 name=f'Sem{k//150:03d}';prev=modules[-1] if modules else 'SemBase'
 lines=[f'import {prev}','set_option autoImplicit false','set_option warningAsError true','namespace Assembly','noncomputable section','open Classical']
 for i in order[k:k+150]:lines.append(f'def e{i} (_v : Vars) : {"ℤ" if sort[i]=="Int" else "Prop"} := {expr(i)}')
 lines.extend(['end','end Assembly']);(L/(name+'.lean')).write_text('\n'.join(lines)+'\n');modules.append(name)
# Proof nodes carry explicit local hypotheses; assertions remain one exact query conjunction.
assertions=sorted(i for i in P if head(i)=='asserted')
lines=[f'import {modules[-1]}','set_option autoImplicit false','set_option warningAsError true','namespace Assembly','def Query (_v : Vars) : Prop := '+' ∧ '.join(ref(N[i][-1]) for i in assertions),'end Assembly']
(L/'Query.lean').write_text('\n'.join(lines)+'\n')
arith={d['node']:d['module'] for d in json.loads((L/'frozen/sol-floor-sums-certificate-formal-r2/generated-inventory.json').read_text()) if d['rule']=='th-lemma'}
hyps={};inventory=[];proofmods=[]
for k in range(0,len(P),45):
 ids=sorted(P)[k:k+45];name=f'Dag{k//45:03d}'
 imports=[proofmods[-1] if proofmods else 'Query']+sorted({'generated.'+arith[i] for i in ids if head(i)=='th-lemma'})
 lines=[*(f'import {s}' for s in imports),'set_option autoImplicit false','set_option warningAsError true','set_option maxRecDepth 20000','set_option maxHeartbeats 1500000','namespace Assembly','noncomputable section','open Classical']
 for i in ids:
  x=N[i];op=head(i);ds=x[1:-1];c=x[-1];H=set().union(*(hyps[j] for j in ds)) if ds else set()
  if op=='hypothesis':H={c}
  discharged=set()
  if op=='lemma':
   # Source lemma is a clause negating its discharged assumptions. Recognize exact literals only.
   clause=list(N[c][1:]) if isinstance(N[c],tuple) and head(c)=='or' else [c]
   for h in H:
    if any((isinstance(N[q],tuple) and head(q)=='not' and N[q][1]==h) or (isinstance(N[h],tuple) and head(h)=='not' and N[h][1]==q) for q in clause):discharged.add(h)
   H-=discharged
  hyps[i]=H
  bind=' '.join(f'(h{h} : {ref(h)})' for h in sorted(H))
  lines.append(f'theorem n{i} (_v : Vars) (_q : Query _v) {bind} : {ref(c)} := by')
  if op=='hypothesis':lines.append(f'  exact h{c}')
  elif op=='asserted':
   pos=assertions.index(i);pr='_q'
   for z in range(pos):pr=f'({pr}).2'
   if pos<len(assertions)-1:pr=f'({pr}).1'
   lines.append('  exact '+pr)
  else:
   if op=='lemma':
    lines.append(f'  by_contra hc')
    # Unfold only the clause and its negations for kernel-checked classical discharge.
    cs=[c]+([q for q in N[c][1:] if isinstance(N[c],tuple) and head(c)=='or'] if isinstance(N[c],tuple) else [])
    lines.append('  change ¬ '+expr(c)+' at hc')
    for h in sorted(discharged):lines.append(f'  have h{h} : {ref(h)} := by\n    '+('change '+expr(h)+'\n    ' if isinstance(N[h],tuple) and head(h)=='not' else '')+'tauto')
   for j in ds:lines.append(f'  have p{j} := n{j} _v _q '+ ' '.join(f'h{h}' for h in sorted(hyps[j])))
   if op=='lemma':lines.append(f'  exact p{ds[0]}')
   elif op=='th-lemma':
    leaves={}
    def local(j):
     z=N[j]
     if isinstance(z,str) and z not in ['true','false'] and not z.lstrip('-').isdigit() or isinstance(z,tuple) and head(j)=='ite' and sort[j]=='Int':leaves[j]=True;return f'w{j}'
     return expr(j,local,True)
    for z in [*map(lambda j:N[j][-1],ds),c]:local(z)
    lines.append(f'  exact FloorCertificate.node_{i} '+' '.join(ref(j) for j in sorted(leaves))+' '+' '.join(f'p{j}' for j in ds))
   else:
    # Shallow syntactic expansion preserves sharing while exposing the precise rule.
    expand=set()
    def expand_bool(j):
     if isinstance(N[j],tuple):
      expand.add(j)
      if head(j) in ['and','or','not','=','~']:
       for z in N[j][1:]:
        if sort[z]=='Prop':expand_bool(z)
    for z in [c,*[N[j][-1] for j in ds]]:expand_bool(z)
    if op=='rewrite':
     seen=set()
     def affine_unfold(z):
      if z in seen:return
      seen.add(z)
      if sort[z]=='Int':
       if isinstance(N[z],str):
        if N[z].lstrip('-').isdigit():expand.add(z)
       elif head(z)!='ite':
        expand.add(z)
        for a in N[z][1:]:affine_unfold(a)
      elif isinstance(N[z],tuple):
       for a in N[z][1:]:affine_unfold(a)
     affine_unfold(c)
    if op in ['intro-def','apply-def']:
     for z in list(expand):
      if head(z) in ['=','~']:
       for a in N[z][1:]:
        if a in fresh or isinstance(N[a],tuple) and head(a)=='ite':expand.add(a)
    lines.append('  simp only ['+', '.join(f'e{z}' for z in sorted(expand))+'] at *')
    lines.append('  '+('omega' if op=='rewrite' else 'tauto'))
  inventory.append(dict(node=i,rule=op,module=name,hyps=sorted(H),discharged=sorted(discharged),conclusion=c))
 lines.extend(['end','end Assembly']);(L/(name+'.lean')).write_text('\n'.join(lines)+'\n');proofmods.append(name)
(L/'assembly-inventory.json').write_text(json.dumps(inventory,indent=2)+'\n')
(L/'assembly-modules.json').write_text(json.dumps(['SemBase']+modules+['Query']+proofmods,indent=2)+'\n')
print('expressions',len(order),'definitions',len(fresh),'proofs',len(P),'root hypotheses',sorted(hyps[22671]))
