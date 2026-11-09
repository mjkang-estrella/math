import pathlib, shutil, json, hashlib
L=pathlib.Path(__file__).resolve().parent
F=L/'frozen/lanes/sol-floor-sums-source-formal-r1'
for n in ['Reduction.lean','Symmetry.lean','Source.lean','Expansion.lean','Audit.lean','verify_audit.py','lean_guard.py','pins.json']:
    shutil.copyfile(F/n,L/n)
pins=json.loads((L/'pins.json').read_text())
print(json.dumps(pins)[:5000])
N=[]
for line in (L/'frozen/lanes/sol-floor-sums-certificate-r2/dag.jsonl').open():
    d=json.loads(line); N.append(d.get('atom',tuple(d.get('args',[]))))
rules={'rewrite','asserted','mp','hypothesis','monotonicity','intro-def','trans','def-axiom','unit-resolution','th-lemma','lemma','apply-def','not-or-elim'}
def head(i):
    x=N[i]; return x if isinstance(x,str) else N[x[0]]
sort={}
for i,x in enumerate(N):
    if isinstance(x,str):
        if x in ['true','false']:sort[i]='Prop'
        elif x in ['m','H','t','a','b','c','d'] or x.startswith('z3name!') or x.lstrip('-').isdigit():sort[i]='Int'
    else:
        op=head(i)
        if op in rules:sort[i]='Proof'
        elif op in ['+','-','*']:sort[i]='Int'
        elif op=='ite':sort[i]=sort[x[2]]
        else:sort[i]='Prop'
def statement(i):
    leaves={}
    def expr(j):
        x=N[j]
        if isinstance(x,str):
            if x=='false':return 'False'
            if x=='true':return 'True'
            if x.lstrip('-').isdigit():return '('+x+' : ℤ)'
            leaves[j]='Int'; return 'v'+str(j)
        op=head(j);a=x[1:]
        if op=='ite' and sort[j]=='Int':
            leaves[j]='Int';return 'v'+str(j)
        e=[expr(v) for v in a]
        if op in ['+','*','and','or']:
            sep={'+':' + ','*':' * ','and':' ∧ ','or':' ∨ '}[op]
            return '('+sep.join(e)+')'
        if op=='-':return '(-'+e[0]+')' if len(e)==1 else '('+' - '.join(e)+')'
        if op in ['=','~','<=','>=','<','>']:
            sym= {'=':'↔' if sort[a[0]]=='Prop' else '=', '~':'↔' if sort[a[0]]=='Prop' else '=', '<=':'≤','>=':'≥','<':'<','>':'>'}[op]
            return '('+e[0]+' '+sym+' '+e[1]+')'
        if op=='not':return '(¬ '+e[0]+')'
        if op=='ite':return '(if '+e[0]+' then '+e[1]+' else '+e[2]+')'
        raise ValueError(op)
    x=N[i];con=expr(x[-1]);prem=[expr(N[j][-1]) for j in x[1:-1]]
    bind=' '.join('(v'+str(j)+' : ℤ)' for j in sorted(leaves))
    return bind, ' → '.join(prem+[con]),len(prem)
groups={}
for i,x in enumerate(N):
    if not isinstance(x,tuple) or head(i) not in ['th-lemma','rewrite','unit-resolution','def-axiom','not-or-elim']:continue
    groups.setdefault(head(i),[]).append(i)
(L/'generated').mkdir(exist_ok=True)
inventory=[]
for op,ids in groups.items():
    for k in range(0,len(ids),35):
        name=op.replace('-','_')+'_'+str(k//35)
        lines=['import Mathlib.Data.Int.Basic','import Lean.Elab.Tactic.Omega','import Mathlib.Tactic.Tauto','set_option autoImplicit false','set_option warningAsError true','set_option maxRecDepth 10000','set_option maxHeartbeats 1500000','namespace FloorCertificate']
        for i in ids[k:k+35]:
            b,s,np=statement(i)
            lines += [f'theorem node_{i} {b} : {s} := by']
            if np: lines += ['  intro '+ ' '.join('h'+str(j) for j in range(np))]
            lines += ['  '+('trivial' if s.split(' → ')[-1]=='True' else 'omega')]
            inventory.append({'node':i,'module':name,'rule':op})
        lines+=['end FloorCertificate']
        (L/'generated'/ (name+'.lean')).write_text('\n'.join(lines)+'\n')
(L/'generated-inventory.json').write_text(json.dumps(inventory,indent=2)+'\n')
print('generated',len(inventory),'local obligations')
