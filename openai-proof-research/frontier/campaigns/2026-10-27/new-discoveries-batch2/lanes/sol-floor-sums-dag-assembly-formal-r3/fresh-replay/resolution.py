from pathlib import Path
import json,re,shutil,sys
L=Path(__file__).resolve().parent
N=[d.get('atom',tuple(d.get('args',[]))) for d in map(json.loads,(L/'frozen/sol-floor-sums-certificate-r2/dag.jsonl').open())]
def head(i):return N[i] if isinstance(N[i],str) else head(N[i][0])
def clause(i):return list(N[i][1:]) if isinstance(N[i],tuple) and head(i)=='or' else [i]
def injection(k,n,pr):
 if k<n-1:pr=f'(Or.inl {pr})'
 for _ in range(k):pr=f'(Or.inr {pr})'
 return pr
def atom(i):return f'(e{i} _v)'
def literal(i):return '(¬ '+atom(N[i][1])+')' if head(i)=='not' else atom(i)
changed=unhandled=0
for f in sorted(L.glob('Dag*.lean')):
 if f.with_suffix('.olean').exists() or f.name in sys.argv[1:]:continue
 parts=re.split(r'(?=theorem n\d+ )',f.read_text());out=[parts[0]];modified=False
 for p in parts[1:]:
  i=int(re.match(r'theorem n(\d+)',p)[1]);op=head(i);ds=N[i][1:-1];c=N[i][-1]
  if op=='unit-resolution' and '  simp only' in p:
   cs=clause(N[ds[0]][-1]);target=clause(c);proof=[];ok=True
   for lit in cs:
    if lit==c:proof.append('hlit');continue
    if lit in target:proof.append(injection(target.index(lit),len(target),'hlit'));continue
    found=None
    for d in ds[1:]:
     q=N[d][-1]
     if head(q)=='not' and N[q][1]==lit:found=f'(False.elim (p{d} hlit))';break
     if head(lit)=='not' and N[lit][1]==q:found=f'(False.elim (hlit p{d}))';break
    if found is None:ok=False;break
    proof.append(found)
   if ok:
    cut=p.index('  simp only');tail='end\nend Assembly\n' if p.endswith('end\nend Assembly\n') else ''
    changes=''.join(f'  change {literal(N[d][-1])} at p{d}\n' for d in ds[1:] if head(N[d][-1])=='not')
    main=' ∨ '.join(literal(j) for j in cs)
    body=f'  change {main} at p{ds[0]}\n'+changes
    if len(cs)>1:
     body+=f'  rcases p{ds[0]} with '+' | '.join('hlit' for _ in cs)+'\n'
     body+=''.join('  · exact '+pr+'\n' for pr in proof)
    else:body+=f'  have hlit := p{ds[0]}\n  exact {proof[0]}\n'
    p=p[:cut]+body+tail;modified=True;changed+=1
   else:unhandled+=1
  out.append(p)
 if modified:
  dest=L/'attempts/direct-resolution'/f.name;dest.parent.mkdir(parents=True,exist_ok=True)
  if not dest.exists():shutil.copyfile(f,dest)
  f.write_text(''.join(out))
print('direct resolution proofs',changed,'remaining tactic rules',unhandled)
