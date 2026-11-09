from pathlib import Path
import json,functools
L=Path(__file__).resolve().parent
N=[d.get('atom',tuple(d.get('args',[]))) for d in map(json.loads,(L/'frozen/sol-floor-sums-certificate-r2/dag.jsonl').open())]
def head(i):return N[i] if isinstance(N[i],str) else head(N[i][0])
@functools.lru_cache(None)
def poly(i):
 x=N[i]
 if isinstance(x,str):
  if x.lstrip('-').isdigit():return {'constant':int(x)}
  return {x:1}
 op=head(i);a=x[1:]
 if op in ['+','-']:
  out={}
  for k,j in enumerate(a):
   sign=-1 if op=='-' and (k or len(a)==1) else 1
   for v,c in poly(j).items():out[v]=out.get(v,0)+sign*c
  return {v:c for v,c in out.items() if c}
 assert op=='*';out={'constant':1}
 for j in a:
  b=poly(j)
  if set(b)<= {'constant'}:out={v:c*b.get('constant',0) for v,c in out.items()}
  else:assert set(out)<= {'constant'};out={v:c*out.get('constant',0) for v,c in b.items()}
 return out
def raw(i):
 x=N[i]
 if isinstance(x,str):
  if x.lstrip('-').isdigit():return f'({x} : ℤ)'
  return {'m':'(m : ℤ)','H':'(H : ℤ)','a':'(a 0 : ℤ)','b':'(a 1 : ℤ)','c':'(a 2 : ℤ)','d':'(a 3 : ℤ)'}[x]
 a=[raw(j) for j in x[1:]];op=head(i)
 if op=='-' and len(a)==1:return '(-'+a[0]+')'
 return '('+{'*':' * ','+':' + ','-':' - '}[op].join(a)+')'
header='\n'.join((L/'SourceBridge.lean').read_text().splitlines()[:10])+'\n'
lines=[header]
for i,z,*_ in json.loads((L/'clip-inventory.json').read_text()):
 p=poly(z);assert p.pop('H')==1;lev=-p.pop('m');assert lev in range(1,5)
 entries=[f'(a {j} : ℤ)' for j,v in enumerate('abcd') if p.pop(v,0)]
 assert not p
 s=entries[-1] if entries else '(0 : ℤ)'
 for e in reversed(entries[:-1]):s=f'({e} + {s})'
 target=f'({s} + (H : ℤ) - {lev} * (m : ℤ))'
 lines += [f'theorem canonical_{i} (m H : ℕ) (a : Fin 4 → ℕ) : e{i} (sourceEnv m H a) = FloorSums.clip H {target} := by',f'  rw [clip_{i} _ H rfl]', '  congr 1',f'  change {raw(z)} = {target}','  omega']
old=(L/'SourceBridge.lean').read_text();body=old[old.index('theorem sum_match'):]
body=body.replace('Finset.not_mem_empty','Finset.notMem_empty')
for i,*_ in json.loads((L/'clip-inventory.json').read_text()):body=body.replace(f'rw [clip_{i} _ H rfl]',f'rw [canonical_{i}]')
idx=body.rindex('  simp only [e');body=body[:idx]+'  simp only [one_mul, neg_mul, neg_one_mul]\n  abel\nend Assembly\n'
(L/'SourceBridge.lean').write_text('\n'.join(lines)+'\n'+body)
print('64 bounded canonical argument identities; no global AC sorting')
