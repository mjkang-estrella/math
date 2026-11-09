import pathlib,json
D=pathlib.Path(__file__).resolve().parents[1];cert=json.loads((D/'outputs/totient-stage4-certificate.json').read_text());T={int(k):v for k,v in cert['children'].items()}
adj={v:set(ws) for v,ws in T.items()}
for v,ws in T.items():
 for w in ws:adj[w].add(v)
def canon(v,p):return '('+''.join(sorted(canon(w,v) for w in adj[v] if w!=p))+')'
def traverse(v,p):
 out=[v]
 for w in sorted(adj[v]-{p},key=lambda x:canon(x,v)):out+=traverse(w,v)
 return out
labels=traverse(cert['centre'],-1);assert len(labels)==88
phi={r['n']:r['phi'] for r in cert['vertices']};par=[labels.index(phi[v]) for v in labels]
# Independent graph shape identity encoded by generated Tree, then finite edge equivalence.
(D/'outputs/lean-label-order.json').write_text(json.dumps({'labels':labels,'phi_index':par},indent=2))
def factors(n):
 out=[];p=2
 while p*p<=n:
  e=0
  while n%p==0:e+=1;n//=p
  if e:out.append((p,e))
  p+=1
 if n>1:out.append((n,1))
 return out
todo=set(labels)
for n in list(todo):
 x=n
 for p,e in factors(n):x//=p**e;todo.add(x)
def tot(n):
 z=n
 for p,e in factors(n):z=z//p*(p-1)
 return z
s='import Definitions\nimport Mathlib.Tactic.NormNum.Prime\nnamespace R162\n'
for n in sorted(todo):
 if n==1:s+='theorem phi_1 : Nat.totient 1 = 1 := Nat.totient_one\n';continue
 p,e=factors(n)[0];rest=n//p**e
 s+=f'theorem phi_{n} : Nat.totient {n} = {tot(n)} := by\n'
 if rest==1:
  s+=f'  rw [show {n} = {p}^{e} by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]\n  norm_num\n'
 else:
  s+=f'  rw [show {n} = {p}^{e} * {rest} by norm_num, Nat.totient_mul (by norm_num), Nat.totient_prime_pow (by norm_num) (by norm_num), phi_{rest}]\n  norm_num\n'
s+='end R162\n';(D/'lean/Arithmetic.lean').write_text(s)
s='import Arithmetic\nnamespace R162\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\ndef labels : Fin 88 → ℕ := !['+','.join(map(str,labels))+']\ndef next : Fin 88 → Fin 88 := !['+','.join(map(str,par))+']\n'
s+='theorem size_four : size (nanostar 4) = 88 := by decide\n'
s+='theorem phi_labels : ∀ i : Fin 88, Nat.totient (labels i) = labels (next i) := by\n intro i\n fin_cases i <;> simp only [labels, next, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.empty_val, '+', '.join('phi_'+str(n) for n in sorted(set(labels)))+']\n'
s+='end R162\n';(D/'lean/Certificate.lean').write_text(s)
print('arithmetic lemmas',len(todo))
# Final syntax/proof normalization for this pinned mathlib.
p=D/'lean/Arithmetic.lean';p.write_text(p.read_text().replace('Nat.totient_mul (by norm_num)','Nat.totient_mul (by decide)'))
p=D/'lean/Certificate.lean';s=p.read_text().replace('import Arithmetic\n','import Arithmetic\nimport Mathlib.Data.Fin.VecNotation\n').replace('simp only [labels, next, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.empty_val,','norm_num [labels, next,');p.write_text(s)
