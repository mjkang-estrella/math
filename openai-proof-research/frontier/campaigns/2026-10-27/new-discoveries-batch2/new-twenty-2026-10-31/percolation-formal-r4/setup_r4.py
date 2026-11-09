from pathlib import Path
import hashlib,json,itertools
R=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/percolation-formal-r4')
S=R/'packet/src'; old=R.parent/'percolation-formal-r3'
expected={'normalized.cnf':'dd13788f1c58d988201ca15ce7fa993df1c3b4454e2fc8fd193d6b374527fccc','normalized-trimmed.json':'0a076e5f03ee0bdd50e25e5c8eb0d6204fa0475af19402af795531c0a383f1d7'}
receipts={}
for n in ['normalized.cnf','normalized.lrat','normalized-trimmed.json']:
 b=(old/n).read_bytes(); h=hashlib.sha256(b).hexdigest()
 if n in expected: assert h==expected[n]
 (R/n).write_bytes(b); assert hashlib.sha256((R/n).read_bytes()).hexdigest()==h
 receipts[n]=h
(R/'certificate-sha256.json').write_text(json.dumps(receipts,indent=2))
V=[(1,y,z) for y in range(5) for z in range(5)]+[(0,1,z) for z in range(5)]+[(0,0,1)]
def norm(v):
 a=next(x for x in v if x%5); return tuple(x*pow(a,-1,5)%5 for x in v)
def det(c):
 a,b,d=c
 return (a[0]*(b[1]*d[2]-b[2]*d[1])-b[0]*(a[1]*d[2]-a[2]*d[1])+d[0]*(a[1]*b[2]-a[2]*b[1]))%5
def make(cols):
 p=[V.index(norm([sum(cols[j][i]*v[j] for j in range(3))%5 for i in range(3)])) for v in V]
 inv=[p.index(i) for i in range(31)]
 # line map uniquely determined by incidence preservation
 inc=lambda a,b:sum(a[i]*b[i] for i in range(3))%5==0
 lines=[next(k for k in range(31) if all(inc(V[p[x]],V[k])==inc(V[x],V[l]) for x in range(31))) for l in range(31)]
 return p,inv,lines,[lines.index(i) for i in range(31)]
mods=[]; names={}
for kind,inds in [('F',range(31)),('G',range(1,31)),('H',[i for i in range(31) if V[i][2]!=0])]:
 names[kind]={}
 for i in inds:
  if kind=='F':cols=next((V[i],b,c) for b in V for c in V if det((V[i],b,c)))
  elif kind=='G':cols=next((V[0],V[i],c) for c in V if det((V[0],V[i],c)))
  else:cols=(V[0],V[25],V[i])
  p,pi,l,li=make(cols); name=f'Coll{kind}{i:02d}';mods.append(name);names[kind][i]=name
  out=['import Collineation','namespace Percolation','set_option maxRecDepth 10000','set_option maxHeartbeats 0']
  for k,v in [('p',p),('pi',pi),('l',l),('li',li)]:
   out += [f'def {name}_{k} (x : Points 5) : Points 5 := ({str(v)} : List (Points 5)).getD x.val 0']
  out += [f'def {name} : Collineation5 where',f'  p := {name}_p',f'  pinv := {name}_pi',f'  l := {name}_l',f'  linv := {name}_li','  pp := by decide','  pi := by decide','  ll := by decide','  li := by decide','  perm := by decide','  incidence_preserved := by decide','end Percolation']
  (S/(name+'.lean')).write_text('\n'.join(out)+'\n')
out=[f'import {m}' for m in mods]+['namespace Percolation','set_option maxRecDepth 100000','set_option maxHeartbeats 0']
for kind in names:
 vals=[names[kind].get(i,'CollF00') for i in range(31)]
 out += [f'def family{kind} (x : Points 5) : Collineation5 := ([{",".join(vals)}] : List Collineation5).getD x.val CollF00']
out += ['theorem familyF_spec : ∀ p : Points 5, (familyF p).p 0 = p := by decide',
 'theorem familyG_spec : ∀ p : Points 5, p ≠ 0 → (familyG p).p 0 = 0 ∧ (familyG p).p 25 = p := by decide',
 'theorem familyH_spec : ∀ p : Points 5, incidence p 30 = false → (familyH p).p 0 = 0 ∧ (familyH p).p 25 = 25 ∧ (familyH p).p 30 = p := by decide',
 'end Percolation']
(S/'CollineationFamily.lean').write_text('\n'.join(out)+'\n')
(R/'family-order.txt').write_text('\n'.join(mods+['CollineationFamily'])+'\n')
print('generated',len(mods),'collineations')
