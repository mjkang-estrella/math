from pathlib import Path
import itertools,json,re
r=Path(__file__).resolve().parents[1]
rows=json.loads((r/'inputs/reconciliation.json').read_text())['per_support']
def det(a):
 a=[row[:] for row in a]; n=len(a); d=1; sg=1
 for k in range(n-1):
  if a[k][k]==0:
   j=next((j for j in range(k+1,n) if a[j][k]),None)
   if j is None:return 0
   a[k],a[j]=a[j],a[k];sg=-sg
  v=a[k][k]
  for i in range(k+1,n):
   for j in range(k+1,n):a[i][j]=(v*a[i][j]-a[i][k]*a[k][j])//d
  for i in range(k+1,n):a[i][k]=0
  d=v
 return sg*a[-1][-1]
def lit(a):return '!!['+'; '.join(', '.join(map(str,row)) for row in a)+']'
records=[];supports=[];mods=[]
for k,row in enumerate(rows):
 code=row['code']; order=row['bfs_order'];p=row['parents']; edges=[(i,j) for i in range(8) for j in range(i+1,8) if code>>(8*order[i]+order[j])&1]
 # Check against the actual inherited, kernel-checked tree record text.
 text=''.join((r/'formal'/f'CatalogueTrees{t:03}.lean').read_text() for t in range(20))
 assert f'({code}, {order}, {p})' in text
 mats={};unsigned=[]
 for doubles in itertools.product([0,1],repeat=len(edges)):
  a=[[0]*8 for _ in range(8)]
  for (i,j),d in zip(edges,doubles):a[i][j]=a[j][i]=1+d
  dg=[3-sum(x) for x in a]
  if not all(0<=d<=2 for d in dg):continue
  for i in range(8):a[i][i]=dg[i]
  unsigned.append(a)
  free=[(i,j) for i,j in edges if p[j]!=i]+[(i,i) for i in range(8) if dg[i]==2]
  for signs in itertools.product([1,-1],repeat=len(free)):
   for s in [1,-1]:
    b=[x[:] for x in a]
    for i in range(8):
     if dg[i]==1:b[i][i]=s
    for (i,j),v in zip(free,signs):b[i][j]=b[j][i]=v*a[i][j]
    mats[tuple(x for row in b for x in row)]=b
 ids=[]
 for a in mats.values():
  n=len(records); c=dict(id=n,support=k,code=code,matrix=a);v=det(a)
  if v:c['det']=v
  else:
   i=next((i for i in range(8) if det([[a[j][l] for l in range(8) if l!=i] for j in range(8) if j!=i])==0),None)
   if i is None:raise SystemExit('PerSupport obstruction failed at '+str(c))
   c['zero_principal_minor']=i
  records.append(c);ids.append(n)
 assert len(mats)==row['normalized'] and len(unsigned)==row['unsigned_patterns']
 supports.append(dict(index=k,code=code,order=order,parents=p,ids=ids,unsigned=len(unsigned)))
(r/'new-certificates.json').write_text(json.dumps(records,separators=(',',':'))+'\n')
(r/'new-supports.json').write_text(json.dumps(supports,indent=2)+'\n')
for start in range(0,len(records),32):
 name=f'NewCertificates{start//32:04}';mods.append(name)
 lines=['import VerifiedDet',f'namespace Nut8.{name}']
 for c in records[start:start+32]:
  n=c['id'];lines.append(f'def C{n} : QuotientMatrix := {lit(c["matrix"])}'.replace('QuotientMatrix','Matrix (Fin 8) (Fin 8) ℤ'))
  if 'det' in c:
   st=f'C{n}.det = ({c["det"]} : ℤ)';rule='sparseDet_eq_det'
   proof=f'  intro h\n  have := certificate{n}\n  rw [h.1] at this\n  norm_num at this'
  else:
   i=c['zero_principal_minor'];st=f'C{n}.adjugate {i} {i} = 0';rule='sparseDet_principal'
   proof=f'  intro h\n  exact h.2 {i} certificate{n}'
  lines += [f'theorem certificate{n} : {st} := by',f'  rw [← {rule}]','  decide +kernel',f'theorem obstruction{n} : ¬ (C{n}.det = 0 ∧ ∀ i, C{n}.adjugate i i ≠ 0) := by',proof]
 lines.append(f'end Nut8.{name}');(r/'formal'/(name+'.lean')).write_text('\n'.join(lines)+'\n')
(r/'new-certificate-modules.json').write_text(json.dumps(mods,indent=2)+'\n')
for sp in supports:
 k=sp['index'];name=f'FiniteSupport{k:03}';ids=sp['ids'];refs=[f'NewCertificates{n//32:04}.C{n}' for n in ids]
 lines=['import SignedCatalogue']+[f'import NewCertificates{b:04}' for b in sorted({n//32 for n in ids})]+[f'namespace Nut8.{name}',f'noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv {sp["order"]} (by decide +kernel)',f'def p : Fin 8 → Fin 8 := ![{", ".join(map(str,sp["parents"]))}]',f'def matrices : Finset QuotientMatrix := {{{", ".join(refs)}}}',f'theorem enumeration : signedCatalogue {sp["code"]} e p = matrices := by','  decide +kernel',f'end Nut8.{name}']
 (r/'formal'/(name+'.lean')).write_text('\n'.join(lines)+'\n')
report=dict(supports=len(supports),unsigned=sum(s['unsigned'] for s in supports),normalized=len(records),nonsingular=sum('det' in c for c in records),singular=sum('zero_principal_minor' in c for c in records),r2_total=9172,difference=len(records)-9172,explanation='Same 9172 representatives after checked BFS permutation, with each tree edge positive. Entries were regenerated, and determinant/minor witnesses recomputed by exact Bareiss elimination; no r2 certificate list was read. Semi signs are deduplicated when no magnitude-one diagonal exists.')
(r/'new-reconciliation.json').write_text(json.dumps(report,indent=2)+'\n');print(report)
