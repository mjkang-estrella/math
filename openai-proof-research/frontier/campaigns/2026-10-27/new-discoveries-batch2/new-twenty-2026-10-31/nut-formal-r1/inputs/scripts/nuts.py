import pathlib,itertools,json,numpy as np,sympy as sp
L=pathlib.Path(__file__).resolve().parents[1];out={'underlying':0,'augmented_labeled_over_catalogue':0,'signed_matrices':0,'singular':0,'full_nullity_one':[]}
def decode(s):
 n=ord(s[0])-63;bits=[(ord(c)-63)>>j&1 for c in s[1:] for j in range(5,-1,-1)];A=np.zeros((n,n),dtype=int);k=0
 for j in range(1,n):
  for i in range(j):A[i,j]=A[j,i]=bits[k];k+=1
 return A
def augment(A,edges,k,deficits):
 if k==len(edges):
  B=A.copy()
  for i,d in enumerate(deficits):B[i,i]=d
  yield B;return
 i,j=edges[k]
 yield from augment(A,edges,k+1,deficits)
 if deficits[i] and deficits[j]:
  A[i,j]=A[j,i]=2;d=deficits.copy();d[i]-=1;d[j]-=1;yield from augment(A,edges,k+1,d);A[i,j]=A[j,i]=1
for s in (L/'sources/graph8.g6').read_text().splitlines():
 A=decode(s);degs=A.sum(axis=1)
 if max(degs)>3:continue
 # connectivity
 seen={0}
 while True:
  t=seen|{j for i in seen for j in range(8) if A[i,j]}
  if t==seen:break
  seen=t
 if len(seen)<8:continue
 out['underlying']+=1;edges=[(i,j) for j in range(8) for i in range(j) if A[i,j]]
 # fixed positive spanning tree implements switching reduction
 tree=set();seen={0}
 while len(seen)<8:
  for i,j in edges:
   if (i in seen)!=(j in seen):tree.add((i,j));seen|={i,j};break
 for B in augment(A.copy(),edges,0,list(3-degs)):
  out['augmented_labeled_over_catalogue']+=1
  vals=np.linalg.eigvalsh(B.astype(float));null=int((abs(vals)<1e-7).sum())
  if null:
   ns=sp.Matrix(B).nullspace()
   if len(ns)!=1 or any(x==0 for x in ns[0]):continue
  signs=[e for e in edges if e not in tree]+[(i,i) for i in range(8) if B[i,i]]
  for sig in itertools.product([1,-1],repeat=len(signs)):
   C=B.copy()
   for (i,j),v in zip(signs,sig):C[i,j]=C[j,i]=v*B[i,j]
   out['signed_matrices']+=1
   if min(abs(np.linalg.eigvalsh(C.astype(float))))>1e-7:continue
   out['singular']+=1;ns=sp.Matrix(C).nullspace()
   if len(ns)==1 and all(x!=0 for x in ns[0]):
    out['full_nullity_one'].append({'quotient':B.tolist(),'signed':C.tolist(),'null':[str(x) for x in ns[0]]})
 (L/'outputs/nuts.json').write_text(json.dumps(out,indent=2))
 print(out['underlying'],out['signed_matrices'],len(out['full_nullity_one']),flush=True)
print('DONE',out['underlying'],out['augmented_labeled_over_catalogue'],out['signed_matrices'],len(out['full_nullity_one']))
