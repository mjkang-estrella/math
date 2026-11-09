import json, pathlib, re, ast, hashlib
root=pathlib.Path(__file__).resolve().parents[1]; packet=root.parent/'conference-mds-resume-r4'
c=json.loads((packet/'data/cex20_certificate.json').read_text()); W=c['W']; p=19; n=20
assert len(W)==n and all(len(r)==n for r in W)
assert all(W[i][j] in ((0,) if i==j else (-1,1)) for i in range(n) for j in range(n))
assert all(sum(W[i][k]*W[j][k] for k in range(n))==(19 if i==j else 0) for i in range(n) for j in range(n))
assert all(W[i][j]==-W[j][i] for i in range(n) for j in range(n))
rows=[sum(x!=0 for x in r) for r in W]; cols=[sum(W[i][j]!=0 for i in range(n)) for j in range(n)]; assert rows==cols==[19]*20
# Fresh elementary Gauss-Jordan elimination; no author verification imports or inverse certificate.
A=[[x%p for x in row] for row in W]; piv=[]; k=0
for j in range(n):
 s=next((i for i in range(k,n) if A[i][j]),None)
 if s is None: continue
 A[k],A[s]=A[s],A[k]; inv=pow(A[k][j],-1,p); A[k]=[(x*inv)%p for x in A[k]]
 for i in range(n):
  if i!=k:
   t=A[i][j]; A[i]=[(x-t*y)%p for x,y in zip(A[i],A[k])]
 piv.append(j); k+=1
assert k==10
lean=(packet/'lean/ConferenceMDS324342.lean').read_text()
x=[5,7,13,9,0,15,14,2,8,18]+[0]*10
word=[sum(x[i]*W[i][j] for i in range(n))%p for j in range(n)]
assert word==[0,0,0,0,0,15,0,0,10,1,18,0,9,0,18,14,5,15,0,0] and any(word) and sum(t!=0 for t in word)==9
seedword=[sum(c['x'][i]*W[i][j] for i in range(n))%p for j in range(n)]
assert seedword==c['word']
seedweight=sum(v!=0 for v in seedword)
# Also reduce word by independently obtained row echelon basis.
z=word[:]
for r,j in zip(A,piv):
 t=z[j]; z=[(v-t*w)%p for v,w in zip(z,r)]
assert not any(z)
lean=(packet/'lean/ConferenceMDS324342.lean').read_text(); embedded=ast.literal_eval(re.search(r'def Wrows : List \(List ℤ\) := (\[.*?\])\n\ndef W20',lean,re.S)[1]); assert W==embedded
old=root.parent/'fresh-corpus-r3/conference'; matches=[]
for f in old.rglob('*.json'):
 try:
  d=json.loads(f.read_text())
  if isinstance(d,dict) and d.get('W')==W: matches.append(str(f))
 except (ValueError,UnicodeError): pass
assert matches
# Normalize columns by the first row's signs, preserving zero location and every Hamming weight.
signs=[1 if v==0 else v for v in W[0]]; N=[[v*signs[j] for j,v in enumerate(row)] for row in W]
assert N[0]==[0]+[1]*19
nw=[v*signs[j]%p for j,v in enumerate(word)]; assert sum(v!=0 for v in nw)==9
result={'seed_certificate_weight':seedweight,'checks':'PASS','field':19,'order':20,'gram':'19I','rank':k,'pivots':piv,'row_counts':rows,'column_counts':cols,'word':word,'support':[j for j,v in enumerate(word) if v],'membership':'explicit combination plus independent RREF reduction','singleton':20-k+1,'same_r3_witness':matches,'normal_form_first_row':N[0],'normalized_word':nw,'exact_d9':'not audited; only d<=9 established','self_dual':'follows from dimension 10 and Gram zero mod19'}
(root/'independent-checks/witness.json').write_text(json.dumps(result,indent=2)); print(json.dumps(result,indent=2))
