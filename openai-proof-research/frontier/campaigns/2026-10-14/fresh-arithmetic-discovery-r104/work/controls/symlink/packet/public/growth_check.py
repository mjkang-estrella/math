#!/usr/bin/env python3
"""Read-only finite GF(4) diagnostic; no external packages, randomness, or writes.
Field elements encode a+b*w as a+2*b, w^2=w+1. Not a general proof.
"""
import json
MUL=((0,0,0,0),(0,1,2,3),(0,2,3,1),(0,3,1,2))
INV=(0,1,3,2)
def eye(n):return [[int(i==j) for j in range(n)] for i in range(n)]
def add(A,B):return [[a^b for a,b in zip(x,y)] for x,y in zip(A,B)]
def scale(a,A):return [[MUL[a][b] for b in row] for row in A]
def matmul(A,B):
 C=[[0]*len(B[0]) for _ in A]
 for i,row in enumerate(A):
  for k,a in enumerate(row):
   if a:
    tab=MUL[a]
    for j,b in enumerate(B[k]):
     if b:C[i][j]^=tab[b]
 return C
def kron(A,B):return [[MUL[a][b] for a in rowA for b in rowB] for rowA in A for rowB in B]
def rref(A):
 A=[row[:] for row in A];piv=[];r=0
 for c in range(len(A[0]) if A else 0):
  k=next((i for i in range(r,len(A)) if A[i][c]),None)
  if k is None:continue
  A[r],A[k]=A[k],A[r];A[r]=[MUL[INV[A[r][c]]][v] for v in A[r]]
  for i in range(len(A)):
   if i!=r and A[i][c]:
    tab=MUL[A[i][c]];A[i]=[v^tab[w] for v,w in zip(A[i],A[r])]
  piv.append(c);r+=1
  if r==len(A):break
 return A,piv
def rank(A):return len(rref(A)[1])
def nullcols(A):
 R,piv=rref(A);n=len(A[0]);free=[j for j in range(n) if j not in piv];vec=[]
 for j in free:
  v=[0]*n;v[j]=1
  for i,c in enumerate(piv):v[c]=R[i][j]
  vec.append(v)
 return [[v[i] for v in vec] for i in range(n)]
def tensor(X,Y):return tuple(kron(a,b) for a,b in zip(X,Y))
def direct(X,Y):
 out=[]
 for a,b in zip(X,Y):out.append([row+[0]*len(b) for row in a]+[[0]*len(a)+row for row in b])
 return tuple(out)
def V(mu):return ([[1,0],[1,1]],[[1,0],[mu,1]])
def core_dim(X):
 n=len(X[0]);N=matmul(add(X[0],eye(n)),add(X[1],eye(n)))
 return n-4*rank(N)
def cohom_profile(X):
 # Group basis (1,g1,g2,g1*g2); interpolation for lambda=(1,w).
 lam=[0,1,2,3]
 def power(x,n):
  a=1
  for _ in range(n):a=MUL[a][x]
  return a
 B=[[power(x,a) for x in lam] for a in range(4)]
 R,piv=rref([B[i]+eye(4)[i] for i in range(4)]);assert piv[:4]==[0,1,2,3]
 Bi=[row[4:] for row in R];n=len(X[0]);Gs=[eye(n),X[0],X[1],matmul(*X)]
 cs=[]
 for j in [1,2]:
  C=[[0]*n for _ in range(n)]
  for i in range(4):C=add(C,scale(Bi[i][j],Gs[i]))
  cs.append(C)
 c0,c1=cs;assert rank(matmul(c0,c0))==rank(matmul(c1,c1))==0
 assert matmul(c0,c1)==matmul(c1,c0)
 r1=rank(c1);K=nullcols(c1);cK=matmul(c0,K)
 dB1=n-2*r1;rB1=rank([u+v for u,v in zip(c1,cK)])-r1
 dB2=r1;rB2=rank(matmul(c0,c1))
 h=[dB1-2*rB1,rB1,dB2-2*rB2,rB2]
 assert all(x>=0 for x in h) and h[0]+2*h[1]+2*h[2]+4*h[3]==n
 return {'h_a_0_to_3':h,'beta_coefficients_1_sqrt2':h[:2]}
def mv(A,v):return [sum(a*b for a,b in zip(row,v)) for row in A]
def main():
 S=V(2);other=V(3);one=(eye(1),eye(1))
 # Augmentation ideal with basis x,y,xy.
 omega=([[1,0,0],[0,1,0],[0,1,1]],[[1,0,0],[0,1,0],[1,0,1]])
 cases=[('same_point',S,[[0,2],[1,0]],6),('different_point',other,[[0,0],[0,0]],4),('syzygy',omega,[[1,0],[0,1]],4),('unit_plus_seed',direct(one,S),[[1,2],[1,1]],4)]
 records=[]
 for name,X,A,N in cases:
  Y=S;v=[1,0];got=[];expected=[]
  for n in range(N+1):
   assert len(Y[0])<=256
   got.append(core_dim(Y));expected.append(2*v[0]+4*v[1])
   if n<N:Y=tensor(Y,X);v=mv(A,v)
  assert got==expected,(name,got,expected)
  records.append({'case':name,'transition_matrix':A,'core_dimensions_n0_onward':got,'profile':cohom_profile(X)})
 return {'status':'finite diagnostic passed','field':'F_4=w^2+w+1','group':'C_2^2; group Hopf tensor product','max_matrix_dimension':max(2*len(x[1][0])**x[3] for x in cases),'cases':records,'limits':'Only the displayed finite matrices and bounded powers; not a proof, independent review, global growth comparison, or substantiality gate.'}
if __name__=='__main__':print(json.dumps(main(),indent=2))
