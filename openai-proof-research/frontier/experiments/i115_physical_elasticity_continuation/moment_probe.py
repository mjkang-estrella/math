from fractions import Fraction
from itertools import product

def monos(r):return [(i,j,r-i-j) for i in range(r+1) for j in range(r-i+1)]
def matrix(r, gauge=True):
 # Unknown D_{bq} degree r plus t_b degree r-1; impose TF sym grad D = C*t and tr D=0.
 ms=monos(r);low=monos(r-1);keys=[('D',b,q,m) for b in range(3) for q in range(3) for m in ms]+[('t',b,m) for b in range(3) for m in low];idx={k:i for i,k in enumerate(keys)};rows=[]
 def add(row,k,c):row[idx[k]]=row.get(idx[k],0)+c
 def deriv(row,b,q,a,m,c):
  n=list(m);n[a]+=1;add(row,('D',b,q,tuple(n)),c*n[a])
 for q in range(3):
  for a in range(3):
   for b in range(a,3):
    for m in low:
     row={};deriv(row,b,q,a,m,3);deriv(row,a,q,b,m,3)
     if a==b:
      for j in range(3):deriv(row,j,q,j,m,-2)
     if a==q:add(row,('t',b,m),-3)
     if b==q:add(row,('t',a,m),-3)
     if a==b:add(row,('t',q,m),2)
     rows.append(row)
 if gauge:
  for m in ms:
   row={}
   for b in range(3):add(row,('D',b,b,m),1)
   rows.append(row)
 return rows,keys
def rank(rows):
 piv={}
 for orig in rows:
  row={k:Fraction(v) for k,v in orig.items() if v}
  while row:
   j=min(row);v=row[j]
   if j not in piv:
    piv[j]={k:w/v for k,w in row.items()};break
   for k,w in piv[j].items():
    z=row.get(k,0)-v*w
    if z:row[k]=z
    elif k in row:del row[k]
 return len(piv)
if __name__=='__main__':
 for r in range(1,6):
  a,k=matrix(r);rk=rank(a);print(r,(len(a),len(k)),rk,'kernel',len(k)-rk,flush=True)
