from check import *

def square2(rows):
 out=[]
 for row in rows:
  r=0
  while row:
   bit=row&-row;r^=rows[bit.bit_length()-1];row^=bit
  out.append(r)
 return out

def plus_unipotent(A):
 rows=[sum((v%2)<<j for j,v in enumerate(row))^(1<<i) for i,row in enumerate(A)]
 for _ in range((len(A)-1).bit_length()):rows=square2(rows)
 return not any(rows)

def main():
 import sympy as S
 t=S.Symbol('t');tested=0;mod2=0;records=[];found=[]
 for d in range(3,25):
  for p0 in range(1,d-1):
   for p1 in range(1,d-p0):
    p=(p0,p1,d-p0-p1)
    for a in range(max(p),d-max(p)+1):
     if a==p[0]:continue
     s=(a,d-a);ts,A=matrix(s,p);tested+=1
     if not plus_unipotent(A):continue
     mod2+=1;N=len(A)
     # exact Newton necessary conditions, before any characteristic polynomial
     A2=mul(A,A)
     if tr(A2)!=N:continue
     A4=mul(A2,A2)
     if tr(A4)!=N:continue
     f=S.Poly(S.Matrix(A).charpoly(t).as_expr(),t)
     g=f
     for root in [1,-1]:
      while g.eval(root)==0:g=g.exquo(S.Poly(t-root,t))
     rec={'s':s,'p':p,'N':N,'charpoly':str(f.as_expr().factor()),'remaining_degree':g.degree()};found.append(rec)
  records.append({'degree':d,'cumulative_pairs':tested,'mod2_survivors':mod2})
 result={'status':'PASS','scope':'all positive reduced nontriangular 2x3 pairs degree3..24','coverage':records,'survivors_of_mod2_and_two_even_moments':found,'source_counterexample_found':any(x['remaining_degree']==0 for x in found)}
 (P/'spectral-probe.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
if __name__=='__main__':main()
