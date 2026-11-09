import pathlib,json,math,mpmath as mp
L=pathlib.Path(__file__).resolve().parent;mp.mp.dps=65
def k(d,M):
 if d>=mp.pi:return mp.mpf(0)
 A=-mp.pi/2;B=mp.pi/2-d;s=mp.mpc(0)
 for a in range(M+1):
  for b in range(M-1):
   f=2*M-2-2*a-2*b
   I=B-A if f==0 else (mp.exp(1j*f*B)-mp.exp(1j*f*A))/(1j*f)
   s+=math.comb(M,a)*math.comb(M-2,b)*mp.exp(1j*(M-2*a)*d)*I
 return mp.re(s)/2**(2*M-2)
out=[]
for row in json.loads((L/'gram-results.json').read_text()):
 M=row['M'];g=[mp.mpf(str(v)) for v in row['gaps']];scale=mp.pi/min(sum(g[i:i+M]) for i in range(len(g)-M+1));g=[v*scale for v in g];x=[mp.mpf(0)]
 for v in g:x.append(x[-1]+v)
 A=mp.matrix([[k(abs(a-b),M) for b in x] for a in x]);e=mp.eigsy(A,eigvals_only=True)[0]/k(0,M)
 out.append({'M':M,'normalized_min_eigenvalue_65digits':str(e),'feasible_after_rescaling':True,'rigorous_certificate':False});print(out[-1],flush=True)
(L/'gram-refined.json').write_text(json.dumps(out,indent=2))
