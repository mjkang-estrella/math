# Copyright (c) 2026 Myeongjin Kang. MIT License.
"""Exact finite diagnostics. Reads only; no filesystem write on any branch."""
from pathlib import Path
import importlib.util,json
from fractions import Fraction as Q
from itertools import product
ROOT=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('local_probe',ROOT/'exchange_probe.py')
p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p)

def dfs_hcs(n,e):
 adj=[[] for _ in range(n)]
 for k,(u,v) in enumerate(e):adj[u].append((v,k));adj[v].append((u,k))
 answer=set()
 def rec(path,seen,bits):
  if len(path)==n:
   if path[1]>path[-1]:return
   for v,k in adj[path[-1]]:
    if v==0:answer.add(bits|(1<<k))
   return
  for v,k in adj[path[-1]]:
   if not (seen>>v&1):rec(path+[v],seen|(1<<v),bits|(1<<k))
 rec([0],1,0);return answer

def cycle_count(n,e,bits):
 adj=[[] for _ in range(n)]
 for k,(u,v) in enumerate(e):
  if bits>>k&1:adj[u].append(v);adj[v].append(u)
 assert all(len(z)==2 for z in adj)
 seen=set();count=0
 for root in range(n):
  if root in seen:continue
  count+=1;seen.add(root);todo=[root]
  while todo:
   for v in adj[todo.pop()]:
    if v not in seen:seen.add(v);todo.append(v)
 return count

def all_cycles(n,e):
 adj=[[] for _ in range(n)]
 for k,(u,v) in enumerate(e):adj[u].append((v,k));adj[v].append((u,k))
 ans={}
 for root in range(n):
  def rec(path,seen,bits):
   for v,k in adj[path[-1]]:
    if v==root and len(path)>=4 and path[1]<path[-1]:ans[bits|(1<<k)]=tuple(path)
    elif v>root and not (seen>>v&1):rec(path+[v],seen|(1<<v),bits|(1<<k))
  rec([root],1<<root,0)
 return ans

def has_matching(n,e,mask):
 if not mask:return True
 u=(mask&-mask).bit_length()-1
 for a,b in e:
  if a==u:v=b
  elif b==u:v=a
  else:continue
  if mask>>v&1 and has_matching(n,e,mask^(1<<u)^(1<<v)):return True
 return False

def pfaffian_signs(n,e):
 rows=[]
 for bits,path in all_cycles(n,e).items():
  mask=((1<<n)-1)^sum(1<<v for v in path)
  if has_matching(n,e,mask):rows.append((bits,(len(path)//2-1)%2))
 piv={}
 for bits,b in rows:
  while bits:
   j=bits.bit_length()-1
   if j in piv:bits^=piv[j][0];b^=piv[j][1]
   else:piv[j]=(bits,b);break
  else:assert b==0
 sol=0
 for j,(bits,b) in sorted(piv.items()):
  if ((bits&sol).bit_count()%2)^b:sol|=1<<j
 assert all((bits&sol).bit_count()%2==b for bits,b in rows)
 return sol,len(rows)

def trace_vectors():
 # Four ring coordinates followed by four spoke coordinates.
 gamma=[]
 for i in range(4):gamma.append([int(j!=i) for j in range(4)]+[int(j in {i,(i+1)%4}) for j in range(4)])
 gamma.extend([[0,1,0,1]+[1]*4,[1,0,1,0]+[1]*4])
 coeff=[1,-1,1,-1,-1,1]
 assert p.rank([[x-y for x,y in zip(z,gamma[0])] for z in gamma[1:]])==4
 assert all(sum(c*z[j] for c,z in zip(coeff,gamma))==0 for j in range(8))
 assert sum(coeff)==0
 # Negative control: a sign error in the P term is detected.
 wrong=coeff[:];wrong[4]=1
 assert any(sum(c*z[j] for c,z in zip(wrong,gamma))!=0 for j in range(8))
 return gamma

def main():
 trace_vectors();print('TRACE: six gadget vectors, affine rank 4, unique relation; wrong-sign control rejected')
 data=json.loads((ROOT/'square-diagnostic.json').read_text());g=data['parent'];h=data['expanded'];meta=data['meta']
 # JSON lists are normalized only where edge-tuple lookup needs them.
 g=(g[0],[tuple(z) for z in g[1]],g[2]);h=(h[0],[tuple(z) for z in h[1]],h[2])
 meta={**meta,'removed':[tuple(z) for z in meta['removed']],'ring':[tuple(z) for z in meta['ring']],'spokes':[tuple(z) for z in meta['spokes']]}
 rec,failed,groups=p.inspect(g,h,meta);n,e=h[:2];m=len(e)
 complete=set(p.hcs(h));assert complete==dfs_hcs(n,e)
 assert rec['groups']==[1,1,1,1,1,3] and rec['within_rank']==2 and rec['with_hexagon_rank']==3 and rec['full_rank']==7
 cs=sum(groups,[]);assert [sorted(k for k in range(m) if c>>k&1) for c in cs]==data['cycle_supports']
 z=sum(1<<k for k in data['factor_support']);assert z==failed[0] and cycle_count(n,e,z)==2 and z not in complete
 coeff=list(map(Q,data['affine_coefficients']));assert sum(coeff)==1
 assert all(sum(q*((c>>k)&1) for q,c in zip(coeff,cs))==((z>>k)&1) for k in range(m))
 assert p.rank([[Q(1)]+p.vector(c,m) for c in cs])==8
 assert [str(q) for q in coeff]==['1/4','3/4','1/4','3/4','-1/4','-1/4','-1/4','-1/4']
 minor=data['independence_minor'];cols=minor['augmented_columns']
 M=[([Q(1)]+list(map(Q,p.vector(c,m)))) for c in cs];M=[[row[j] for j in cols] for row in M];det=Q(1)
 for j in range(8):
  k=next(k for k in range(j,8) if M[k][j])
  if k!=j:M[j],M[k]=M[k],M[j];det=-det
  v=M[j][j];det*=v
  for k in range(j+1,8):
   q=M[k][j]/v;M[k]=[x-q*y for x,y in zip(M[k],M[j])]
 assert det==Q(minor['determinant'])==-4
 iso=data['prism_isomorphism'];ue,ve=iso['u'],iso['v']
 mapped={tuple(sorted(z)) for i in range(6) for z in [(ue[i],ue[(i+1)%6]),(ve[i],ve[(i+1)%6]),(ue[i],ve[i])]}
 assert mapped==set(e)

 bad=coeff[:];bad[0]+=1
 assert any(sum(q*((c>>k)&1) for q,c in zip(bad,cs))!=((z>>k)&1) for k in range(m))
 print('CUBE EXPANSION: independent Hamiltonian DFS = matching complement enumeration; 8 cycles; ranks 2+1+4=7')
 print('CERTIFICATE: disconnected 2-factor has unique affine coefficients (1,3,1,3,-1,-1,-1,-1)/4; wrong coefficient rejected')
 # Explicit six-trace half identity: exhaust its three possible Q choices here.
 goal=tuple(2*x for x in p.vector(z,m));minus={tuple(x+y for x,y in zip(p.vector(c,m),p.vector(d,m))) for c in groups[4] for d in groups[5]}
 assert all(tuple(sum((c>>k)&1 for c in tup)-goal[k] for k in range(m)) not in minus for tup in product(*groups[:4]))
 print('EXCHANGE: all proposed three-cycle and six-trace half-integral resolutions rejected; full REAL rank still holds')
 t,num=pfaffian_signs(n,e);count=0
 for matching in p.matchings(n,e):
  factor=((1<<m)-1)^matching;c=cycle_count(n,e,factor)
  assert (t&factor).bit_count()%2==(n//2-c)%2;count+=1
 assert (t&z).bit_count()%2!=(t&cs[0]).bit_count()%2
 print(f'PFAFFIAN: independently solved {num} conformal-cycle parity equations; all {count} spanning 2-factors satisfy component parity')
 for k in range(4,18,2):
  g=p.prism(k);n,e=g[:2];hc=list(p.hcs(g));m=len(e);idx={edge:i for i,edge in enumerate(e)}
  L=[]
  ring=sum(1<<j for j,(u,v) in enumerate(e) if (u<k)==(v<k))
  for i in range(k):
   x=ring
   for edge in [(i,(i+1)%k),(k+i,k+(i+1)%k)]:x^=1<<idx[tuple(sorted(edge))]
   for tcol in [i,(i+1)%k]:x|=1<<idx[(tcol,k+tcol)]
   L.append(x)
  Z=[c for c in hc if all(c>>idx[(i,k+i)]&1 for i in range(k))]
  assert len(Z)==2 and set(L+Z)==set(hc) and len(hc)==k+2
  assert p.rank([[1]+p.vector(c,m) for c in hc])==k+2
  assert all(sum((c>>j)&1 for c in L)-sum((c>>j)&1 for c in Z)==(k-2)*((ring>>j)&1) for j in range(m))
 print('PRISMS: exact classification/bases and unbounded-denominator ring-factor identity checked for m=4,6,...,16')
 print('PASS_EXACT_FINITE_DIAGNOSTICS_ONLY_H_UNRESOLVED')
if __name__=='__main__':main()
