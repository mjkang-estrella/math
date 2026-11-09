from pathlib import Path
import json,sys,math
from fractions import Fraction as F
L=Path(__file__).resolve().parent
sys.path.insert(0,str(Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/experiments/i25_matching_entropy_improvement/vendor')))
import networkx as nx
import numpy as np
def graph(name):return nx.from_edgelist(json.loads((L/(name+'-edges.json')).read_text()))
gs=[graph(x) for x in ['G','H']];cert={}
for name,g in zip(['G','H'],gs):
 ok,em=nx.check_planarity(g);seen=set();faces=[]
 for a,b in em.edges():
  if (a,b) not in seen:faces.append(em.traverse_face(a,b,seen))
 assert ok and nx.is_connected(g) and all(len(f)==3 for f in faces)
 assert len(g)-g.number_of_edges()+len(faces)==2
 assert sorted(dict(g.degree()).values())==[5]*12+[6]*20
 cert[name]=dict(order=len(g),edges=g.number_of_edges(),faces=faces,rotation={str(v):list(em.neighbors_cw_order(v)) for v in g},degree5=sorted(v for v in g if g.degree(v)==5))
def trace_series(g,a,b,K=90):
 q=math.lcm(a.denominator,b.denominator);A=nx.to_numpy_array(g,nodelist=range(32),dtype=int).astype(object);D=np.diag(A.sum(axis=1));M=int(q*a)*A+int(q*b)*D
 P=np.eye(32,dtype=object);S=F(32);den=1;tr=[]
 for k in range(1,K+1):
  P=P@M;den*=q*k;t=int(np.trace(P));S+=F(t,den);tr.append(t)
 R=max(F(sum(row),q) for row in M.tolist());tail=32*3**math.ceil(R)*R**(K+1)/math.factorial(K+1)
 return S,tail,tr
results=[]
for a,b in [(F(9,10),F(1,50)),(F(9,10),F(9,10))]:
 x,ex,tx=trace_series(gs[0],a,b);y,ey,ty=trace_series(gs[1],a,b)
 # Each positive-entry matrix gives lower S and upper S+tail.
 lo=x-y-ey;hi=x-y+ex
 results.append(dict(alpha=str(a),beta=str(b),K=90,lower=str(lo),upper=str(hi),sign=1 if lo>0 else -1 if hi<0 else 0,approx=[float(lo),float(hi)],tail=[str(ex),str(ey)],first_trace_difference=next((dict(k=k+1,G=str(u),H=str(v)) for k,(u,v) in enumerate(zip(tx,ty)) if u!=v),None)))
assert results[0]['sign']==1 and results[1]['sign']==-1
(L/'graph-certificates.json').write_text(json.dumps(cert,indent=2));(L/'exact-signs.json').write_text(json.dumps(results,indent=2));print([(r['alpha'],r['beta'],r['approx'],r['first_trace_difference']) for r in results])
