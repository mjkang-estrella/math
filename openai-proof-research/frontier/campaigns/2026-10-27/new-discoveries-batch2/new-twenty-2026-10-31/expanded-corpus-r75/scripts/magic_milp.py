import numpy as np,scipy.optimize as so,scipy.sparse as sp,json,pathlib
D=pathlib.Path(__file__).resolve().parents[1];n=7;ks=[1]*6+[8];p=n+sum(ks);s=4
edges=[(i,(i+1)%n) for i in range(n)];j=n
for i,k in enumerate(ks):
 for _ in range(k):edges.append((i,j));j+=1
rows=[];cols=[];data=[];lo=[];hi=[]
def row(terms,l,h):
 k=len(lo)
 for j,v in terms:rows.append(k);cols.append(j);data.append(v)
 lo.append(l);hi.append(h)
# vertex label assignment x, edge sum assignment y
for v in range(p):row([(v*p+l,1) for l in range(p)],1,1)
for l in range(p):row([(v*p+l,1) for v in range(p)],1,1)
for e in range(p):row([(p*p+e*p+l,1) for l in range(p)],1,1)
for l in range(p):row([(p*p+e*p+l,1) for e in range(p)],1,1)
for e,(u,v) in enumerate(edges):row([(u*p+l,l+1) for l in range(p)]+[(v*p+l,l+1) for l in range(p)]+[(p*p+e*p+l,-s-l) for l in range(p)],0,0)
A=sp.csc_matrix((data,(rows,cols)),shape=(len(lo),2*p*p));r=so.milp(np.zeros(2*p*p),integrality=np.ones(2*p*p),bounds=so.Bounds(0,1),constraints=so.LinearConstraint(A,lo,hi),options={'time_limit':105,'threads':2})
o={'n':n,'ks':ks,'s':s,'message':r.message,'success':r.success}
if r.x is not None:
 lab=[int(np.argmax(r.x[v*p:(v+1)*p]))+1 for v in range(p)];o['labels']=lab;o['sums']=sorted(lab[u]+lab[v] for u,v in edges);o['exact_verified']=sorted(lab)==list(range(1,p+1)) and o['sums']==list(range(s,s+p))
(D/'outputs/magic-positive.json').write_text(json.dumps(o,indent=2));print(o)
