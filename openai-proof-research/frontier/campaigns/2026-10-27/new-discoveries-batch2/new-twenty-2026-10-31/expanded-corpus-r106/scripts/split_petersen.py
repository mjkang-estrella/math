import json,itertools
x=json.load(open('outputs/split-validated.json'));H=[tuple(e) for e in x['split']];F=[e for e in H if set(e)!={2,5}];deg=[sum(v in e for e in F) for v in range(9)];F+=[(9,v) for v in range(9) if deg[v]==2];V=list(itertools.combinations(range(5),2));A=[[int((i,j) in F or (j,i) in F) for j in range(10)] for i in range(10)];B=[[int(i!=j and not set(V[i])&set(V[j])) for j in range(10)] for i in range(10)];f={};used=set()
def rec(k):
 if k==10:return dict(f)
 for j in range(10):
  if j not in used and all(A[k][u]==B[j][v] for u,v in f.items()):
   f[k]=j;used.add(j);r=rec(k+1)
   if r is not None:return r
   used.remove(j);del f[k]
 return None
out={'completed_edges':F,'isomorphism_to_Kneser_5_2':rec(0),'kneser_labels':V};open('outputs/split-petersen.json','w').write(json.dumps(out,indent=2));print(out)
