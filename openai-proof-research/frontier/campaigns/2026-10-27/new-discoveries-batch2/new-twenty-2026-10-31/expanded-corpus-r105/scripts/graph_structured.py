import pathlib,sys,json,itertools,random,numpy as np
D=pathlib.Path(__file__).resolve().parents[1]
# Import function without executing search driver.
s=(D/'scripts/search_graphs.py').read_text().split('mode=sys.argv[1]')[0];exec(s)
out=[];bad=[];ct=0
for n in [9,10,12,16,20,30,50]:
 lo=[float('inf'),float('inf')];ratio=0;seen=0
 for a in range(2,n-2):
  for b in range(1,n-a):
   # two cliques joined by path; clique with many leaves; join clique and bipartite blocks
   c=n-a-b
   families=[]
   E=list(itertools.combinations(range(a),2))+list(itertools.combinations(range(a,a+b),2))+[(0,a)]
   E+=[(a+i-1,a+i)for i in range(b,n-a)];families.append(E)
   E=list(itertools.combinations(range(a),2))+[(0,i)for i in range(a,a+b)]+[(min(1,a-1),i)for i in range(a+b,n)];families.append(E)
   E=[(u,v)for u in range(a)for v in range(a,n)]+list(itertools.combinations(range(a,a+b),2));families.append(E)
   for E in families:
    z=calc(n,E)
    if z is None:continue
    vals,sz,bound=z;gaps=[vals[0]-vals[1],vals[1]-vals[2]];lo=[min(x,y)for x,y in zip(lo,gaps)];ratio=max(ratio,sz/bound);seen+=1
    if min(gaps)<-1e-6 or sz>bound:bad.append(dict(n=n,edges=E,indices=vals,sz=sz,bound=bound));print('CANDIDATE',bad[-1],flush=True)
 out.append(dict(n=n,graphs=seen,min_float_gaps=lo,max_sz_ratio=ratio));ct+=seen;print(out[-1],flush=True);(D/'outputs/graphs-structured.json').write_text(json.dumps(dict(coverage=out,candidates=bad),indent=2))
