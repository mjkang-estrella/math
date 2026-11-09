import itertools,json,pathlib,random,time,sys
D=pathlib.Path(__file__).resolve().parents[1]
def crossing(F,V):
 return all(not(a&b and (a|b)!=V) or ((a&b) in F and (a|b) in F) for a in F for b in F)
def solve(arcs,F,tau):
 cuts=[([i for i,(u,v) in enumerate(arcs) if (U>>u&1) and not(U>>v&1)],[i for i,(u,v) in enumerate(arcs) if (U>>v&1) and not(U>>u&1)]) for U in F]
 if any(len(a)*(tau-1)+len(b)<tau for a,b in cuts):return None
 # color symmetry: restricted growth strings
 colors=[0]*len(arcs)
 def rec(i,m):
  if i==len(arcs):return all(all(any(colors[j]!=c for j in a) or any(colors[j]==c for j in b) for c in range(tau)) for a,b in cuts)
  for c in range(min(m+1,tau-1)+1):
   colors[i]=c
   # Reject colors with a completely assigned violated cut.
   if all(any(j>=i+1 or colors[j]!=c for j in a) or any(j>=i+1 or colors[j]==c for j in b) for a,b in cuts):
    if rec(i+1,max(m,c)):return True
  return False
 return rec(0,-1)
n=int(sys.argv[1]);V=(1<<n)-1;possible=list(itertools.permutations(range(n),2));cnt=eligible=0;examples=[];random.seed(196)
if n==3:
 families=[set(s for s in range(1,V) if mask>>(s-1)&1) for mask in range(1<<(V-1))];families=[F for F in families if crossing(F,V)]
 cases=((mask,F,tau) for mask in range(1<<len(possible)) for F in families for tau in (2,3,4))
else:
 def randomcases():
  for k in range(5000):
   mask=random.randrange(1<<len(possible));F=set(random.sample(range(1,V),random.randrange(1,V)))
   while True:
    new=F|{a&b for a in F for b in F if a&b and (a|b)!=V}|{a|b for a in F for b in F if a&b and (a|b)!=V}
    if F==new:break
    F=new
   yield mask,F,random.choice((2,3,4))
 cases=randomcases()
for mask,F,tau in cases:
 arcs=[a for j,a in enumerate(possible) if mask>>j&1]
 # weak connectivity
 seen={0}
 while True:
  new=seen|{v for u,v in arcs if u in seen}|{u for u,v in arcs if v in seen}
  if new==seen:break
  seen=new
 if len(seen)<n:continue
 cnt+=1;ok=solve(arcs,F,tau)
 if ok is None:continue
 eligible+=1
 if not ok:examples.append({'arcs':arcs,'family':sorted(F),'tau':tau});break
r={'n':n,'tested_connected_cases':cnt,'hypothesis_satisfying':eligible,'counterexamples':examples,'mode':'exhaustive digraph/family/tau' if n==3 else 'seed196 random digraph/crossing-closure/tau, 5000 attempts'}
(D/f'outputs/strengthening-{n}.json').write_text(json.dumps(r,indent=2));print(r)
