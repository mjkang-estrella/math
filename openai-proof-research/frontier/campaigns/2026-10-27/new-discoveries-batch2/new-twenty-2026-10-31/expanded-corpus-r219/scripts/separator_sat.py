import itertools,sys,pathlib,json
D=pathlib.Path(__file__).resolve().parents[1];n=int(sys.argv[1]);arcs=list(itertools.permutations(range(n),2));v={e:i+1 for i,e in enumerate(arcs)};cs=[];N=len(arcs);k=3*n-4
for s in range(n-1):
 for S in itertools.combinations(range(n),s):
  rem=sorted(set(range(n))-set(S))
  for mask in range(1,(1<<len(rem))-1):
   U=[x for i,x in enumerate(rem) if mask>>i&1];W=[x for i,x in enumerate(rem) if not mask>>i&1];cross=[v[x,y] for x in U for y in W]
   for order in itertools.permutations(S):cs.append(cross+[v[order[j],order[i]] for j in range(s) for i in range(j)])
# Sequential at-most k: q(i,j) means at least j of first i are true, only forward implications needed.
nextvar=N;Q={}
for i in range(1,N+1):
 for j in range(1,min(i,k)+1):nextvar+=1;Q[i,j]=nextvar
for i in range(1,N+1):
 cs.append([-i,Q[i,1]])
 for j in range(1,min(i-1,k)+1):cs.append([-Q[i-1,j],Q[i,j]])
 for j in range(2,min(i,k)+1):cs.append([-i,-Q[i-1,j-1],Q[i,j]])
 if i>k:cs.append([-i,-Q[i-1,k]])
p=D/f'outputs/separator-{n}.cnf'
with p.open('x') as f:
 f.write(f'p cnf {nextvar} {len(cs)}\n')
 for c in cs:f.write(' '.join(map(str,c))+' 0\n')
print(json.dumps(dict(n=n,arc_bound=k,variables=nextvar,clauses=len(cs),path=str(p))))
