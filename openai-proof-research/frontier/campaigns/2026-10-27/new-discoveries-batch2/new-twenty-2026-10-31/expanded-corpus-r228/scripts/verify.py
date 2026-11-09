import pathlib,ctypes,itertools,collections,math,json,re
D=pathlib.Path(__file__).resolve().parents[1];lib=ctypes.CDLL(str(D/'scripts/compact-inversions.so'));libc=ctypes.CDLL(None)
# Independent full permutation histogram; compared to compact recurrence stdout via separate logs later.
ans=[]
for n in range(2,9):
 for k in range(3,n+1):
  h=collections.Counter(sum(p[i]>p[j] for i in range(n) for j in range(i+1,n) if (j-i)%k==1) for p in itertools.permutations(range(n)))
  ans.append(dict(n=n,k=k,coefficients=[h[i] for i in range(max(h)+1)]))
(D/'bruteforce-inversions.json').write_text(json.dumps(ans,indent=2)+'\n')
for name in ['inversion-small','inversion-large','inversion-21']:
 ls=(D/f'logs/{name}.log').read_text().splitlines()
 for a,b in zip(ls[::2],ls[1::2]):
  n=int(re.search(r'N (\d+)',a)[1]);c=list(map(int,b.removeprefix('coefficients ').strip(',').split(',')));assert sum(c)==math.factorial(n);assert c==c[::-1]
  k=int(re.search(r' k (\d+)',a)[1]);z=next((z for z in ans if z['n']==n and z['k']==k),None)
  if z:assert z['coefficients']==c
print('Brute-force through S8 agrees with full DP; all existing full DP sums and reversal symmetry pass.')
# Direct semantic check on SAT-produced coloring, with simple paths, no CNF auxiliaries.
s=(D/'logs/spc-solve-6.log').read_text();truth={int(v) for l in s.splitlines() if l.startswith('v ') for v in l[2:].split() if int(v)>0};b=6;n=9;edges=[(i,j) for i in range(3) for j in range(3,n)];colors=[next(c for c in range(3) if 3*e+c+1 in truth) for e in range(len(edges))];adj=[[] for _ in range(n)]
for e,(i,j) in enumerate(edges):adj[i].append((j,colors[e]));adj[j].append((i,colors[e]))
def connected(s,t):
 def dfs(v,mask,last):
  if v==t:return True
  return any(dfs(w,mask|1<<w,(last+[c])[-2:]) for w,c in adj[v] if not mask>>w&1 and c not in last)
 return dfs(s,1<<s,[])
assert all(connected(s,t) for s in range(n) for t in range(s+1,n));(D/'spc-verified.json').write_text(json.dumps(dict(graph='K3,6',edges=edges,colors=colors,all_pairs_strongly_proper_simple_paths=True),indent=2)+'\n');print('SAT coloring independently verified by direct simple-path search.')
