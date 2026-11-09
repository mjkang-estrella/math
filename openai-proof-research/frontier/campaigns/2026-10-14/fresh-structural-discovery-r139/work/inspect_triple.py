exec(open('frontier/campaigns/2026-10-14/fresh-structural-discovery-r139/work/triple_probe.py').read().split('for n in range(4,7):')[0])
s=open('frontier/campaigns/2026-10-14/fresh-structural-discovery-r139/work/triple-probe-result.jsonl').read();r=json.loads(s[s.index('{\n'):]);states=[frozenset(map(tuple,E)) for E in r['states']];k=len(states);H=[[F(3*(i==j)) for j in range(k)] for i in range(k)];fibers={}
for a in combinations(range(3),2):
 fs=defaultdict(list)
 for i,E in enumerate(states):
  fs[(tuple(sorted(e for e in E if not(set(e)&set(a)))),a in E,tuple(sum(tuple(sorted((v,w))) in E for v in a) for w in range(6) if w not in a))].append(i)
 fibers[str(a)]=list(fs.values())
 for ids in fs.values():
  for i in ids:
   for j in ids:H[i][j]-=F(1,len(ids))
A=[[sum(H[i][z]*H[z][j] for z in range(k))-H[i][j] for j in range(k)] for i in range(k)]
w=neg_witness(A);q=sum(w[i]*A[i][j]*w[j] for i in range(k) for j in range(k));print(json.dumps(dict(fibers=fibers,H=[[str(x) for x in row] for row in H],square_witness=list(map(str,w)),square_quadratic=str(q)),indent=2))
