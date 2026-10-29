import datetime,hashlib,itertools,json
from pathlib import Path
P=Path(__file__).resolve().parent;B=P.parent.parent;S=P.parent/'sol-fresh-source-discovery-r83'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
pr=json.loads((S/'provenance.json').read_text())
for name,h in pr['source_sha256'].items():assert sha(S/name)==h,name
def check(C):
 n=len(C);t=list(map(sum,C));T1=sum(t);T2=sum(x*x for x in t)
 Q=sum(C[i][j]*t[i]*t[j] for i in range(n) for j in range(n))
 rows=[]
 for complement in (False,True):
  es=[(i,j) for i in range(n) for j in range(i) if bool(C[i][j])!=complement]
  d=[0]*n
  for i,j in es:d[i]+=1;d[j]+=1
  m1=sum(x*x for x in d);m2=sum(d[i]*d[j] for i,j in es)
  gap=2*n*m2-2*len(es)*m1
  prediction=((n*n+T1)*T2-n*T1*T1-n*Q if complement else n*Q-(T1+2*n)*T2+2*T1*T1)
  assert gap==prediction
  rows.append({'complement':complement,'n':n,'edges':len(es),'M1':m1,'M2':m2,'twice_gap':gap})
 return rows
pairs=list(itertools.combinations(range(4),2))
for bits in range(64):
 C=[[int(i==j) for j in range(4)] for i in range(4)]
 for k,(i,j) in enumerate(pairs):C[i][j]=C[j][i]=(bits>>k)&1
 check(C)
perms=list(itertools.permutations(range(4)));identity=tuple(range(4))
mul=lambda a,b:tuple(a[b[i]] for i in range(4))
noncentral=[p for p in perms if any(mul(p,q)!=mul(q,p) for q in perms)]
assert len(noncentral)==23
C=[[int(mul(p,q)==mul(q,p)) for q in noncentral] for p in noncentral]
stats=check(C);assert stats[0]['M1']==164 and stats[0]['M2']==280
triple=[(1,0,2,3),(1,0,3,2),(2,3,1,0)]
minor=[[int(mul(p,q)==mul(q,p)) for q in triple] for p in triple]
assert minor==[[1,1,0],[1,1,1],[0,1,1]]
v=[1,-1,1];assert sum(v[i]*minor[i][j]*v[j] for i in range(3) for j in range(3))==-1
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'UNRESOLVED','credit':0,'counts':[8,38],
 'source':'Das–Sarkhel–Nath PJM14(1)(2025) Conjecture4.1; both commuting and noncommuting graphs',
 'root_read':'Full summary/discovery, literal cached publisher Conjecture4.1 and worker check outputs. Prior-resolution bodies reported by worker are retained, not independently re-proved by root.',
 'source_hashes_verified':len(pr['source_sha256']),'all_reflexive_graphs_on_four_vertices_checked':64,'S4':stats,'PSD_obstruction':{'minor':minor,'quadratic_value':-1},
 'ordinary_reduction':'Direct expansion of adjacency quadratic forms gives L=nQ-(T1+2n)T2+2T1² and U=(n²+T1)T2-nT1²-nQ. Nonnegative interval width does not locate Q inside it.',
 'remaining_gap':'Uniform group-specific bounds on Q, or an actual finite-group negative gap. Generic PSD false; arbitrary nongroup graph counterexample irrelevant to full source.',
 'scope_limits':'No root repetition of442class2tests or order64cocycle audit; no full source proof, formal certificate or novelty clearance.',
 'registry':'Worker18:30 dated23a4ae6f head/compare evidence retained; no new root remote observation or semantic all-registry clearance.',
 'summary_sha256':sha(S/'SUMMARY.md'),'discovery_sha256':sha(S/'discovery.md')}
(P/'ADOPTION.json').write_text(json.dumps(out,indent=2)+'\n')
n=(B/'NEXT.md').read_text().replace('and structural/geometric r83.','and algebraic/structural r85.')
marker='r79 lasso separation';assert marker in n
n=n.replace(marker,'r83 universal group-graph Zagreb Conjecture4.1 remains unresolved. Root verified both centralizer identities on all64four-vertex reflexive graphs and the exact S4PSD obstruction. No full Q bounds or group counterexample. See root-fresh-source-r83-handback/ADOPTION.json.\n'+marker,1)
(B/'NEXT.md').write_text(n)
paths=[p for p in S.rglob('*') if p.is_file() and '__pycache__' not in p.parts]
paths.extend([P/'check.py',P/'ADOPTION.json',P/'pathspec.txt',B/'NEXT.md'])
(P/'pathspec.txt').write_text(''.join(str(p.relative_to(B.parents[4]))+'\n' for p in sorted(paths)))
print(json.dumps({'status':'Scoped checks PASS; unresolved','source_hashes':len(pr['source_sha256']),'counts':[8,38]}))
