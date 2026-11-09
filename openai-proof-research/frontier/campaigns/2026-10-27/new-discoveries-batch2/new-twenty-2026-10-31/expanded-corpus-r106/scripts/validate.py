import json,itertools,pathlib,re,hashlib,datetime
D=pathlib.Path('.');checks={}
# Independent full-matrix recomputation of both Zagreb gaps for S3,S4 and S3 x S3.
def compose(a,b):return tuple(a[b[i]] for i in range(len(a)))
P3=list(itertools.permutations(range(3)));P4=list(itertools.permutations(range(4)))
def mc(P):
 C=[[compose(a,b)==compose(b,a) for b in P] for a in P];c=list(map(sum,C));g=len(P);z=c.count(g);return C,[g,z,sum(c),sum(v*v for v in c),sum(c[i]*c[j] for i in range(g) for j in range(g) if C[i][j])]
def gapform(v):
 g,z,s1,s2,q=v;n=g-z;t1=s1-2*z*g+z*z;t2=s2-2*z*s1-z*g*g+3*z*z*g-z**3;qx=q-2*z*s2+z*z*s1-2*z*(g-z)*(s1-z*g)+z*z*(g-z)**2
 return (n*qx-(t1+2*n)*t2+2*t1*t1,(n*n+t1)*t2-n*t1*t1-n*qx)
def literal(C):
 g=len(C);X=[i for i in range(g) if sum(C[i])<g];n=len(X);out=[]
 for commute in [True,False]:
  A=[[int(i!=j and bool(C[i][j])==commute) for j in X] for i in X];d=list(map(sum,A));e=sum(d)//2;m1=sum(v*v for v in d);m2=sum(d[i]*d[j] for i in range(n) for j in range(i) if A[i][j]);out.append(2*(n*m2-e*m1))
 return tuple(out)
C3,v3=mc(P3);C4,v4=mc(P4);C33=[[a and b for a in ra for b in rb] for ra in C3 for rb in C3];v33=[v*v for v in v3]
for name,C,v in [('S3',C3,v3),('S4',C4,v4),('S3xS3',C33,v33)]:assert gapform(v)==literal(C);checks[name]={'moment_gaps':gapform(v),'literal_gaps':literal(C)}
# Check all rows of source inequalities independently from retained numeric outputs.
rows=[]
for l in (D/'logs/permutations.log').read_text().splitlines():
 a=list(map(int,l.split()));
 if len(a)==9:rows.append(a)
a=[15]
for p in range(4):
 s=(D/f'logs/permutation15-{p}.log').read_text();m=re.fullmatch(r'n 15 pattern (\d) count13 (\d+) count123 (\d+)\s*',s);assert m and int(m[1])==p
 a.append(int(m[2]))
for p in range(4):
 s=(D/f'logs/permutation15-{p}.log').read_text();a.append(int(re.search(r'count123 (\d+)',s)[1]))
rows.append(a)
assert [r[0] for r in rows]==list(range(1,16))
assert all(r[2]<=r[3] and r[5]<=r[6]<=r[7]<=r[8] for r in rows)
checks['permutation_inequalities']='all pass at 1..15';(D/'outputs/permutation-counts.json').write_text(json.dumps({'pattern_order':['123','132','321','231'],'rows_n_counts13_counts123':rows},indent=2))
# Aggregate disjoint forest masks and compare the graph count with binomial counting.
from math import comb
counts=[]
for shard in range(8):
 p=D/f'logs/forest8-{shard}.receipt.json';rec=json.loads(p.read_text());assert rec['returncode']==0
 s=(D/f'logs/forest8-{shard}.log').read_text();m=re.fullmatch(r'exhaustive n 8 tested (\d+) failures 0\s*',s);assert m;counts.append(int(m[1]))
assert sum(counts)==sum(comb(28,j) for j in range(18))
checks['forest8']={'shard_counts':counts,'total':sum(counts),'matches_binomial_count':True}
checks['raw']={}
x=json.load(open('extracted.json'));assert len(x)==20
for i,v in x.items():assert hashlib.sha256((D/f'raw/{i}.jsonl').read_bytes()).hexdigest()==v['provenance']['raw_sha256'];checks['raw'][i]=True
(D/'outputs/coverage.json').write_text(json.dumps(checks,indent=2));print(json.dumps({k:v for k,v in checks.items() if k!='raw'},indent=2))
