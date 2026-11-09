"""Exact finite diagnostic; not a Lean proof. No unsigned spectral pretest."""
from pathlib import Path
import re,json,itertools
r=Path(__file__).resolve().parents[1]
s=(r/'formal/GraphClosure7_000.lean').read_text()
codes=json.loads(re.search(r'def targets : List Nat := (\[.*?\])',s).group(1))
cs=json.loads((r/'inputs/nut-formal-r2/all-normalized-certificates.json').read_text())
flat=lambda a:tuple(x for row in a for x in row)
actual={flat(c['matrix']) for c in cs}
allm=set(); rows=[]; abssets=set()
for code in codes:
 bit=lambda i,j:bool((code>>(8*i+j))&1)
 edges=[(i,j) for i in range(8) for j in range(i+1,8) if bit(i,j)]
 seen={0};order=[0];parents=[0]
 for i in order:
  for j in range(8):
   if bit(i,j) and j not in seen:seen.add(j);order.append(j);parents.append(order.index(i))
 assert len(order)==8
 tree={tuple(sorted((order[k],order[parents[k]]))) for k in range(1,8)}
 # r2 uses a tree rooted at 0 and visits sorted neighbours, identical BFS.
 count=0; normalized=set()
 for doubles in itertools.product([0,1],repeat=len(edges)):
  a=[[0]*8 for _ in range(8)]
  for (i,j),d in zip(edges,doubles):a[i][j]=a[j][i]=1+d
  diag=[3-sum(row) for row in a]
  if not all(0<=d<=2 for d in diag):continue
  for i in range(8):a[i][i]=diag[i]
  abssets.add(flat(a));count+=1
  free=[(i,j) for i,j in edges if (i,j) not in tree]+[(i,i) for i in range(8) if diag[i]==2]
  for signs in itertools.product([1,-1],repeat=len(free)):
   for semi in [1,-1]:
    b=[row[:] for row in a]
    for i in range(8):
     if diag[i]==1:b[i][i]=semi
    for (i,j),v in zip(free,signs):b[i][j]=b[j][i]=v*a[i][j]
    normalized.add(flat(b))
 allm.update(normalized)
 rows.append(dict(code=code,unsigned_patterns=count,normalized=len(normalized),bfs_order=order,parents=parents))
# Relabel each r2 support into the root catalogue, then switch the BFS tree positive.
r2codes={sum((1<<(8*i+j)) for i in range(8) for j in range(8) if i!=j and c['matrix'][i][j]) for c in cs}
def iso(a,b):
 bit=lambda c,i,j:(c>>(8*i+j))&1
 da=[sum(bit(a,i,j) for j in range(8)) for i in range(8)]
 db=[sum(bit(b,i,j) for j in range(8)) for i in range(8)]
 if sorted(da)!=sorted(db):return None
 p=[]
 def go():
  i=len(p)
  if i==8:return p[:]
  for j in range(8):
   if j in p or da[i]!=db[j]:continue
   if any(bit(a,i,k)!=bit(b,j,p[k]) for k in range(i)):continue
   p.append(j);v=go()
   if v is not None:return v
   p.pop()
  return None
 return go()
mapping={}
for a in sorted(r2codes):
 for row in rows:
  p=iso(row['code'],a)
  if p is not None:
   mapping[a]=(row,p);break
 assert a in mapping
transported=set()
for c in cs:
 a=c['matrix']; ac=sum((1<<(8*i+j)) for i in range(8) for j in range(8) if i!=j and a[i][j])
 row,p=mapping[ac];b=[[a[p[i]][p[j]] for j in range(8)] for i in range(8)]
 order=row['bfs_order'];parents=row['parents'];d=[1]*8
 for k in range(1,8):
  i=order[k];j=order[parents[k]];d[i]=d[j]*(1 if b[j][i]>0 else -1)
 transported.add(flat([[d[i]*b[i][j]*d[j] for j in range(8)] for i in range(8)]))
(r/'support-transport.json').write_text(json.dumps([dict(r2_code=a,catalogue_code=row['code'],permutation=p) for a,(row,p) in mapping.items()],indent=2)+'\n')
report=dict(transported_matrix_sets_identical=transported==allm,transported_unique=len(transported),r2_supports=len(r2codes),kind='untrusted Python exact diagnostic, not formal coverage',supports=len(codes),unsigned_patterns=sum(x['unsigned_patterns'] for x in rows),normalized=len(allm),r2_records=len(cs),r2_unique=len(actual),identical_matrix_sets=allm==actual,only_generated=len(allm-actual),only_r2=len(actual-allm),nonsingular=sum('det' in c for c in cs),singular=sum('zero_principal_minor' in c for c in cs),per_support=rows)
(r/'reconciliation.json').write_text(json.dumps(report,indent=2)+'\n')
print({k:v for k,v in report.items() if k!='per_support'})
