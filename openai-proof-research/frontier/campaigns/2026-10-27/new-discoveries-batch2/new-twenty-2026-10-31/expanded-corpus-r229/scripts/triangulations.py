import itertools,random,pathlib,json,sys
D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(229);p=1000003
def rank(a):
 basis={}
 for row in a:
  row=[x%p for x in row]
  for j in sorted(basis):
   v=row[j]
   if v:row=[(x-v*y)%p for x,y in zip(row,basis[j])]
  q=next((j for j,x in enumerate(row) if x),None)
  if q is not None:
   u=pow(row[q],-1,p);basis[q]=[x*u%p for x in row]
 return len(basis)
def cross(a,b):
 i,j=a;k,l=b
 return i<k<j<l or k<i<l<j
out=[]
extended='--extended' in sys.argv
for k,n in ([(3,11),(3,12),(4,12)] if extended else [(3,9),(3,10),(3,11),(4,11)]):
 relevant=[(i,j) for i in range(n) for j in range(i+1,n) if min(j-i,n-(j-i))>k]
 fixed=[(i,j) for i in range(n) for j in range(i+1,n) if min(j-i,n-(j-i))<=k]
 target=k*(n-2*k-1);forbidden=[]
 for ids in itertools.combinations(range(len(relevant)),k+1):
  if all(cross(relevant[i],relevant[j]) for i,j in itertools.combinations(ids,2)):forbidden.append(sum(1<<i for i in ids))
 m=n-k-1;t=rng.sample(range(1,10000),2*m);pts=[tuple(pow(x,d,p) for d in range(1,k+1)) for x in t]
 def matrix(es):
  ans=[]
  for i,j in es:
   a=i;b=n-1-j
   if a>=m or b>=m:continue
   b+=m;row=[0]*(2*m*k)
   for d in range(k):row[a*k+d]=(pts[a][d]-pts[b][d])%p;row[b*k+d]=-row[a*k+d]
   ans.append(row)
  return ans
 row={'k':k,'n':n,'relevant_edges':len(relevant),'forbidden_crossings':len(forbidden),'subset_trials':0,'triangulations':0,'full_row_rank':0,'deficient':[],'exhaustive':(n<=11 if extended else n!=11 or k==4)}
 todo=itertools.combinations(range(len(relevant)),target) if row['exhaustive'] else (rng.sample(range(len(relevant)),target) for _ in range(100000 if extended else 20000))
 for ids in todo:
  row['subset_trials']+=1;mask=sum(1<<i for i in ids)
  if any(mask&f==f for f in forbidden):continue
  es=fixed+[relevant[i] for i in ids];mat=matrix(es);r=rank(mat);row['triangulations']+=1
  if r==len(mat):row['full_row_rank']+=1
  else:row['deficient'].append({'relevant':[relevant[i] for i in ids],'rank':r,'rows':len(mat)})
 print(row,flush=True);out.append(row)
(D/('evidence/triangulations-extended.json' if extended else 'evidence/triangulations-search.json')).write_text(json.dumps(out,indent=2))
