import itertools,json,sys,math
from pathlib import Path
O=Path('outputs')
def stats(p):
 n=len(p); seen=set(); lens=[]
 for a in range(1,n+1):
  if a not in seen:
   x=a;l=0
   while x not in seen: seen.add(x);l+=1;x=p[x-1]
   lens.append(l)
 R=E=0;m=n+1
 for i in range(n-1,-1,-1):
  v=p[i]
  if v<m: R|=1<<(v-1);m=v
  if v>i+1:E|=1<<(v-1)
 return R,E,sorted(lens,reverse=True)
def enumerate_n(n,first=None):
 D=[{} for _ in range(n+1)];signs=[0,0];total=0;hits=[]
 targetR=sum(1<<(v-1) for v in {1,n-4,n-2,n-1}) if n>=7 else 0
 targetE=((1<<n)-1)^targetR
 seq=itertools.permutations(range(1,n+1)) if first is None else ((first,)+q for q in itertools.permutations([v for v in range(1,n+1) if v!=first]))
 for p in seq:
  R,E,L=stats(p);s=(-1)**(n-len(L));signs[s<0]+=1;total+=1
  key=(R<<n)|E
  for k in range(2,min(L)+1):D[k][key]=D[k].get(key,0)+s*(-1)**(n-1)
  if (R,E)==(targetR,targetE):hits.append(list(p))
 out={'n':n,'first':first,'permutations':total,'even':signs[0],'odd':signs[1],'counts':{str(k):{'positive':sum(v>0 for v in D[k].values()),'negative':sum(v<0 for v in D[k].values())} for k in range(2,n+1)},'target_hits':hits}
 if first is not None:out['coefficients']=[{str(k):v for k,v in d.items() if v} for d in D]
 (O/('full-n%d%s.json'%(n,'' if first is None else '-first%d'%first))).write_text(json.dumps(out,indent=1)+'\n')
 print(n,first,total,out['counts'])
def family():
 out=[]
 for n in range(7,17):
  c=n-5;a,b,d,e= n-4,n-3,n-2,n
  tails=[(b,1,a,e,d),(b,1,e,a,d),(b,e,1,a,d),(1,b,a,e,d),(1,b,e,a,d),(e,b,1,a,d),(1,b,a,d,e),(b,1,a,d,e)]
  rows=[]
  for name,t in zip(['A1','A2','A3','A4','A5','A6','B1','B2'],tails):
   p=tuple(range(2,n-4))+t+(n-1,);R,E,L=stats(p)
   inv=sum(p[i]>p[j] for i in range(n) for j in range(i+1,n));assert (-1)**inv==(-1)**(n-len(L))
   assert R==sum(1<<(v-1) for v in {1,n-4,n-2,n-1});assert E==((1<<n)-1)^R
   rows.append({'name':name,'word':p,'inv':inv,'cycles':L,'raw_sign':(-1)**inv,'admissible':min(L)>=3})
  raw=sum(r['raw_sign'] for r in rows if r['admissible']);assert raw== (0 if n==7 else (-1)**n)
  # Independent tail search verifies completeness, without importing candidate code.
  hits=[]
  for t in itertools.permutations([1,a,b,d,e]):
   p=tuple(range(2,n-4))+t+(n-1,);R,E,L=stats(p)
   if R==sum(1<<(v-1) for v in {1,a,d,n-1}) and E==((1<<n)-1)^R:hits.append(p)
  assert set(hits)=={tuple(r['word']) for r in rows}
  out.append({'n':n,'rows':rows,'tail_search_size':math.factorial(5),'hits':len(hits),'raw':raw,'normalized':(-1)**(n-1)*raw})
 (O/'family.json').write_text(json.dumps(out,indent=1)+'\n')
 print('family verified n=7..16')
if sys.argv[1]=='family':family()
elif sys.argv[1]=='small':
 for n in range(2,10):enumerate_n(n)
elif sys.argv[1]=='chunk':enumerate_n(10,int(sys.argv[2]))
elif sys.argv[1]=='aggregate':
 ds=[{} for _ in range(11)]; tot=ev=od=0
 for j in range(1,11):
  a=json.loads((O/('full-n10-first%d.json'%j)).read_text());tot+=a['permutations'];ev+=a['even'];od+=a['odd']
  for k,d in enumerate(a['coefficients']):
   for key,v in d.items():ds[k][key]=ds[k].get(key,0)+v
 counts={str(k):{'positive':sum(v>0 for v in ds[k].values()),'negative':sum(v<0 for v in ds[k].values())} for k in range(2,11)}
 out={'n':10,'permutations':tot,'even':ev,'odd':od,'counts':counts};assert counts['3']['negative']==89 and counts['4']['negative']==3
 (O/'full-n10.json').write_text(json.dumps(out,indent=1)+'\n');print(out)
