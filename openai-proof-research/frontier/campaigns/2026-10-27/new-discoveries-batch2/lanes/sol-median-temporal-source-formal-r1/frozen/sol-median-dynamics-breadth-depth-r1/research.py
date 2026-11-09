from pathlib import Path
import urllib.request,urllib.error,json,hashlib,datetime,subprocess,sys
L=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
def get(url,name):
 rec=dict(url=url,time=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source check (bounded)'}),timeout=25) as r:
   b=r.read(10000000);rec.update(status=r.status,sha256=sha(b),bytes=len(b),final_url=r.url)
  p=L/'frozen'/name;p.write_bytes(b)
 except Exception as e:rec['error']=str(e)
 with (L/'http.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 print(rec)
if sys.argv[1]=='fetch':
 get('https://export.arxiv.org/api/query?id_list=1911.08613','median-current.xml')
 get('https://export.arxiv.org/api/query?search_query=all:%22median%20dynamics%22&max_results=15','median-companions.xml')
 get('https://export.arxiv.org/api/query?search_query=all:%22majority%20dynamics%22%20AND%20all:convexity&max_results=12','majority-convexity.xml')
elif sys.argv[1]=='orbit':
 import numpy as np
 from scipy.sparse import coo_matrix
 from scipy.sparse.linalg import expm_multiply
 from math import comb
 out=[]
 for a,b in [(a,b) for a in [1,3,5,7] for b in [3,9,21,51,101]]:
  states=[(i,j) for i in range(a+1) for j in range(b+1)];N=len(states)
  rr=[];cc=[];dd=[]
  for s,(i,j) in enumerate(states):
   moves=[]
   if 2*j>b and i<a:moves.append(((i+1)*(b+1)+j,a-i))
   if 2*j<b and i>0:moves.append(((i-1)*(b+1)+j,i))
   if 2*i>a and j<b:moves.append((s+1,b-j))
   if 2*i<a and j>0:moves.append((s-1,j))
   for z,r in moves:rr.append(s);cc.append(z);dd.append(r)
   rr.append(s);cc.append(s);dd.append(-sum(r for z,r in moves))
  Q=coo_matrix((dd,(rr,cc)),shape=(N,N)).tocsr()
  f=np.array([[i/a,j/b] for i,j in states]);qf=Q@f
  vals=expm_multiply(Q,np.column_stack([f,qf]),start=0,stop=10,num=101)
  for p in [.05,.15,.25,.35,.45,.49]:
   prob=np.array([comb(a,i)*comb(b,j)*p**(i+j)*(1-p)**(a+b-i-j) for i,j in states])
   k=np.array([i+j for i,j in states]);n=a+b
   d2=prob*((k/p-(n-k)/(1-p))**2-k/p**2-(n-k)/(1-p)**2)
   der=np.einsum('s,tsv->tv',prob,vals[:,:,2:]);curv=np.einsum('s,tsv->tv',d2,vals[:,:,:2])
   for kind,arr in [('time',der),('curvature',-curv)]:
    ix=np.unravel_index(arr.argmax(),arr.shape);v=float(arr[ix])
    if v>1e-8:out.append(dict(a=a,b=b,p=p,kind=kind,t=ix[0]/10,side=int(ix[1]),violation=v))
  print(a,b,'best',sorted(out,key=lambda r:-r['violation'])[:2],flush=True)
 (L/'orbit-results.json').write_text(json.dumps(out,indent=2))
elif sys.argv[1]=='queries':
 from urllib.parse import quote
 queries=['ti:"Majority dynamics and aggregation"','au:Baldasso AND all:majority','cat:math.PR AND all:conjecture','cat:math.CA AND all:conjecture','cat:math.MG AND all:conjecture']
 for i,q in enumerate(queries):get('https://export.arxiv.org/api/query?search_query='+quote(q)+'&max_results=20&sortBy=submittedDate&sortOrder=descending','query-'+str(i)+'.xml')
elif sys.argv[1]=='titles':
 import xml.etree.ElementTree as E
 ns={'a':'http://www.w3.org/2005/Atom'}
 for x in ['query-1.xml','query-2.xml','query-3.xml','query-4.xml']:
  p=L/'frozen'/x
  if not p.exists():continue
  print(x)
  for e in E.fromstring(p.read_bytes()).findall('a:entry',ns):print(e.findtext('a:id',namespaces=ns),e.findtext('a:title',namespaces=ns))
elif sys.argv[1]=='papers':
 for aid in sys.argv[2:]:
  get('https://arxiv.org/pdf/'+aid,aid+'.pdf')
  p=L/'frozen'/(aid+'.pdf')
  if p.exists():subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
elif sys.argv[1]=='bodies':
 import re
 out=[]
 for p in sorted((L/'frozen').glob('2610*.txt')):
  lines=p.read_text().splitlines();out.append('\nSOURCE '+p.name)
  ix=[i for i,x in enumerate(lines) if re.search(r'^(Theorem 1|Theorem 5.8|Proof of Theorem 1|Proof of Theorem 5.8|Proof for Theorem 1|Conjecture|.*[Ww]e conjecture)',x)]
  for i in ix[:5]:out.append('Lines '+str(i+1)+':\n'+'\n'.join(lines[i:i+18]))
 (L/'body-excerpts.txt').write_text('\n'.join(out))
elif sys.argv[1]=='atlas':
 import numpy as np,networkx as nx
 from scipy.sparse import coo_matrix
 from scipy.sparse.linalg import expm_multiply
 results=[];tested=0
 graphs=[g for g in nx.graph_atlas_g() if 2<=len(g)<=7 and nx.is_connected(g)]
 for ix,g in enumerate(graphs):
  n=len(g);N=1<<n;ss=np.arange(N);bits=((ss[:,None]>>np.arange(n))&1).astype(float)
  rows=[];cols=[];data=[]
  for v in range(n):
   nei=list(g[v]);ones=bits[:,nei].sum(axis=1);new=np.where(ones*2>len(nei),1,np.where(ones*2<len(nei),0,bits[:,v]))
   dest=ss^((new!=bits[:,v]).astype(int)<<v)
   rows.extend(ss);cols.extend(dest);data.extend(np.ones(N))
  rows.extend(ss);cols.extend(ss);data.extend(-n*np.ones(N));Q=coo_matrix((data,(rows,cols)),shape=(N,N)).tocsr()
  val=expm_multiply(Q,np.column_stack([bits,Q@bits]),start=0,stop=8,num=17)
  k=bits.sum(axis=1)
  for p in [.1,.25,.4,.49]:
   prob=p**k*(1-p)**(n-k);d2=prob*((k/p-(n-k)/(1-p))**2-k/p**2-(n-k)/(1-p)**2)
   for kind,arr in [('time',np.einsum('s,tsv->tv',prob,val[:,:,n:])),('curvature',-np.einsum('s,tsv->tv',d2,val[:,:,:n]))]:
    j=np.unravel_index(arr.argmax(),arr.shape)
    if arr[j]>1e-8:results.append(dict(graph=nx.to_graph6_bytes(g,header=False).decode().strip(),edges=list(g.edges()),p=p,t=j[0]/2,v=int(j[1]),kind=kind,violation=float(arr[j])))
  tested+=1
  if tested%100==0:print(tested,results[-2:],flush=True)
 (L/'atlas-results.json').write_text(json.dumps(dict(tested=tested,results=results),indent=2))
elif sys.argv[1]=='motifs':
 import numpy as np,random
 from scipy.sparse import coo_matrix
 from scipy.sparse.linalg import expm_multiply
 rng=random.Random(22140);results=[];graphs=[]
 for n in [6,8,10,12]:
  for density in [.2,.4,.6,.8]:
   for rep in range(5):graphs.append((n,[(i,j) for i in range(n) for j in range(i) if rng.random()<density],'random'))
  # Two dense communities and a single bridge: delayed communication.
  for a in range(2,n-1):graphs.append((n,[(i,j) for i in range(n) for j in range(i) if (i<a)==(j<a)]+[(0,a)],'barbell'))
  # A central edge with asymmetric leaf populations: frozen local memory.
  for a in range(1,n-2):graphs.append((n,[(0,1)]+[(0,i) for i in range(2,a+2)]+[(1,i) for i in range(a+2,n)],'double-star'))
 for ix,(n,edges,family) in enumerate(graphs):
  N=1<<n;ss=np.arange(N);bits=((ss[:,None]>>np.arange(n))&1).astype(float)
  rows=[];cols=[];data=[]
  for v in range(n):
   nei=[j if i==v else i for i,j in edges if v in (i,j)];ones=bits[:,nei].sum(axis=1);new=np.where(ones*2>len(nei),1,np.where(ones*2<len(nei),0,bits[:,v]))
   dest=ss^((new!=bits[:,v]).astype(int)<<v)
   rows.extend(ss);cols.extend(dest);data.extend(np.ones(N))
  rows.extend(ss);cols.extend(ss);data.extend(-n*np.ones(N));Q=coo_matrix((data,(rows,cols)),shape=(N,N)).tocsr()
  val=expm_multiply(Q,np.column_stack([bits,Q@bits]),start=0,stop=8,num=17);k=bits.sum(axis=1)
  for p in [.1,.25,.4,.49]:
   prob=p**k*(1-p)**(n-k);d2=prob*((k/p-(n-k)/(1-p))**2-k/p**2-(n-k)/(1-p)**2)
   for kind,arr in [('time',np.einsum('s,tsv->tv',prob,val[:,:,n:])),('curvature',-np.einsum('s,tsv->tv',d2,val[:,:,:n]))]:
    j=np.unravel_index(arr.argmax(),arr.shape)
    if arr[j]>1e-8:results.append(dict(n=n,edges=edges,p=p,t=j[0]/2,v=int(j[1]),kind=kind,violation=float(arr[j]),family=family))
  with (L/'motifs-progress.json').open('w') as f:json.dump(dict(tested=ix+1,total=len(graphs),results=results),f,indent=2)
  if results:print(results[-1],flush=True)
 (L/'motifs-results.json').write_text(json.dumps(dict(tested=len(graphs),results=results),indent=2))
