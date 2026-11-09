import itertools,collections,numpy as np,time,json,pathlib,sys
D=pathlib.Path(__file__).resolve().parents[1];maxd=int(sys.argv[1]);t=time.time()
def comps(d):return [(a,b,d-a-b) for a in range(1,d-1) for b in range(1,d-a)]
def cont(rows,cols):
 out=[]
 def rec(r,c,flat):
  if len(r)==1:
   if sum(c)==r[0]:out.append(tuple(flat+c))
   return
  for a in range(min(r[0],c[0])+1):
   for b in range(min(r[0]-a,c[1])+1):
    z=r[0]-a-b
    if z<=c[2]:rec(r[1:],[c[0]-a,c[1]-b,c[2]-z],flat+[a,b,z])
 rec(list(rows),list(cols),[]);return out
perms={k:list(itertools.permutations(range(k))) for k in (1,2,3)}
def image(alpha):
 P=[];Q=[]
 for i in range(3):
  for j in range(3):
   for _ in range(alpha[3*i+j]):
    v=j;r=0
    while r<len(P):
     k=next((k for k,x in enumerate(P[r]) if x>v),len(P[r]))
     if k==len(P[r]):P[r].append(v);Q[r].append(i);break
     P[r][k],v=v,P[r][k];r+=1
    else:P.append([v]);Q.append([i])
 poly={(0,)*9:1}
 for col in range(len(P[0])):
  inds=[r for r in range(len(P)) if len(P[r])>col];k=len(inds);terms=[]
  for pm in perms[k]:
   ex=[0]*9
   for a in range(k):ex[3*Q[a][col]+P[pm[a]][col]]+=1
   sign=(-1)**sum(pm[a]>pm[b] for a in range(k) for b in range(a+1,k));terms.append((ex,sign))
  new=collections.defaultdict(int)
  for a,c in poly.items():
   for b,sg in terms:new[tuple(x+y for x,y in zip(a,b))]+=c*sg
  poly={a:c for a,c in new.items() if c}
 return poly
out=[]
for d in range(3,maxd+1):
 tested=0;minimum=1e9;maxsize=0;bad=[]
 for s in comps(d):
  for p in comps(d):
   if p<s or max(s)+max(p)>d:continue
   basis=cont(s,p);idx={a:i for i,a in enumerate(basis)};M=np.zeros((len(basis),len(basis)))
   for j,a in enumerate(basis):
    for b,c in image(a).items():M[idx[b],j]=c
   eig=np.linalg.eigvals(M);im=max(abs(eig.imag));minimum=min(minimum,im);maxsize=max(maxsize,len(basis));tested+=1
   if im<1e-7:bad.append([s,p,len(basis)])
 print(json.dumps({'degree':d,'reduced_unordered_weight_pairs':tested,'largest_matrix':maxsize,'min_max_imaginary':minimum,'all_real_candidates':bad,'cumulative_seconds':time.time()-t}),flush=True)
 out.append([d,tested,maxsize,minimum,bad])
(D/'outputs/rsk.json').write_text(json.dumps(out))
