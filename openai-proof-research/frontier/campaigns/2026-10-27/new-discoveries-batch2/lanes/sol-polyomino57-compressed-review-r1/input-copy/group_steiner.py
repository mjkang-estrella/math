import os,resource,signal,json,gzip,pathlib,time
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(160,165));signal.alarm(175)
import numpy as np
L=pathlib.Path(__file__).parent;rows=json.loads((L/'group-domains.json').read_text());receipt=[];start=time.monotonic()
for r in rows:
 a,b,e=[r[x] for x in ['a','b','e']];V,G=r['V'],r['G'];n=len(V);k=len(G)
 if not G[0]:receipt.append(dict(a=a,b=b,e=e,status='empty-constraint',lower=12));continue
 if len({g[0] for g in G if len(g)==1})>=8:
  receipt.append(dict(a=a,b=b,e=e,status='forced-cell-small-check'));continue
 N=1<<k;D=np.full((N,n),12,dtype=np.uint8);cover=[sum(1<<g for g in range(k) if v in G[g]) for v in range(n)]
 for v,c in enumerate(cover):
  m=c
  while m:D[m,v]=1;m=(m-1)&c
 # exact graph distances; entries <=20 (or 99 if disconnected)
 dist=np.full((n,n),99,dtype=np.uint8)
 for v in range(n):
  dist[v,v]=0
  for w in r['adj'][v]:dist[v,w]=1
 for v in range(n):dist=np.minimum(dist,dist[:,v,None]+dist[None,v,:])
 for m in range(1,N):
  s=(m-1)&m;ss=[]
  while s:
   if s<(m^s):ss.append(s)
   s=(s-1)&m
  if ss:
   ix=np.array(ss,dtype=np.int32);D[m]=np.minimum(D[m],np.min(D[ix]+D[ix^m]-1,axis=0))
  D[m]=np.minimum(D[m],np.min(D[m,:,None]+dist,axis=0))
 lower=int(D[-1].min());file=f'steiner-{a}-{b}-{e}.bin.gz';data=gzip.compress(D.tobytes(),compresslevel=9,mtime=0);(L/file).write_bytes(data)
 receipt.append(dict(a=a,b=b,e=e,status='dp',n=n,k=k,entries=int(D.size),compressed_bytes=len(data),lower=lower,file=file))
 print(a,b,e,n,k,D.size,len(data),lower,round(time.monotonic()-start,2),flush=True)
 assert lower==12
(L/'steiner-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
