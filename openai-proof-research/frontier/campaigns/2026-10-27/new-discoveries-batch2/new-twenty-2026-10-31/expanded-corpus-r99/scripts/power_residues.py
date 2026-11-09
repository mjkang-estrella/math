import os,resource,time,json,math,collections
resource.setrlimit(resource.RLIMIT_CPU,(110,110));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);start=time.time();N=200000;M=math.lcm(*range(2,13));out={'N':N,'modulus_lcm':M,'coverage':[],'limitation':'finite residue counts cannot refute or prove infinite occurrence'}
for d in range(2,7):
 a=[0]*(N+1);a[0]=1;k=1
 while k**d<=N:
  part=k**d
  for i in range(part,N+1):a[i]=(a[i]+a[i-part])%M
  k+=1
 for m in range(2,13):
  counts=collections.Counter(x%m for x in a[100001:]);out['coverage'].append({'d':d,'m':m,'interval':[100001,N],'counts':[counts[r]for r in range(m)]})
 out['seconds']=time.time()-start;json.dump(out,open('outputs/power-residues.json','w'),indent=2)
print('completed',len(out['coverage']),'seconds',out['seconds'])
