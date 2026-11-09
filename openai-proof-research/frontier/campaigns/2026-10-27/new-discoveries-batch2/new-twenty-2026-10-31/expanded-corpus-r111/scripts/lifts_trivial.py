import pathlib,json,numpy as np,random,collections
L=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(111);out={'tested':0,'by_m':{},'best_extra_zero':100000,'best':None,'eligible':0,'rejection':collections.Counter()};patterns=json.loads((L/'outputs/nuts.json').read_text())['full_nullity_one']
used=set()
for p in patterns:
 B=np.array(p['quotient']);C=np.array(p['signed'])
 if min(abs(np.linalg.eigvalsh(B.astype(float))))>1e-7:continue
 key=json.dumps(p['quotient'])
 if key in used:continue
 used.add(key)
 out['eligible']+=1
 for m in range(3,81):
  for trial in range(20):
   es=[];bad=False
   for j in range(8):
    d=int(B[j,j]);sg=int(np.sign(C[j,j]))
    if d%2:
     if m%2:bad=True;break
     es.append((j,j,m//2))
    if d>=2:
     vals=[t for t in range(1,m) if t!=m//2 ]
     if not vals:bad=True;break
     a=rng.choice(vals);es.extend([(j,j,a),(j,j,-a)])
    for i in range(j):
     k=int(B[i,j]);vals=[t for t in range(m) ]
     if len(vals)<k:bad=True;break
     for a in rng.sample(vals,k):es.extend([(i,j,a),(j,i,-a)])
   if bad:continue
   mats=np.zeros((m,8,8),dtype=complex);z=np.exp(2j*np.pi*np.arange(m)/m)
   for i,j,a in es:mats[:,i,j]+=z**a
   eig=np.linalg.eigvalsh(mats);zeros=int((abs(eig)<1e-7).sum());out['tested']+=1;out['by_m'][m]=out['by_m'].get(m,0)+1
   if zeros-1<out['best_extra_zero']:
    out['best_extra_zero']=zeros-1;out['best']={'m':m,'edges':es,'pattern':p,'zero_counts':[int((abs(x)<1e-7).sum())for x in eig]};print('BEST',out['tested'],m,zeros,flush=True)
   if zeros==1:
    (L/'outputs/lifts.json').write_text(json.dumps(out,indent=2));raise SystemExit('NUMERICAL CANDIDATE')
 (L/'outputs/lifts.json').write_text(json.dumps(out,indent=2))
print('DONE',out['tested'],out['eligible'],out['rejection'])
