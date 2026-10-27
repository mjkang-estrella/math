import mpmath as mp,json
from pathlib import Path
mp.mp.dps=140
hits=[];cases=0
for ns in ['0.5001','0.51','0.75','1','1.5','2','5','20']:
 n=mp.mpf(ns)
 for xs in ['-20','-10','-3','-1','0','1','3','10','20']:
  x=mp.mpf(xs);K=40
  u=[mp.pcfd(-n-j+mp.mpf('.5'),x) for j in range(K+3)]
  r=[u[j]/u[j+1] for j in range(K+2)]
  logs=[mp.log(z) for z in r];der=[-r[j]+r[j+1] for j in range(K+1)]
  for k in range(1,K+1):
   cases+=1
   if k>=2 and (logs[0]>mp.mpf('1e-80') or der[0]<-mp.mpf('1e-80')):
    hit={'n':ns,'x':xs,'k':k,'logR':str(logs[0]),'derivLogR':str(der[0])};hits.append(hit);print('HIT',hit,flush=True)
   logs=[logs[j]-logs[j+1] for j in range(len(logs)-1)]
   der=[der[j]-der[j+1] for j in range(len(der)-1)]
  # Both lists now start with log R[1] and its derivative.
 print('done',ns,flush=True)
Path(__file__).with_name('segura-scan.json').write_text(json.dumps({'numerical_only':True,'dps':mp.mp.dps,'cases':cases,'hits':hits},indent=2)+'\n')
print('cases',cases,'hits',len(hits))
