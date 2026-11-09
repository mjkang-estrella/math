from pathlib import Path
import mpmath as mp,json
mp.mp.dps=70
p=Path(__file__).resolve().parent
rows=[]
for bb in ['.05','.2','.5','.8','1']:
    beta=mp.mpf(bb)
    for qq in ['0','.5','1','3.5','10','35']:
        q=mp.mpf(qq);d=(1-beta)*q;limit=mp.gamma(1+q)/mp.gamma(1+beta*q)
        prev=mp.mpf(0)
        for N in [1,2,3,5,10,100,1000,10000]:
            # Closed finite gamma product, independently checked against literal product at N<=10.
            rn=mp.mpf(N)**d*mp.gamma(N+1+beta*q)/mp.gamma(1+beta*q)*mp.gamma(1+q)/mp.gamma(N+1+q)
            if N<=10:
                direct=mp.mpf(N)**d*mp.fprod((k+beta*q)/(k+q) for k in range(1,N+1));assert abs(rn/direct-1)<mp.mpf('1e-60')
            assert prev<=rn*(1+mp.mpf('1e-60')) and rn<=limit*(1+mp.mpf('1e-60'))
            ratio=(1+mp.mpf(1)/N)**d*(N+1+beta*q)/(N+1+q)
            lower=(1+d/(N+1))*(N+1+beta*q)/(N+1+q)
            assert ratio>=lower-mp.mpf('1e-60') and lower>=1-mp.mpf('1e-60')
            rows.append({'beta':bb,'q':qq,'N':N,'ratio_to_limit':mp.nstr(rn/limit,25),'successive_ratio':mp.nstr(ratio,25)})
            prev=rn
(p/'finite-product-checks.json').write_text(json.dumps({'status':'PASS numerical diagnostics only','cases':len(rows),'rows':rows},indent=2)+'\n')
print('PASS240finite-product moment, monotonicity and upper-bound diagnostics; finite checks not proofs')
