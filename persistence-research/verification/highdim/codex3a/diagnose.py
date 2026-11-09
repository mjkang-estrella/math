import sys
sys.dont_write_bytecode=True
import os,json,math,itertools,importlib.util
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
C=__import__('continue');HERE=C.HERE
from hnt import vp
G=C.FastGen([9,9,9],98,3,C.run_target.SUP,False,maxp=10**12)
G.account={'lifts':0,'max_lifts':100000000}
r=(102968334004,650862747363,650862747363,650862747364);M=650866421520
a,w=G.sig(r,M)
out={'input':{'r':r,'M':M,'a':a,'w':w},'factors':[]}
for f in (2,3,5,7,11,13,17,19):
    alive,used=G.expand(r,M,f)
    out['factors'].append({'f':f,'alive':len(alive),'used_primes':[e[0] for e in used],
        'both_unbounded':sum(a[1] is None and w[1] is None for _,a,w in alive),
        'signatures':sorted(set(str((a,w)) for _,a,w in alive))})
json.dump(out,open(os.path.join(HERE,'depth_diagnosis.json'),'w'),indent=2)
print(json.dumps(out,indent=2),flush=True)
# Equivalence checks on explicit lifts for repeated and mixed coefficients.
sup=C.run_target.SUP
cases=0
for coefs,K in [([9,9,9],98),([9,18,54],908),([9,9,9,9],89)]:
    A=C.FastGen(coefs,K,max(3,vp(K,2)+1),sup,False,maxp=10**12)
    B=C.gen_hd.Gen(coefs,K,max(3,vp(K,2)+1),sup,False,maxp=10**12)
    A.account={'lifts':0,'max_lifts':100000000}
    for M,f in [(1,3),(6,2),(24,3),(72,2)]:
        for r in [(0,)*(len(coefs)+1),tuple(range(len(coefs)+1))]:
            aa,uu=A.expand(r,M,f);bb,_=B.expand(r,M,f)
            assert set(aa)==set(bb),(coefs,K,M,f)
            assert len(aa)==len(set(rr for rr,_,_ in aa))
            cases+=1
print('FastGen/original explicit alive sets agree:',cases,flush=True)
