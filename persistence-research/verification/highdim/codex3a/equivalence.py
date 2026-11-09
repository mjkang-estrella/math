import sys
sys.dont_write_bytecode=True
import os,itertools
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
C=__import__('continue')
cases=0
for coefs,K in [([9,9,9],98),([9,18,54],908),([9,9,9,9],89)]:
    qmin=max(3,C.breadth.vp(K,2)+1)
    A=C.FastGen(coefs,K,qmin,C.run_target.SUP,False,maxp=10**12)
    B=C.gen_hd.Gen(coefs,K,qmin,C.run_target.SUP,False,maxp=10**12)
    A.account={'lifts':0,'max_lifts':100000000}
    dim=len(coefs)+1
    for M,f in [(1,3),(6,2),(24,3),(72,2)]:
        for r in [(0,)*dim,tuple(range(dim)),(0,)+tuple(range(dim-1,0,-1))]:
            aa,_=A.expand(r,M,f);bb,_=B.expand(r,M,f)
            assert set(aa)==set(bb),(coefs,K,M,f,r)
            assert len(aa)==len(set(rr for rr,_,_ in aa))
            cases+=1
print('PASS',cases,'explicit survivor-set comparisons including reversed equal-coefficient coordinates and cache hits')
