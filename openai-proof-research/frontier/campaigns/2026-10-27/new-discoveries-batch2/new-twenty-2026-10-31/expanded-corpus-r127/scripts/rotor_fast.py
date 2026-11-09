# Vectorised exact DP (python ints via numpy object arrays) for r(C_{n,m,i}); see rotor.py for model.
import sys, json, math, pathlib, time
import numpy as np
D=pathlib.Path(__file__).resolve().parents[1]
def counts(n,M):
    """return array R[m][i] for m=0..M"""
    tot=np.zeros((M+1,n),dtype=object)
    for q0 in (1,-1):
        for z0 in (True,False):
            A=np.zeros((M+1,n),dtype=object)
            rw0=1 if q0==-1 else 0
            if z0: A[0,rw0]=1
            else: A[1:,rw0]=1
            states={(q0,z0):A}
            for k in range(1,n):
                new={}
                for (qp,zp),A in states.items():
                    for q in (1,-1):
                        rw=1 if q==-1 else 0
                        for z in (True,False):
                            if qp==1 and q==-1 and zp and z: continue
                            if z: C=np.roll(A,rw,axis=1)
                            else:
                                C=np.zeros_like(A)
                                for a in range(1,M+1):
                                    C[a:]+=np.roll(A[:M+1-a],(k*a+rw)%n,axis=1)
                            key=(q,z)
                            if key in new: new[key]=new[key]+C
                            else: new[key]=C
                states=new
            for (ql,zl),A in states.items():
                if ql==1 and q0==-1 and zl and z0: continue
                tot=tot+A
    return tot
if __name__=='__main__':
    n0,n1,mmaxf=int(sys.argv[1]),int(sys.argv[2]),sys.argv[3]
    out=D/'outputs/rotor-counts.jsonl'
    for n in range(n0,n1+1):
        t=time.time(); M=eval(mmaxf,{'n':n})
        R=counts(n,M)
        viol=[]
        for m in range(1,M+1):
            row=[int(v) for v in R[m]]
            g={}
            for i in range(n): g.setdefault(math.gcd(math.gcd(n,m),i),set()).add(row[i])
            bad={d:sorted(s) for d,s in g.items() if len(s)>1}
            if bad: viol.append((m,bad))
            with out.open('a') as f: f.write(json.dumps({'n':n,'m':m,'r':[str(v) for v in row]})+'\n')
        print(json.dumps({'n':n,'M':M,'violations':[(m,{str(d):[str(v) for v in s] for d,s in b.items()}) for m,b in viol],'sec':round(time.time()-t,2)}),flush=True)
