"""Bounded LP discovery; every reported positive witness is checked over Q.

No floating-point feasibility or failure is itself a mathematical certificate.
"""
import os
for name in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:
    os.environ[name] = '1'
import resource
resource.setrlimit(resource.RLIMIT_AS, (512*1024**2, 512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU, (180, 180))
import argparse, json, time, warnings
from array import array
warnings.filterwarnings('ignore', message='Unrecognized options detected.*')
from fractions import Fraction
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

def product(exponents):
    a=[1]
    for d in exponents:
        b=a+[0]*d
        for i,x in enumerate(a): b[i+d]-=x
        a=b
    return a

def problem(k,n,series=False):
    ds=list(range(1,2*n+2,2))
    numerator=product(range(2*k-1,2*k+2*n-1,2))
    degree=len(numerator)-1
    D=2*n*(k-2)-1
    columns=[]; labels=[]
    rr=array('i');cc=array('i');vv=array('d')
    for j,d in enumerate(ds):
        p=product(ds[:j]+ds[j+1:])
        for a in range(max(0,D+d+1)):
            if series:
                c=len(labels);labels.append((j,a))
                for r in range(a,degree+1,d):rr.append(r);cc.append(c);vv.append(1)
                continue
            col=[(a+i,x) for i,x in enumerate(p) if x]
            assert max(i for i,x in col)<=degree
            c=len(columns); columns.append(col);labels.append((j,a))
            for r,v in col: rr.append(r);cc.append(c);vv.append(v)
    A=coo_matrix((vv,(rr,cc)),shape=(degree+1,len(labels))).tocsc()
    return A,numerator,columns,labels

def exact_primal(x,cols,b,labels,n):
    for den in (1,1000,1000000):
        rat=[Fraction(float(t)).limit_denominator(den) for t in x]
        if any(t<0 for t in rat):continue
        out=[Fraction(0) for _ in b]
        if cols:
            for t,col in zip(rat,cols):
                if t:
                    for i,v in col:out[i]+=v*t
        else:
            ds=list(range(1,2*n+2,2))
            for j in range(n+1):
                p=product(ds[:j]+ds[j+1:])
                for (jj,a),t in zip(labels,rat):
                    if jj==j and t:
                        for i,v in enumerate(p):
                            if v:out[a+i]+=v*t
        if out==b:return rat
    return None

def run(k,n,series=False):
    A,b,cols,labels=problem(k,n,series)
    exact_b=b
    if series:
        b=b.copy()
        for d in range(1,2*n+2,2):
            for i in range(d,len(b)):b[i]+=b[i-d]
    t=time.monotonic()
    res=linprog(np.ones(A.shape[1]),A_eq=A,b_eq=b,bounds=(0,None),method='highs',options={'time_limit':12,'threads':1})
    rec={'k':k,'n':n,'basis':'series' if series else 'polynomial','shape':A.shape,'lp_status':res.status,'message':res.message,'seconds':time.monotonic()-t}
    if res.success:
        x=exact_primal(res.x,cols,exact_b,labels,n)
        rec['exact_certificate']=x is not None
        if x is not None:
            rec['nonzero']=[{'j':j,'a':a,'coefficient':str(v)} for (j,a),v in zip(labels,x) if v]
    elif res.status==2:
        # A^T y >= 0 and b^T y = -1 certify infeasibility.
        dual=linprog(np.zeros(len(b)),A_ub=-A.T,b_ub=np.zeros(A.shape[1]),A_eq=np.array([b]),b_eq=[-1],bounds=(None,None),method='highs',options={'time_limit':12,'threads':1})
        rec['dual_status']=dual.status
        if dual.success:
            for den in (1,1000,1000000):
                y=[Fraction(float(t)).limit_denominator(den) for t in dual.x]
                vals=[sum(y[i] for i in range(a,len(b),2*j+1)) for j,a in labels] if series else [sum(y[i]*v for i,v in col) for col in cols]
                dot=sum(t*v for t,v in zip(y,b))
                if min(vals)>=0 and dot<0:
                    rec['exact_dual']=[str(t) for t in y];rec['dual_dot']=str(dot);break
    return rec

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--max-n',type=int,default=8);ap.add_argument('--max-k',type=int,default=12);ap.add_argument('--output',default='results.json');args=ap.parse_args()
    out=[]
    for n in range(args.max_n+1):
        for k in range(2,args.max_k+1):
            r=run(k,n);out.append(r)
            print(k,n,r['lp_status'],r.get('exact_certificate',False),bool(r.get('exact_dual')),flush=True)
            Path(args.output).write_text(json.dumps(out,indent=2)+'\n')
            if r.get('exact_dual'):raise SystemExit(0)
