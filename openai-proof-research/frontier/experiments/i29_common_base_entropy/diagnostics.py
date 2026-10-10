"""Exact enumeration, rational-activity Gibbs laws, and rational log certificates.
Standard library only. Float search scores are diagnostics, never certificates.
"""
from pathlib import Path
from fractions import Fraction as Q
from itertools import combinations
from functools import lru_cache
import random, math, json

OUT=Path('frontier/experiments/i29_common_base_entropy')
R=random.Random(290923)
def mask(t): return sum(1<<i for i in t)
def bits(a,n): return [i for i in range(n) if a>>i&1]
def gf_rank(cols,p,r):
    rows=[[c[j] for c in cols] for j in range(r)]; k=0
    for col in range(len(cols)):
        a=next((a for a in range(k,r) if rows[a][col]%p),None)
        if a is None: continue
        rows[k],rows[a]=rows[a],rows[k]
        z=pow(rows[k][col],-1,p);rows[k]=[(v*z)%p for v in rows[k]]
        for j in range(r):
            if j!=k:
                z=rows[j][col];rows[j]=[(v-z*w)%p for v,w in zip(rows[j],rows[k])]
        k+=1
        if k==r: break
    return k
def representable(n,r,p):
    while True:
        cols=[[R.randrange(p) for _ in range(r)] for _ in range(n)]
        if gf_rank(cols,p,r)==r:break
    bases=[mask(t) for t in combinations(range(n),r) if gf_rank([cols[i] for i in t],p,r)==r]
    return {'kind':'representable','p':p,'columns':cols,'bases':bases}
def paving(n,r):
    allb=[mask(t) for t in combinations(range(n),r)];R.shuffle(allb);holes=[]
    for a in allb:
        if R.randrange(2) and all((a&b).bit_count()<=r-2 for b in holes):holes.append(a)
    return {'kind':'sparse-paving','circuit_hyperplanes':sorted(holes),'bases':sorted(set(allb)-set(holes))}
def partition(n,r):
    order=list(range(n));R.shuffle(order);blocks=[[order[i]] for i in range(r)]
    for i in order[r:]:blocks[R.randrange(r)].append(i)
    bm=[mask(t) for t in blocks]
    return {'kind':'partition','blocks':blocks,'bases':[mask(t) for t in combinations(range(n),r) if all((mask(t)&b).bit_count()==1 for b in bm)]}
def check_matroid(B,n,r):
    S=set(B);assert S and all(a.bit_count()==r for a in B)
    for a in B:
        for b in B:
            for i in bits(a&~b,n):
                assert any((a^(1<<i)^(1<<j)) in S for j in bits(b&~a,n))
def matrix_rank(rows):
    if not rows:return 0
    a=[[Q(x) for x in row] for row in rows];i=0
    for j in range(len(a[0])):
        k=next((k for k in range(i,len(a)) if a[k][j]),None)
        if k is None:continue
        a[i],a[k]=a[k],a[i];v=a[i][j];a[i]=[x/v for x in a[i]]
        for k in range(i+1,len(a)):
            v=a[k][j]
            if v:a[k]=[x-v*y for x,y in zip(a[k],a[i])]
        i+=1
        if i==len(a):break
    return i
def geometry(B1,B2,C,n):
    # Reduce coordinates fixed across the chosen exposed face.
    union=0; forced=(1<<n)-1
    for b in C:union|=b;forced&=b
    act=bits(union&~forced,n); r=C[0].bit_count()-forced.bit_count()
    if not act:return {'n_active':0,'r_active':0,'dimension':0,'row_rank':0}
    rows=[];chains=[]
    for B in [B1,B2]:
        minor=[b&~forced for b in B if b&forced==forced and b&~union==0]
        tight=[]
        for sm in range(1<<len(act)):
            a=mask(act[j] for j in bits(sm,len(act)))
            rank=max((b&a).bit_count() for b in minor)
            if all((b&a).bit_count()==rank for b in C):tight.append(sm);rows.append([int(sm>>j&1) for j in range(len(act))])
        # Maximal chain obtained by choosing a minimal proper tight superset.
        chain=[0]
        while chain[-1]!=(1<<len(act))-1:
            chain.append(min((a for a in tight if a!=chain[-1] and a&chain[-1]==chain[-1]),key=lambda a:(a.bit_count(),a)))
        assert len(chain)-1<=r;chains.append(chain)
    rho=matrix_rank(rows)
    a0=C[0];dif=[[int(b>>i&1)-int(a0>>i&1) for i in act] for b in C[1:]];d=matrix_rank(dif)
    assert d+rho==len(act) and rho<=2*r-1
    return {'n_active':len(act),'r_active':r,'dimension':d,'row_rank':rho,'chains':chains}

@lru_cache(maxsize=50000)
def log_iv(q):
    q=Q(q);assert q>0
    if q==1:return Q(0),Q(0)
    k=0;t=q
    while t<1:t*=2;k-=1
    while t>=2:t/=2;k+=1
    def series(t):
        z=(t-1)/(t+1);z2=z*z;v=z;s=Q(0);N=36
        for j in range(N):s+=2*v/(2*j+1);v*=z2
        return s,s+2*v/((2*N+1)*(1-z2))
    a,b=series(t);c,d=series(Q(2))
    if k>=0:a+=k*c;b+=k*d
    else:a+=k*d;b+=k*c
    scale=10**30
    return Q((a*scale).__floor__(),scale),Q((b*scale).__ceil__(),scale)
def ent_iv(vals):
    a=b=Q(0)
    for p in vals:
        if p:
            lo,hi=log_iv(p);a-=p*hi;b-=p*lo
    return a,b
def gibbs(C,n,w):
    weights=[math.prod(w[i] for i in bits(b,n)) for b in C];Z=sum(weights)
    probs=[Q(v,Z) for v in weights]
    x=[sum((p for p,b in zip(probs,C) if b>>i&1),Q(0)) for i in range(n)]
    return probs,x
def float_ent(vals):return -sum(float(q)*math.log(float(q)) for q in vals if q)
def certify(row,inst):
    p,x=gibbs(inst['common'],inst['n'],row['activities']);H=ent_iv(p);F=ent_iv(x);B=ent_iv([1-q for q in x]);c=Q(inst['r']-1,inst['r'])
    gap=(F[0]-H[1]-c*B[1],F[1]-H[0]-c*B[0])
    # Rank-one and two-atom disjoint cycle identities may be exact equality.
    equality=all(v==0 or v==1 for v in x) or (len(p)==2 and not(inst['common'][0]&inst['common'][1]))
    assert gap[1]<=0 or (equality and gap[0]<=0<=gap[1])
    return dict(row,mean=list(map(str,x)),entropy_interval=list(map(str,H)),defect_interval=list(map(str,gap)),equality_by_identity=equality)

def main():
    instances=[];laws=[];geometries=[]
    for kind in ['representable2','representable3','sparse-paving','partition','mixed']:
        for j in range(32):
            n=6+j%4;r=2+j%3
            gen=lambda k:representable(n,r,int(k[-1])) if k.startswith('representable') else paving(n,r) if k=='sparse-paving' else partition(n,r)
            A=gen('representable2' if kind=='mixed' else kind);B=gen('sparse-paving' if kind=='mixed' else kind)
            check_matroid(A['bases'],n,r);check_matroid(B['bases'],n,r)
            C=sorted(set(A['bases'])&set(B['bases']))
            if not C:continue
            inst={'kind':kind,'n':n,'r':r,'matroid1':A,'matroid2':B,'common':C};idx=len(instances);instances.append(inst)
            for t in range(8):
                w=[1]*n if t==0 else [R.choice([1,2,3,5,11,37,101]) for _ in range(n)]
                p,x=gibbs(C,n,w);F=float_ent(x);bb=float_ent([1-a for a in x]);H=float_ent(p)
                laws.append({'instance':idx,'trial':t,'activities':w,'float_ratio':(F-H)/bb if bb else 0,'float_defect':F-H-(1-1/r)*bb})
            if j%4==0:
                geometries.append({'instance':idx,'type':'whole','data':geometry(A['bases'],B['bases'],C,n)})
                # Every maximizing set for an integral linear objective is an exposed face.
                theta=[R.randrange(-3,4) for _ in range(n)];score=lambda a:sum(theta[i] for i in bits(a,n));mx=max(map(score,C));face=[a for a in C if score(a)==mx]
                geometries.append({'instance':idx,'type':'exposed','theta':theta,'face':face,'data':geometry(A['bases'],B['bases'],face,n)})
    # Even cycles: exact extremizers and failed common-basis-root reserves.
    for r in range(2,8):
        n=2*r;parts1=[[2*i,2*i+1] for i in range(r)];parts2=[[2*i+1,(2*i+2)%n] for i in range(r)]
        def pm(parts):return [mask(t) for t in combinations(range(n),r) if all(len(set(t)&set(p))==1 for p in parts)]
        A=pm(parts1);B=pm(parts2);C=sorted(set(A)&set(B));assert len(C)==2 and C[0]&C[1]==0
        idx=len(instances);instances.append({'kind':'cycle','n':n,'r':r,'matroid1':{'kind':'partition','blocks':parts1,'bases':A},'matroid2':{'kind':'partition','blocks':parts2,'bases':B},'common':C})
        for t,k in enumerate([1,2,101]):
            w=[1]*n;w[bits(C[0],n)[0]]=k;p,x=gibbs(C,n,w)
            laws.append({'instance':idx,'trial':t,'activities':w,'float_ratio':float(Q(r-1,r)),'float_defect':0})
    # Certify all family leaders, all cycles, and a deterministic sample.
    selected={i for i,row in enumerate(laws) if instances[row['instance']]['kind']=='cycle' or i%19==0}
    for kind in sorted(set(i['kind'] for i in instances)):
        ii=[i for i,v in enumerate(laws) if instances[v['instance']]['kind']==kind]
        selected.update(sorted(ii,key=lambda i:laws[i]['float_defect'],reverse=True)[:8])
        selected.update(sorted(ii,key=lambda i:laws[i]['float_ratio'],reverse=True)[:8])
    cert=[certify(laws[i],instances[laws[i]['instance']]) for i in sorted(selected)]
    # Incompatible gluing across a rank-one tight flat of M1, already a 4-cycle.
    compat={'n':4,'M1_blocks':[[0,1],[2,3]],'M2_blocks':[[0,3],[1,2]],'common':[mask([0,2]),mask([1,3])],
            'tight_flat':[0,1],'independent_product_invalid_probability':'1/2','joint_entropy':'log(2)','independent_marginal_entropy':'2 log(2)'}
    # Universal root=common-basis subtraction at coefficient 1 fails at p=1/102.
    p=Q(1,102);hh=ent_iv([p,1-p]);bp=ent_iv([1-p]);rootgap=[hh[0]-2*bp[1],hh[1]-2*bp[0]];assert rootgap[0]>0
    # z0*z2+z1*z3 along (1+t,1-t,1+t,1-t) is 2+2t^2.
    failures={'gluing':compat,'basis_root':{'r':2,'p':str(p),'activities':[1,101,1,1],'root':[1,3],'D_minus_W_interval':list(map(str,rootgap))},'log_concavity':{'polynomial':'z0*z2+z1*z3','direction':[1,-1,1,-1],'log_second_derivative_at_ones':'2','covariance_positive_eigenvalue':'1','active_row_rank':3,'dimension':1}}
    data={'seed':290923,'instance_count':len(instances),'law_count':len(laws),'certified_count':len(cert),'geometric_checks':len(geometries),'instances':instances,'laws':laws,'certificates':cert,'geometry':geometries,'obstructions':failures,'limitations':'Finite screens; float scores exploratory. Certificates use exact rational probabilities and outward rational logarithm intervals. No optimizer or universal numerical inference.'}
    (OUT/'results.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({k:data[k] for k in ['instance_count','law_count','certified_count','geometric_checks']}))
if __name__=='__main__':main()
