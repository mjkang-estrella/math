#!/usr/bin/env python3
"""MIT. Finite joint retraction LP diagnostic; never an all-tree theorem."""
import json,itertools,random,sys
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix


def solve(parent, weights, anchors, points):
    d=len(parent); k=len(points); a=len(anchors)
    xs=[np.array(x,dtype=float) for x in anchors+points]
    w=np.array(weights,dtype=float)
    # Output coordinates for unknown points, then L, then per-pair norm auxiliaries.
    li=k*d; nvar=li+1; rows=[]; rhs=[]; cols=[]; vals=[]
    def row(v,b):
        idx=len(rhs)
        for c,z in v.items():
            if z:rows.append(idx);cols.append(c);vals.append(z)
        rhs.append(b)
    for i in range(k):
        for e in range(d):
            z={i*d+e:-1}
            for f,p in enumerate(parent):
                if p==e:z[i*d+f]=1
            row(z,0)
    def coord(i,e):
        return ({(i-a)*d+e:1},0) if i>=a else ({},float(xs[i][e]))
    pairs=[]
    for i in range(a+k):
        for j in range(max(a,i+1),a+k):
            dist=float(np.dot(w,np.abs(xs[i]-xs[j])))
            if dist==0:raise ValueError('duplicate points')
            start=nvar;nvar+=d
            pairs.append((i,j,start,dist))
            for e in range(d):
                vi,ci=coord(i,e);vj,cj=coord(j,e)
                for sign in (-1,1):
                    z={start+e:-1}
                    for c,v in vi.items():z[c]=z.get(c,0)+sign*v
                    for c,v in vj.items():z[c]=z.get(c,0)-sign*v
                    row(z,-sign*(ci-cj))
            z={start+e:weights[e] for e in range(d)};z[li]=-dist;row(z,0)
    mat=coo_matrix((vals,(rows,cols)),shape=(len(rhs),nvar)).tocsr()
    obj=np.zeros(nvar);obj[li]=1
    bounds=[(0,None)]*nvar;bounds[li]=(1,None)
    result=linprog(obj,A_ub=mat,b_ub=np.array(rhs),bounds=bounds,method='highs',options={'time_limit':45})
    if not result.success:return {'status':int(result.status),'message':result.message}
    q=result.x[:li].reshape((k,d));L=float(result.fun)
    cone_violation=max([0]+[sum(q[i,f] for f,p in enumerate(parent) if p==e)-q[i,e] for i in range(k) for e in range(d)])
    ys=xs[:a]+list(q)
    max_ratio=max(float(np.dot(w,np.abs(ys[i]-ys[j])))/dist for i,j,_,dist in pairs)
    assert cone_violation<1e-7 and max_ratio<=L+1e-7
    return {'status':0,'minimum_numerical_L':L,'primal_max_pair_ratio':max_ratio,'primal_max_cone_violation':float(cone_violation),'output_flows':q.tolist(),'variables':nvar,'constraints':len(rhs),'limits':'Floating LP optimum; no exact dual certificate and no all-configuration conclusion.'}


def flow(parent,mass):
    q=list(mass)
    for e in reversed(range(len(parent))):
        if parent[e]>=0:q[parent[e]]+=q[e]
    return q


def unique(xs):
    out=[];seen=set()
    for x in xs:
        key=tuple(x)
        if key not in seen:seen.add(key);out.append(x)
    return out


def cases():
    for k in [2,3,4,8]:
        par=[-1]+[0]*k; x=[k-1]+[1]*k
        anchors=[[k]+[1]*k]
        for j in range(k):
            y=x.copy();y[j+1]=0;anchors.append(y)
        yield {'name':f'known_star_{k}','parent':par,'weights':[1]*(k+1),'anchors':anchors,'points':[x],'known_optimum':2*k/(k+1)}
    rng=random.Random(3321743)
    trees={'path7':[-1,0,1,2,3,4,5],'binary7':[-1,0,0,1,1,2,2],'binary15':[-1]+[(i-1)//2 for i in range(1,15)],'comb9':[-1,0,0,1,1,3,3,5,5]}
    for name,par in trees.items():
        d=len(par)
        for case in range(8):
            weights=[1]*d if case<2 else [2.**rng.randint(-3,3) for _ in par]
            anchors=[[0]*d]+[flow(par,[int(i==j) for i in range(d)]) for j in range(d)]
            points=[]
            for _ in range(10):
                mass=[rng.randint(0,4)/4 if rng.random()<.35 else 0 for _ in par]
                if not any(mass):mass[-1]=1
                base=flow(par,mass);anchors.append(base)
                z=base.copy()
                for e in rng.sample(range(d),rng.randint(1,min(3,d))):z[e]+=rng.choice([-1,-.5,-.25,.25,.5,1])
                # Drop accidental feasible points; they belong among fixed anchors.
                feasible=all(z[e]>=sum(z[f] for f,p in enumerate(par) if p==e) for e in range(d))
                if feasible:anchors.append(z)
                else:points.append(z)
            anchors=unique(anchors);points=unique(points)
            yield {'name':f'{name}_{case}','parent':par,'weights':weights,'anchors':anchors,'points':points}


def main():
    for case in cases():
        if not case['points']:continue
        case['result']=solve(case['parent'],case['weights'],case['anchors'],case['points'])
        if 'known_optimum' in case:
            assert case['result']['status']==0
            assert abs(case['result']['minimum_numerical_L']-case['known_optimum'])<1e-8
        if case['name'].startswith('path') and case['result']['status']==0:
            assert abs(case['result']['minimum_numerical_L']-1)<1e-8
        print(json.dumps(case),flush=True)
if __name__=='__main__':main()
