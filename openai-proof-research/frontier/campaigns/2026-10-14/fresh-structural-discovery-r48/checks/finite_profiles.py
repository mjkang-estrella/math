#!/usr/bin/env python3
"""MIT. Finite diagnostics only; general proofs are in mechanism-check.md."""
import itertools,json,math

def main():
    profiles=[]
    for d in range(0,6):
        vertices=list(itertools.product(range(3),repeat=d));V=set(vertices)
        neighbors={}
        for x in vertices:
            neighbors[x]={x[:j]+(a,)+x[j+1:] for j in range(d) for a in (x[j]-1,x[j]+1) if 0<=a<=2}
        layers=[sum(x.count(1)==k for x in vertices) for k in range(d+1)]
        assert layers==[math.comb(d,k)*2**(d-k) for k in range(d+1)]
        assert all(len(neighbors[x])==d+x.count(1) for x in vertices)
        b={x:sum(y.count(1)>x.count(1) for y in neighbors[x]) for x in vertices}
        assert all(b[x]==d-x.count(1) for x in vertices)
        codegree=max((len(neighbors[x]&neighbors[y]) for i,x in enumerate(vertices) for y in vertices[i+1:]),default=0)
        assert codegree<=2
        moments=[]
        for p in range(7):
            full=sum(2**(p*len(neighbors[x])) for x in vertices)
            backward=sum(2**(p*b[x]) for x in vertices)
            assert full==(2**(p+1)+2**(2*p))**d
            assert backward==(1+2**(p+1))**d
            moments.append({'p':p,'full':full,'backward':backward})
        profiles.append({'d':d,'vertices':len(vertices),'layers':layers,'max_codegree':codegree,'moments':moments})
    colors=[]
    for d in range(3,7):
        m=(3**d).bit_length()-1;n=2*d
        def label(x):return (x&((1<<m)-1), (x>>m).bit_count()%2)
        counts={};min_nc=n;max_nc=0
        for x in range(1<<n):
            c=label(x);counts[c]=counts.get(c,0)+1
            adj={label(x^(1<<j)) for j in range(n)}
            assert c not in adj
            min_nc=min(min_nc,len(adj));max_nc=max(max_nc,len(adj))
        assert len(counts)==2**(m+1)
        assert set(counts.values())=={2**(2*d-m-1)}
        assert min_nc==max_nc==m+1<2*d
        assert 3**d<=len(counts)<2*3**d
        assert max(counts.values())*3**d<=4**d
        colors.append({'d':d,'cube_dimension':n,'displayed_bits':m,'labels':len(counts),'fiber_size':max(counts.values()),'neighbor_labels':max_nc,'target_center_degree':2*d})
    return {'status':'PASS','profiles':profiles,'colorings':colors,'scope':'Finite checks only, not a Ramsey proof or general theorem certification.'}
if __name__=='__main__':print(json.dumps(main(),indent=2))
