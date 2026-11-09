# Graphicness test for a 3-connected simple binary matroid M (vectors over GF(2)).
# If M = M(G), G is (up to Whitney) a 3-connected simple graph, and its vertex stars are exactly the
# non-separating cocircuits D (M\D connected). So: compute non-separating cocircuits; if every element lies in exactly
# two, build G and compare circuit families; equality => graphic. Otherwise (or mismatch) => not graphic.
import sys, json, itertools
src=open(sys.path[0]+'/orderable_binary_search.py').read().split('t=time.time()')[0]
_a=sys.argv; sys.argv=['x','3','7','0']; exec(src); sys.argv=_a
def dual_vectors(vecs):
    # cocircuits of M are minimal nonempty supports of the row space of the representation matrix
    m=len(vecs); r=max(v.bit_length() for v in vecs)
    rows=[sum(((vecs[j]>>i)&1)<<j for j in range(m)) for i in range(r)]
    sp=set([0])
    for row in rows: sp|={x^row for x in sp}
    sp.discard(0); sp=sorted(sp,key=lambda s:bin(s).count('1')); co=[]
    for s in sp:
        if not any((c&s)==c for c in co): co.append(s)
    return co
def connected_matroid(vecs):
    if len(vecs)<=1: return True
    circ=circuits(vecs); m=len(vecs)
    if any(v==0 for v in vecs): return False
    parent=list(range(m))
    def f(x):
        while parent[x]!=x: x=parent[x]
        return x
    for c in circ:
        el=[i for i in range(m) if c>>i&1]
        for a in el[1:]: parent[f(a)]=f(el[0])
    return len({f(i) for i in range(m)})==1
def is_graphic_3conn(vecs):
    m=len(vecs); co=dual_vectors(vecs)
    ns=[D for D in co if connected_matroid([vecs[i] for i in range(m) if not D>>i&1])]
    cnt=[sum(1 for D in ns if D>>i&1) for i in range(m)]
    if any(c!=2 for c in cnt): return False, {'nonsep_cocircuits':len(ns),'element_counts':cnt}
    edges=[tuple(j for j,D in enumerate(ns) if D>>i&1) for i in range(m)]
    gv=[(1<<a)|(1<<b) for a,b in edges]
    same=sorted(circuits(gv))==sorted(circuits(vecs))
    return same, {'vertices':len(ns),'edges':edges}
if __name__=='__main__':
    for path in sys.argv[1:]:
        st=json.load(open(path)); res=[]
        for v in st['cands']:
            g,info=is_graphic_3conn(v); res.append({'vecs':v,'graphic':g,'info':info})
        print(json.dumps({'file':path,'num_candidates':len(res),'num_nongraphic':sum(1 for x in res if not x['graphic']),'nongraphic':[x for x in res if not x['graphic']][:3],'graphic_examples':[x['info'] for x in res if x['graphic']][:2]}))
