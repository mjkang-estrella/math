"""Independent I95 semantic reconstruction and REAL interval audit; no I91 imports.
Stdlib only. Offline, read-only, no search/generator execution, no writes.
"""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from itertools import combinations, permutations
from fractions import Fraction as Q
from math import gcd,lcm
from collections import deque,Counter
import json,hashlib
ROOT=Path(__file__).resolve().parents[3]
CERT='frontier/experiments/i91_finite_cat0_obstruction/certificate.json'
def sha(x):return hashlib.sha256(json.dumps(x,separators=(',',':'),sort_keys=True).encode()).hexdigest()
def reconstruct():
    # Literal seven two-dimensional subspaces, checked independently by XOR.
    lines=['123','145','167','246','257','347','356']
    assert all(int(s[0])^int(s[1])==int(s[2]) for s in lines)
    assert {tuple(map(int,s)) for s in lines}=={tuple(sorted((a,b,a^b))) for a,b in combinations(range(1,8),2)}
    points=['X'+str(i) for i in range(1,8)]+['Y'+str(i) for i in [1,2,4,7]]
    core=sorted(points+['L'+s for s in lines]);adj={v:set() for v in core}
    for p in points:
        for s in lines:
            if p[1] in s and (p,s)!=('Y7','347'):
                adj[p].add('L'+s);adj['L'+s].add(p)
    edges={tuple(sorted((v,w))) for v in core for w in adj[v]}
    # Enumerate graph cycles directly, not via author's triple/representative loop.
    cycles=set()
    def visit(path):
        if len(path)==6:
            if path[0] not in adj[path[-1]]:return
            p=[int(v[1:]) for v in path if v[0] in 'XY']
            if len(set(p))!=3 or p[0]^p[1]^p[2]==0:return
            orbits=[]
            for seq in [path,list(reversed(path))]:
                orbits.extend(tuple(seq[k:]+seq[:k]) for k in range(6))
            cycles.add(min(orbits));return
        for v in sorted(adj[path[-1]]):
            if v not in path:visit(path+[v])
    for v in core:visit([v])
    cycles=sorted(cycles);opp=[{tuple(sorted((cy[i],cy[i+3]))) for i in range(3)} for cy in cycles]
    distances=[]
    for start in range(len(cycles)):
        dist={start:0};todo=deque([start])
        while todo:
            u=todo.popleft()
            for v in range(len(cycles)):
                if v not in dist and opp[u]&opp[v]:dist[v]=dist[u]+1;todo.append(v)
        assert len(dist)==len(cycles);distances.append(max(dist.values()))
    assert len(edges)==32 and len(cycles)==86 and max(distances)==3
    assert set().union(*(set(c) for c in cycles))==set(core)
    assert ('L347','Y7') not in edges and ('L347','X7') in edges
    full_witness=[]
    mids=set()
    for group in opp:
        for a,b in group:mids.add(('c',a,b))
    for letter,i in zip('ABCD',[1,2,4,7]):
        name='J'+letter;mids.add((name,'X'+str(i),'Y'+str(i)))
        full=adj['X'+str(i)]&adj['Y'+str(i)]
        for H,H2 in combinations(sorted(full),2):
            mids.add((name,H,H2))
            witnesses=[]
            for cy in cycles:
                if H in cy and H2 in cy:
                    p=cy[(cy.index(H)+3)%6]
                    if H2 in adj[p]:witnesses.append((cy,p))
            assert witnesses;full_witness.append([i,H,H2,witnesses[0][1],list(witnesses[0][0])])
    mids.add(('c','JC','JD'))
    extra=[('u','L145','JD'),('up','L246','JD'),('v','L167','JC'),('vp','L257','JC'),('m','u','v'),('mp','up','vp')]
    mids.update(extra);mids=sorted(mids)
    names=sorted(core+['c','JA','JB','JC','JD']+[r[0] for r in extra]);pairs=list(combinations(names,2));index={p:i for i,p in enumerate(pairs)}
    def var(a,b):return index[tuple(sorted((a,b)))]
    ideal={}
    def specify(a,b,value):
        k=var(a,b);value=Q(value)
        if k in ideal:assert ideal[k]==value
        ideal[k]=value
    for a,b in edges:specify(a,b,1)
    for a,b in combinations(core,2):
        if adj[a]&adj[b]:specify(a,b,2)
    for group in opp:
        for a,b in group:specify(a,b,3)
    for v in core:specify('c',v,Q(3,4))
    for j in ['JA','JB','JC','JD']:specify('c',j,Q(1,4))
    specify('JC','JD',1);specify('JC','X7',Q(3,2))
    initial=[[0,4*(2**24)] for _ in pairs]
    for k,value in ideal.items():initial[k]=[int(value*2**24)]*2
    row_provenance={}
    def insert(terms,kind,witness):
        coeff=Counter()
        for a,b,c in terms:
            if a!=b:coeff[var(a,b)]+=Q(c)
        coeff={k:v for k,v in coeff.items() if v}
        if not coeff:return
        den=lcm(*(v.denominator for v in coeff.values()))
        integer={k:int(v*den) for k,v in coeff.items()};div=gcd(*integer.values())
        row=tuple(sorted((k,v//div) for k,v in integer.items()))
        assert div>0
        if row not in row_provenance:row_provenance[row]=(kind,witness)
    for m,a,b in mids:
        for z in [a,b]:
            for sign in [1,-1]:insert([(m,z,4*sign),(a,b,-sign)],'midpoint_endpoint',[m,a,b,z,sign])
        for z in names:insert([(m,z,4),(a,z,-2),(b,z,-2),(a,b,1)],'CN',[m,a,b,z])
    # Choose unordered perfect matchings as diagonals; remaining four pairs are sides.
    for four in combinations(names,4):
        a=four[0]
        for b in four[1:]:
            c,d=[v for v in four if v not in (a,b)]
            insert([(a,b,1),(c,d,1),(a,c,-1),(a,d,-1),(b,c,-1),(b,d,-1)],'quadrilateral',[a,b,c,d])
    for z in names:
        if z=='c':continue
        for a,b in combinations([v for v in names if v not in ('c',z)],2):
            for q in map(Q,['2/5','1/2','1','2','5/2']):
                for orient in [1,-1]:
                    insert([('c',b,orient),(z,a,orient),('c',a,-orient),(z,b,-orient),('c',z,-q),(a,b,-1/q)],'Young_Reshetnyak',['c',z,a,b,str(q),orient])
    rows=sorted(row_provenance)
    assert len(names)==29 and len(pairs)==406 and len(mids)==65 and len(rows)==151892
    assert max(sum(abs(c) for k,c in r) for r in rows)==69
    return dict(names=names,pairs=pairs,mids=mids,rows=rows,initial=initial,provenance=row_provenance,witnesses=full_witness,cycles=cycles,diam=max(distances),edges=edges,adj=adj)

def check_certificate(r):
    c=json.loads((ROOT/CERT).read_text());D=2**24
    assert c['names']==r['names'] and c['pairs']==[list(p) for p in r['pairs']]
    assert c['initial']==r['initial'] and c['midpoints']==[list(m) for m in r['mids']]
    assert c['dyadic_denominator']==D and c['inequalities']==len(r['rows'])
    expected_used=sorted(set(step[0] for step in c['trace'])|{c['contradiction']['row']})
    assert len(expected_used)==1687 and set(c['used_rows'])==set(map(str,expected_used))
    for i in expected_used:assert c['used_rows'][str(i)]==[list(t) for t in r['rows'][i]]
    bounds=[[Q(a,D),Q(b,D)] for a,b in r['initial']]
    errors=[[1,1] for _ in bounds];slacks=[];types=Counter()
    for step,(row_index,k,side,numer) in enumerate(c['trace'],1):
        row=r['rows'][row_index];coef=dict(row)[k]
        minimum_other=sum(co*bounds[j][co<0] for j,co in row if j!=k)
        unrounded=-minimum_other/coef;value=Q(numer,D)
        typ=r['provenance'][row][0];types[typ]+=1
        if side=='upper':
            assert coef>0 and value>=unrounded and value<bounds[k][1]
            endpoint=1;slacks.append(value-unrounded)
        else:
            assert side=='lower' and coef<0 and value<=unrounded and value>bounds[k][0]
            endpoint=0;slacks.append(unrounded-value)
        # Independently carry a conservative integer coefficient of delta.
        # RHS delta plus all required prior endpoint errors; no discretization of REAL distances.
        loss=1+sum(abs(co)*errors[j][co<0] for j,co in row if j!=k)
        newerr=(loss+abs(coef)-1)//abs(coef)
        assert newerr<=100*max(v for pair in errors for v in pair)
        bounds[k][endpoint]=value;errors[k][endpoint]=newerr
        assert bounds[k][0]<=bounds[k][1]
    assert len(c['trace'])==2953
    final=r['rows'][c['contradiction']['row']]
    margin=sum(co*bounds[j][co<0] for j,co in final)
    assert margin==Q(93183,8388608)>Q(1,100)
    assert c['contradiction']['row']==85821
    named=[(r['pairs'][j],co,str(bounds[j][co<0])) for j,co in final]
    errmax=max(v for pair in errors for v in pair)
    assert errmax<=100**2953
    final_error=1+sum(abs(co)*errors[j][co<0] for j,co in final)
    assert Q(final_error,10**10000)<margin
    assert 69*Q(1,10**4000)+Q(1,10**10000)<Q(1,100)
    # Non-dyadic REAL boundary: inward rounding loses an actual Euclidean distance.
    v=Q(1,3);assert Q((D+2)//3,D)>v>Q(D//3,D)
    assert max(slacks)<Q(1,D) and any(slacks)
    return {'status':'PASS_INDEPENDENT_SEMANTICS_AND_REAL_TRACE','points':len(r['names']),'variables':len(r['pairs']),'midpoints':len(r['mids']),'rows':len(r['rows']),'rows_sha256':sha(r['rows']),'used_rows':len(expected_used),'updates':len(c['trace']),'margin':str(margin),'final_row_named':named,'nonzero_outward_roundings':sum(x>0 for x in slacks),'trace_semantic_types':dict(sorted(types.items())),'independent_error_coefficient_digits':len(str(final_error)),'full_line_witnesses':r['witnesses'],'hexagons':len(r['cycles']),'diameter':r['diam']}

if __name__=='__main__':print(json.dumps(check_certificate(reconstruct()),indent=2,sort_keys=True))
