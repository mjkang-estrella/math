#!/usr/bin/env python3
"""Project a legacy nd tree onto coefficient-permutation orbits.
The legacy file is an untrusted search hint. New rest kills and re-enumerated size
leaves are independently checked by check_sym. Ordered source size lists are NOT
copied: the resulting domain is genuinely unordered.
"""
import collections
import hashlib
import json
import pathlib
import sys
sys.dont_write_bytecode=True
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from gen_sym import Generator


def project(source,dest,seconds=120):
    data=pathlib.Path(source).read_bytes()
    records=[json.loads(line) for line in data.splitlines() if line.strip()]
    meta=records[0]
    coefs=meta['coefs']
    old={n['id']:n for n in records[1:]}
    root=[n for n in old.values() if n['p']==-1][0]
    assert meta['root']['m']==1 and all(x==0 for x in meta['root']['r'])
    G=Generator(coefs,meta['K'],meta['qmin'],seconds=seconds,lifts=10**10,nodes=10000000)
    G.new(G.zero(),1,-1)
    todo=[(0,root)]
    while todo:
        idx,nd=todo.pop()
        G.check_budget()
        M=nd['m']
        nr=G.nodes[idx]['r']
        r=(nr[0],)+tuple(e for xs in nr[1:] for e in xs)
        if nd['k']=='l':
            if 'prime' in nd['x']:
                G.nodes[idx].update(k='l',x={'prime':nd['x']['prime']})
            else:
                assert 'sz' in nd['x']
                a,w=G.sig(r,M)
                assert a[1] is not None and w[1] is not None
                N=2**G.t0*3**a[0]*7**w[0]
                G.nodes[idx].update(k='l',x={'sz':[a[0],w[0]],'sol':G.exact(N,r,M)})
            continue
        Q=nd['m2']
        lookup={tuple(x%Q for x in old[c]['r']):old[c] for c in nd['c']}
        G.nodes[idx].update(k='i',m2=Q,c=[],rest=nd['rest'] or [])
        for rr in G.lifts_of(r,M,Q//M):
            G.lifts+=1
            if G.lifts%2048==0: G.check_budget()
            remaining=collections.defaultdict(list)
            for c,e in zip(G.coefs,rr[1:]): remaining[c].append(e)
            labelled=[rr[0]]
            for c,b in zip(coefs,nd['r'][1:]):
                options=remaining[c]
                j=next(j for j,e in enumerate(options) if e%M==b%M)
                labelled.append(options.pop(j))
            child=lookup.get(tuple(labelled))
            if child is not None:
                k=G.new(rr,Q,idx)
                G.nodes[idx]['c'].append(k)
                todo.append((k,child))
    G.write(dest,extra={'projection_source':str(source),'source_sha256':hashlib.sha256(data).hexdigest()})
    return {'source':str(source),'certificate':str(dest),'source_nodes':len(old),
            'nodes':len(G.nodes),'refinements':G.lifts,'solutions':G.solutions(),
            'source_sha256':hashlib.sha256(data).hexdigest()}

if __name__=='__main__':
    print(json.dumps(project(sys.argv[1],sys.argv[2])))
