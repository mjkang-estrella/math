import collections,itertools,json,pathlib,re
L=pathlib.Path(__file__).resolve().parents[1]
w=list(map(int,'0 8 4 5 9 11 12 13 10 1 2 6 11 0 1 14 5 10 3 4 7 0 8 9 6 5 12 11 2 1 7 6 13 12 3 2 8 14 10 13 4 3 7 9 14'.split()))
def edges(m,n):
    E=set()
    for r,c in itertools.product(range(m),range(n)):
        v=r*n+c
        for s,d in [((r+1)%m,c),(r,(c+1)%n)]: E.add(tuple(sorted((v,s*n+d))))
    return E
def check(m,n,w):
    assert collections.Counter(w)=={v:3 for v in range(m*n)}
    E=edges(m,n); pairs=[]
    for a,b in itertools.combinations(range(m*n),2):
        sub=[x for x in w if x in (a,b)]
        alt=all(x!=y for x,y in zip(sub,sub[1:]))
        p=[i for i,x in enumerate(w) if x==a]; q=[i for i,x in enumerate(w) if x==b]
        inter=all(p[i]<q[i] for i in range(3)) and all(q[i]<p[i+1] for i in range(2)) or all(q[i]<p[i] for i in range(3)) and all(p[i]<q[i+1] for i in range(2))
        assert alt==inter==((a,b) in E),(a,b,sub)
        pairs.append(dict(a=a,b=b,subword=sub,edge=alt))
    return dict(m=m,n=n,word=w,edges=len(E),nonedges=len(pairs)-len(E),pairs=pairs)
res=check(3,5,w)
# Compare extracted Lean literal independently of discovery scripts.
s=(L/'packet/Witness.lean').read_text()
coords=re.findall(r'\(⟨(\d+), by decide⟩, ⟨(\d+), by decide⟩\)',s)
assert [5*int(r)+int(c) for r,c in coords]==w
(L/'pair-check.json').write_text(json.dumps(res,indent=2)+'\n')
print('PASS 45 letters; 15 counts = 3; 105 pairs; 30 edges; 75 nonedges; both checkers agree; Lean literal agrees.')
# Independently validate the two source examples (source uses column-major labels).
for m,n,s in [(3,3,'abcdefgadhigbcaehbfdeighcfi'),(3,4,'ajbkcdaeblfcgdjahkigehfdbelcifjgkhli')]:
    word=[((ord(c)-97)%3)*n+(ord(c)-97)//3 for c in s]
    result=check(m,n,word)
    (L/f'neighbor-{m}-{n}.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS independent source neighbor',m,n,result['edges'])
