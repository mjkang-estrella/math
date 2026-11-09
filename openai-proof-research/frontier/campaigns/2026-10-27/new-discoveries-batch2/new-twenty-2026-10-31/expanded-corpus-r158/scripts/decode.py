import pathlib,json,sys,itertools
L=pathlib.Path(__file__).resolve().parents[1];m,n=map(int,sys.argv[1:]);v=m*n
log=(L/'outputs'/f'grid-{m}-{n}.log').read_text();pos=set(int(w) for l in log.splitlines() if l.startswith('v ') for w in l.split()[1:] if int(w)>0)
vs={(a,b):i for a,b,i in json.loads((L/'work'/f'grid-{m}-{n}.vars.json').read_text())}
def lt(a,b):return (vs[a,b] in pos) if a<b else not lt(b,a)
order=sorted(range(3*v),key=lambda a:sum(lt(b,a) for b in range(3*v) if b!=a))
word=[a//3 for a in order]
bad=[]
for a,b in itertools.combinations(range(v),2):
 seq=[c for c in word if c in (a,b)]
 alt=all(x!=y for x,y in zip(seq,seq[1:]))
 xa,ya=divmod(a,n);xb,yb=divmod(b,n)
 edge=(xa==xb and (ya-yb)%n in [1,n-1]) or (ya==yb and (xa-xb)%m in [1,m-1])
 if alt!=edge:bad.append([a,b,seq,edge])
out={'m':m,'n':n,'word':word,'length':len(word),'counts':[word.count(a) for a in range(v)],'bad_pairs':bad,'pairs_checked':v*(v-1)//2}
(L/'outputs'/f'grid-{m}-{n}-witness.json').write_text(json.dumps(out,indent=2));print(out)
