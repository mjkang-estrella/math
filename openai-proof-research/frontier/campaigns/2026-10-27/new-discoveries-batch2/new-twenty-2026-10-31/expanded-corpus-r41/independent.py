import pathlib,json,resource,os
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(30,30));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
p=pathlib.Path(__file__).resolve().parent;w=json.loads((p/'leaf-extended-witness.json').read_text());es=w['edges'];ms=[]
for mask in range(1<<len(es)):
 vs=[v for i,e in enumerate(es) if mask>>i&1 for v in e]
 if len(vs)==len(set(vs)):ms.append(mask)
nu=max(m.bit_count() for m in ms);lam=max((h|j).bit_count() for h in ms for j in ms if not h&j);mu=max(h.bit_count() for h in ms for j in ms if not h&j and (h|j).bit_count()==lam)
trip=[(m,h,j) for m in ms if m.bit_count()==nu for h in ms if h.bit_count()==mu for j in ms if not h&j and (h|j).bit_count()==lam];lex=max(((m&(h|j)).bit_count(),(m&h).bit_count()) for m,h,j in trip);opt=[x for x in trip if ((x[0]&(x[1]|x[2])).bit_count(),(x[0]&x[1]).bit_count())==lex]
assert (nu,lam,mu)==(6,10,5);assert (w['M'],w['H'],w['Hp']) in opt
left={0,3,5,7,8,10};assert all((a in left)!=(b in left) for a,b in es)
for u,v in zip([7,6,0,1,10],[6,0,1,10,11]):assert tuple(sorted((u,v))) in map(tuple,es)
(p/'leaf-independent.json').write_text(json.dumps({'catalog':ms,'nu':nu,'lambda':lam,'mu':mu,'optimal_triples':opt,'lex':lex},indent=2));print('Independent powerset check:',len(ms),'matchings;',len(trip),'triples before overlaps;',len(opt),'fully optimal triples; bipartition and path edges checked.')
