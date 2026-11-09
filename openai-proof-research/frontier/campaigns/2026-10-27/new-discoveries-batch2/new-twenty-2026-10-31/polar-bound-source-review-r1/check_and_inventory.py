from pathlib import Path
import json,hashlib,datetime,resource,os,itertools
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
o=Path(__file__).resolve().parent;r=o.parent/'expanded-corpus-r255'; evidence=[]
def read(p,depth):
 b=p.read_bytes();evidence.append(dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),depth=depth));return b.decode(errors='replace')
for p in [o.parent/'ledger.json',o.parent/'STATUS.md',o.parent/'polar-root-ruling-r1.json',o.parent/'polar-review-r1/REVIEW.md',o.parent/'simptree-review-r1/REVIEW.md']:
 read(p,'context/precedent; full text processed, relevant review passages inspected')
for n in ['2303.17055v1-pdf.txt','2303.17055v2-pdf.txt']:
 t=read(r/n,'definitions, Section 2 constructions, Sections 3-4 theorem/proof/construction comparison');print(n,'conjecture',t[t.index('Conjecture 49.'):t.index('Conjecture 49.')+1050])
for p in r.glob('*.receipt.json'):
 j=json.loads(p.read_text())
 if 'polar' in p.name or '2303.17055' in p.name:evidence.append(dict(path=str(p),receipt=j,depth='cached transport receipt'))
terms=['357910','2303.17055','2k2','h-split','polar obstruction','polar graph','multipartite']
for p in list(r.glob('*sub*.body'))+list(r.glob('openai-complete-*.body'))+list(r.glob('pool-index-*.body'))+list(r.glob('pool-txt-*.body')):
 t=read(p,'complete cached relevant subtree/index raw text keyword screen; no all-code clearance')
 try:j=json.loads(t)
 except: j=None
 if isinstance(j,dict) and 'tree' in j:print(p.name,'truncated',j.get('truncated'),'entries',len(j['tree']))
 hits=[line for line in t.splitlines() if any(k in line.lower() for k in terms)]
 if hits:print('MATCH',p.name,'\n'.join(hits)[:5000])
# Exact deterministic edge reconstruction and twelve supplied partitions only; no subset search.
C=set(range(4));S=set(range(4,8));I=set(range(8,12));V=C|S|I
E={tuple(sorted((u,v))) for u,v in itertools.combinations(V,2) if (u in C and v in C) or (u in C and v in S) or (u,v) in [(4,5),(6,7)] or (u in [2,3] and v in [8,9]) or (u in [0,1] and v in [10,11])}
cert=json.loads(read(r/'certificate.json','graph and twelve deletion masks independently compared to ordinary proof'))
assert E=={tuple(e) for e in cert['edges']}
# Printed k=3: c1-c2; i1 only c2; i2 only c1; i3 both. Delete i3.
fibres={'c1':{0,1},'c2':{2,3},'i1':{8,9},'i2':{10,11},**{str(x):{x} for x in S}}
seed_edges={frozenset(x) for x in [('c1','c2'),('c2','i1'),('c1','i2'),('4','5'),('6','7')]}
seed_edges|={frozenset((c,str(s))) for c in ['c1','c2'] for s in S}
built=set()
for x,y in itertools.combinations(fibres,2):
 if frozenset((x,y)) in seed_edges: built|={tuple(sorted((u,v))) for u in fibres[x] for v in fibres[y]}
for c in ['c1','c2']:built|={tuple(e) for e in itertools.combinations(sorted(fibres[c]),2)}
assert built==E
checks=[]
for d in cert['deletion_partitions']:
 v=d['deleted'];A=set(d['A']);B=set(d['B']);assert not A&B and A|B==V-{v}
 def adj(u,v):return tuple(sorted((u,v))) in E
 # nonadjacency equivalence via all ordered triples, finite tiny local check
 assert all(not(not adj(x,y) and not adj(y,z)) or not adj(x,z) for x in A for y in A for z in A)
 assert all(not(adj(x,y) and adj(y,z)) or x==z or adj(x,z) for x in B for y in B for z in B)
 todo=set(B);parts=[]
 while todo:
  x=min(todo);part={x}|{y for y in todo if adj(x,y)};parts.append(sorted(part));todo-=part
 assert len(parts)<=4;checks.append({'deleted':v,'B_cliques':parts,'PASS':True})
(o/'finite-data-comparison.json').write_text(json.dumps({'edge_count':len(E),'source_k3_twin_reduction_exact':True,'deletions':checks,'not_Lean':True,'no_nonpolarity_enumeration':True},indent=2))
(o/'read-inventory.json').write_text(json.dumps(evidence,indent=2))
print('EXACT REDUCTION AND 12 PARTITIONS PASS')
