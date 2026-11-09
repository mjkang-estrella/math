import itertools as it,re,json,collections,pathlib
O=pathlib.Path(__file__).resolve().parent; F=O/'proof'; edges=list(it.combinations(range(5),2)); ts=list(it.combinations(range(5),3)); incidence=[tuple(edges.index(e) for e in it.combinations(t,2)) for t in ts]; labels='abcdefghij'; codes=[' '.join(labels[i] for i in t) for t in incidence]
s=(F/'Checker.lean').read_text(); pairs=re.findall(r'\(code ([a-j] [a-j] [a-j])\) = \(code ([a-j] [a-j] [a-j])\)',s); expected=set(it.combinations(range(10),2)); actual=[tuple(sorted((codes.index(a),codes.index(b)))) for a,b in pairs];assert len(actual)==45 and set(actual)==expected
# Check each branch tests only triangles completed at its own depth, and each coordinate branches once.
stages={}
for depth,body in re.findall(r'def check(\d+)(.*?)(?=\ndef |\ntheorem)',s,re.S):
 d=int(depth); tests=re.findall(r'\(code ([a-j] [a-j] [a-j])\) = \(code ([a-j] [a-j] [a-j])\)',body)
 assert all(max(labels.index(c) for c in a+b if c!=' ')+1==d for a,b in tests)
 if d<10:
  assert f'all4 fun {labels[d]} =>' in body
 stages[depth]=len(tests)
endpoint=(F/'Endpoint.lean').read_text();bridge=[tuple(map(int,p)) for p in re.findall(r'have ht : t(\d) = t(\d)',endpoint)];assert bridge==list(it.combinations(range(10),2))
sets={};
for t in it.product(range(4),repeat=3):
 mask=(1<<t[0])|(1<<t[1])|(1<<t[2]);p=frozenset(t);assert mask not in sets or sets[mask]==p;sets[mask]=p
hist=collections.Counter();valid=0
for a in it.product(range(4),repeat=10):
 ps={frozenset(a[e] for e in tri) for tri in incidence};hist[len(ps)]+=1;valid+=len(ps)==10
assert valid==0 and sum(hist.values())==4**10
assert frozenset([0,0,1])==frozenset([0,1,1]) # sets erase multiplicities
assert (1<<0)|(1<<0)|(1<<1)==3
# Positive control with ten distinct edge labels: triangle supports are distinct.
assert len({frozenset(t) for t in incidence})==10
r={'edges':edges,'triangles':ts,'incidence':incidence,'code_triples':codes,'pair_tests':len(actual),'stage_tests':stages,'no_four_bridge_pairs':bridge,'codes_checked':64,'full_assignments':4**10,'pruning':False,'symmetry':False,'valid':valid,'palette_count_histogram':dict(hist),'positive_distinct_edge_labels':True,'multiplicity_erasure':True};print(json.dumps(r,indent=2))
