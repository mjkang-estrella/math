# Merge chunk files: group by CSF hash; report collision classes and those with differing invariants.
import sys, json, collections
paths = sys.argv[2:]; G = collections.defaultdict(list); n = 0
for p in paths:
    for line in open(p):
        h, seq, inv = json.loads(line); G[h].append((seq, json.dumps(inv))); n += 1
coll = [v for v in G.values() if len(v) > 1]
bad = [v for v in coll if len({inv for _, inv in v}) > 1]
res = dict(graphs=n, distinct_csf=len(G), collision_classes=len(coll), collision_classes_with_differing_invariants=len(bad),
           examples_collision=coll[:3], examples_bad=bad[:5])
json.dump(res, open(sys.argv[1], 'w'), indent=1)
print('graphs', n, 'distinct', len(G), 'collisions', len(coll), 'bad', len(bad))
