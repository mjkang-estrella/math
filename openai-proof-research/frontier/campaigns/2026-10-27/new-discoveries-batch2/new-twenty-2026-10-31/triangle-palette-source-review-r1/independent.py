import itertools, collections, json, time, resource, os
os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
t=time.monotonic()
edges=list(itertools.combinations(range(5),2))
triangles=list(itertools.combinations(range(5),3))
indices=[tuple(edges.index(e) for e in itertools.combinations(v,2)) for v in triangles]
hist=collections.Counter(); good=[]
# Every full word is visited. No partial assignment, symmetry or palette-code reduction.
for word in itertools.product(range(4),repeat=len(edges)):
    palettes=[frozenset(word[i] for i in tri) for tri in indices]
    hist[len(set(palettes))]+=1
    if len(set(palettes))==10:good.append(word)
print(json.dumps(dict(edges=edges,triangles=triangles,indices=indices,total=sum(hist.values()),distinct_palette_histogram=dict(sorted(hist.items())),distinguishing_colorings=len(good),elapsed_seconds=time.monotonic()-t,maxrss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss),indent=2))
assert sum(hist.values())==4**10
assert not good
