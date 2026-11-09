import itertools,json,pathlib
# Tetrahedral plane graph is self-dual; proper face n-colorings equal vertex n-colorings of K4.
out={}
for n in [2,3,4,5]:
 count=sum(all(c[i]!=c[j] for i in range(4) for j in range(i+1,4)) for c in itertools.product(range(n),repeat=4));out[n]=count;print(n,count)
pathlib.Path('outputs/facecolor.json').write_text(json.dumps(out,indent=2))
