import itertools,math,json
m=6;v=set();image=set()
for p in itertools.permutations(range(m)):
 for mask in range(1<<m):
  w=[]
  for j,k in enumerate(p):w.extend([2*k+1+(mask>>j&1),2*k+2-(mask>>j&1)])
  v.add(tuple(w));c=tuple(w[2*j]+w[2*j+1] for j in range(m));d=tuple(w[2*j+1]-w[2*j] for j in range(m));image.add((c,d))
  assert sorted(c)==[4*k+3 for k in range(m)] and all(x in [-1,1] for x in d)
assert len(v)==len(image)==math.factorial(m)*2**m
print(json.dumps(dict(m=m,vertices=len(v),affine_image_vertices=len(image),finding='exact product vertex set: scaled permutahedron times cube',limitation='not a facet computation; product identity gives the ordinary proof')))
