# Generate projective point pools for dbl2: all pairwise intersection points of K lines a x + b y + c z = 0
# with integer coefficients (seeded random choice from a small box, allowing concurrencies), deduplicated
# as projective points (primitive integer vectors, sign-normalised). Optional extra random points.
import random,sys,math,itertools,pathlib
def norm(v):
  g=0
  for x in v: g=math.gcd(g,abs(x))
  if g==0: return tuple(v)
  v=[x//g for x in v]
  for x in v:
    if x!=0:
      if x<0: v=[-y for y in v]
      break
  return tuple(v)
def pool(K,box,seed,extra=0):
  R=random.Random(seed); lines=set()
  while len(lines)<K:
    l=norm([R.randint(-box,box) for _ in range(3)])
    if any(l) and l[:2]!=(0,0): lines.add(l)
  lines=sorted(lines); pts=set()
  for a,b in itertools.combinations(lines,2):
    c=(a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0])
    if any(c): pts.add(norm(list(c)))
  for _ in range(extra): pts.add(norm([R.randint(-9,9),R.randint(-9,9),R.randint(1,9)]))
  return lines,sorted(pts)
if __name__=='__main__':
  K,box,seed,extra,out=int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]),int(sys.argv[4]),sys.argv[5]
  lines,pts=pool(K,box,seed,extra)
  pathlib.Path(out).write_text(''.join(f'{x} {y} {z}\n' for x,y,z in pts))
  print(len(lines),'lines',len(pts),'points',lines)
