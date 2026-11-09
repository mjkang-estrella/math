# Build C_{t,r}: t+1 general lines L_1..L_{t+1}; all C(t+1,2) intersections, minus (t-r) of the points on L_{t+1}.
import sys,itertools,pathlib
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from pools import norm
t,r,seed,out=int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]),sys.argv[4]
import random; R=random.Random(seed)
while True:
  lines=[norm([R.randint(-9,9) for _ in range(3)]) for _ in range(t+1)]
  pts={}
  for i,j in itertools.combinations(range(t+1),2):
    a,b=lines[i],lines[j]; c=(a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0])
    if any(c): pts[(i,j)]=norm(list(c))
  if len(set(pts.values()))==len(pts)==(t+1)*t//2: break
keep=[p for (i,j),p in pts.items() if j!=t]+[pts[(i,t)] for i in range(r)]
pathlib.Path(out).write_text(''.join(f'{x} {y} {z}\n' for x,y,z in keep)); print(len(keep),'points from lines',lines)
