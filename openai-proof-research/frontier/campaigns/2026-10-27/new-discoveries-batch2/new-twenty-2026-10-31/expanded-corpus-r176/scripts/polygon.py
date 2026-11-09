import itertools,json,pathlib
D=pathlib.Path(__file__).resolve().parents[1]
pts=[(x,y) for x in range(-3,4) for y in range(-3,4) if x*x+y*y>=4]
def ds(a,b):return sum((x-y)**2 for x,y in zip(a,b))
def cross(a,b):return a[0]*b[1]-a[1]*b[0]
def local(p,a,b):
 u=(a[0]-p[0],a[1]-p[1]);v=(b[0]-p[0],b[1]-p[1]);w=(-p[0],-p[1]);det=cross(u,v)
 return det!=0 and cross(w,v)*det>0 and cross(u,w)*det>0
cnt=0;qual=0;bad=[]
for q in itertools.permutations(pts,4):
 if any(ds(q[i],q[(i+1)%4])>8 for i in range(4)):continue
 cnt+=1
 if not all(local(q[i],q[(i-1)%4],q[(i+1)%4]) for i in range(4)):continue
 qual+=1
 if any(ds(q[i],q[(i+1)%4])!=8 for i in range(4)) or ds(q[0],q[2])!=16 or ds(q[1],q[3])!=16:bad.append(q)
r={'P':[(2,0),(0,2),(-2,0),(0,-2)],'grid':'integer [-3,3]^2','candidate_points':len(pts),'ordered_injective_assignments':len(pts)*(len(pts)-1)*(len(pts)-2)*(len(pts)-3),'edge_feasible':cnt,'local_cone_feasible':qual,'nonisometric':bad};(D/'outputs/polygon.json').write_text(json.dumps(r,indent=2)+'\n');print(r)
