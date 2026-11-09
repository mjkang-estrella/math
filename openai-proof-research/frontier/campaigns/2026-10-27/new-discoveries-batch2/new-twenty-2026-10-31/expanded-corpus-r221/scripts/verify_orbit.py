import pathlib,json,sys
D=pathlib.Path(__file__).resolve().parents[1];m=3;n=int(sys.argv[1]);s=int(sys.argv[2]);N=m*n
pts=[(i,j) for i in range(m) for j in range(n)]
intervals=[sum(1<<k for k,(a,b) in enumerate(pts) if i<=a<=r and j<=b<=t) for i,j in pts for r,t in pts if i<=r and j<=t]
def convex(s):return all(s&v==v for v in intervals if (s&(v&-v)) and (s&(1<<(v.bit_length()-1))))
def row(s):
 for x in reversed(range(N)):
  if convex(s^(1<<x)):s^=1<<x
 return s
start=s;orbit=[]
while s not in orbit:
 assert convex(s);orbit.append(s);s=row(s)
assert s==start
scores=[sum((-1)**(i+j) for k,(i,j) in enumerate(pts) if s>>k&1) for s in orbit]
o={'m':m,'n':n,'start':start,'initial_points_1_based':[[i+1,j+1] for k,(i,j) in enumerate(pts) if start>>k&1],'length':len(orbit),'sum':sum(scores),'states':orbit,'scores':scores,'method':'independent full interval test for every single toggle; lexicographic reverse linear extension'}
p=D/f'outputs/orbit-{n}-{start}.json';assert not p.exists();p.write_text(json.dumps(o,indent=2));print({k:v for k,v in o.items() if k not in ['states','scores']})
