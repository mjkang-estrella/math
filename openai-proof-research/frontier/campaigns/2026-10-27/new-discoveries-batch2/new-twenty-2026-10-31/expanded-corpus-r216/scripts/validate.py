from itertools import product,combinations
import runpy,pathlib
L=pathlib.Path(__file__).resolve().parents[1]
# Independent brute subset validation of ideal-difference generation, convexity, and toggle legality.
for m,n in [(2,2),(2,3),(3,3)]:
 N=m*n;intervals=[(x,y,sum(1<<z for z in range(N) if x//n<=z//n<=y//n and x%n<=z%n<=y%n)) for x in range(N) for y in range(N) if x//n<=y//n and x%n<=y%n]
 convex={s for s in range(1<<N) if all(not(s>>x&1 and s>>y&1) or not(t&~s) for x,y,t in intervals)}
 ideals={s for s in range(1<<N) if all(not(s>>y&1) or s>>x&1 for x,y,t in intervals)}
 assert convex=={a&~b for a in ideals for b in ideals if not b&~a}
 print('independent convex generator validation',m,n,len(convex))
# Rado literal wording diagnostic, no intended four-variable resolution.
col={1:0,2:1,3:0,4:0};sol=[(x,y,w) for x,y,w in product(range(1,5),repeat=3) if 3*x+2*y==4*w]
assert all(not(col[x]==col[y]==col[w]) for x,y,w in sol)
print('literal a=2 Rado avoiding colouring',col,'solutions',sol,'zero-credit formulation issue')
