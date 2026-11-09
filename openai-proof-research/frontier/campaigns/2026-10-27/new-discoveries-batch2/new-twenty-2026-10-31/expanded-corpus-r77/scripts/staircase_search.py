from fractions import Fraction as F
import pathlib,json
D=pathlib.Path(__file__).resolve().parents[1];a={(1,0):F(1),(2,0):F(-1),(3,0):F(1,3)};hist=[{},a];bad=[]
for k in range(1,9):
 b={};N=3*(k+1)+2
 def get(i,j):return a.get((i,j),F(0))
 def integral(i):return sum((get(i,p)/F(p+1) for p in range(3*k+2)),F(0))
 for j in range(1,N):
  b[1,j]=integral(j)+sum((F(2*p-j+1,(p+1)*(j-p))*get(j-1-p,p) for p in range(j)),F(0))
  b[2,j]=get(1,j)-b[1,j]/2
  for i in range(3,N):b[i,j]=get(i-1,j)-(1+F(1,i*(i-1)))*get(i-2,j)+(F(1,3)+F(1,i*(i-2)))*get(i-3,j)
 b[2,0]=2*integral(1)
 for i in range(3,N):
  b[i,0]=get(i-1,0)-(1+F(1,(i-1)*i))*get(i-2,0)+(F(1,3)+F(1,(i-2)*i))*get(i-3,0)+(1+F(2,i))*integral(i-1)-(F(1,2)+F(2,i))*integral(i-2)-(1+F(2,i))*sum((get(i-2-p,p)/F(p+1) for p in range(i-1)),F(0))+(F(1,2)+F(2,i))*sum((get(i-3-p,p)/F(p+1) for p in range(i-2)),F(0))+sum((get(i-2-p,p)/F(i-p) for p in range(i-1)),F(0))-sum((get(i-3-p,p)/F(i-p) for p in range(i-2)),F(0))/2
 a={ij:v for ij,v in b.items() if v};hist.append(a)
for k,a in enumerate(hist[1:],1):
 for (i,j),v in a.items():
  if (j==0 and i>=3*k) or (j==1 and i>=3*(k-1)) or i>=3*(k-(j+1)//3):bad.append(['staircase',k,i,j,str(v)])
  if k>=i+j+2 and v!=hist[k-1].get((i,j),0):bad.append(['stability',k,i,j,str(v)])
(D/'outputs/search-staircase.json').write_text(json.dumps(dict(id=381131,space='unique deterministic coefficient arrays k1..9; all nonzero support in padded boxes0..3k+1; corrected later Proposition1 recurrence used, not erroneous self-reference of2012 display; exact Fractions',nonzero_counts=[len(a) for a in hist[1:]],violations=bad,arrays=[{str(ij):str(v) for ij,v in a.items()} for a in hist[1:]]),indent=2)+'\n');print('violations',bad[:10])
