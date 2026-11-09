from pathlib import Path
import json,itertools,collections
L=Path(__file__).resolve().parent
def triples(n):return [(x,y,x+y//2) for y in range(1,n+1) for x in range(1,n-y//2+1)]
def count(c):
 n=len(c)-1
 return sum(c[x]==c[y]==c[z] for x,y,z in triples(n))
def grouped(c):
 n=len(c)-1
 return sum((c[x]==c[x+v])*sum(c[x]==c[y] for y in (2*v,2*v+1) if 1<=y<=n) for v in range(n//2+1) for x in range(1,n-v+1))
def source(n):
 a,b,d=(n+3)//6,(n+1)//2,(5*n+3)//6
 return [None]+[int(a<i<=b or i>d) for i in range(1,n+1)]
def weight(n,i,j):return int(i+j//2<=n)+int(j+i//2<=n)+int(2*(j-i)<=n)+int(2*(j-i)+1<=n)+1+int(i-j//2>=1)
def prefix_identity(c):
 n=len(c)-1;s=[0]+[1-2*v for v in c[1:]];S=[0]
 for v in s[1:]:S.append(S[-1]+v)
 A=sum(s[y]*(S[n-y//2]+S[n]-S[y//2]) for y in range(1,n+1))
 C=sum((len([y for y in (2*v,2*v+1) if 1<=y<=n]))*sum(s[x]*s[x+v] for x in range(1,n-v+1)) for v in range(n//2+1))
 return (n*n-n*n//4+A+C)//4,(n*n-n*n//4+A+C)%4
out={'scope':'Diagnostic exact tests, not a universal proof','exhaustive':[]}
for n in range(1,14):
 badmerge=None;badstep=None;badlocal=None;mn=10**9;arg=None;tested=0
 W={(i,j):weight(n,i,j) for i in range(1,n+1) for j in range(i+1,n+1)}
 for tail in itertools.product(range(2),repeat=n-1):
  c=[None,0]+list(tail);m=count(c);tested+=1
  assert m==grouped(c);assert prefix_identity(c)==(m,0)
  if m<mn:mn=m;arg=c[1:]
  if n>=12 and badmerge is None:
   # A pair whose either monochromatic replacement increases the total,
   # despite a mixed pair contributing the simple inner sum 1.
   for v in range(1,(n-1)//2+1):
    if c[2*v]==c[2*v+1]:continue
    ms=[]
    for color in range(2):
     d=c[:];d[2*v]=d[2*v+1]=color;ms.append(count(d)-m)
    if min(ms)>0:badmerge={'c':c[1:],'pair':[2*v,2*v+1],'M':m,'merge_deltas':ms};break
  if n>=12 and badstep is None:
   delta=m-count(c[:-1]);targetdelta=(n*n+5)//6-((n-1)**2+5)//6
   if delta<targetdelta:badstep={'c':c[1:],'M':m,'prefix_M':count(c[:-1]),'delta':delta,'target_delta':targetdelta}
  if n>=12 and badlocal is None and m>(n*n+5)//6:
   # All one-coordinate energy changes, with every role included.
   s=[0]+[1-2*v for v in c[1:]]
   ds=[-sum(W[min(i,j),max(i,j)]*s[i]*s[j] for j in range(1,n+1) if i!=j)//2 for i in range(1,n+1)]
   if min(ds)>0:badlocal={'c':c[1:],'M':m,'one_flip_deltas':ds}
 out['exhaustive'].append(dict(n=n,tested_complement_representatives=tested,minimum=mn,argmin=arg,merge_obstruction=badmerge,increment_obstruction=badstep,strict_local_obstruction=badlocal))
# Structural blow-ups of the public exceptional 11-word; all coordinates count.
word=[0,1,0,1,1,0,0,1,0,1,1]
out['exceptional_blowups']=[dict(k=k,n=11*k,M=count([None]+[v for v in word for _ in range(k)]),target=((11*k)**2+5)//6) for k in range(1,25)]
out['attainment']=[dict(n=n,M=count(source(n)),target=(n*n+5)//6) for n in range(12,121)]
(L/'mechanisms.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='attainment'},indent=2))
