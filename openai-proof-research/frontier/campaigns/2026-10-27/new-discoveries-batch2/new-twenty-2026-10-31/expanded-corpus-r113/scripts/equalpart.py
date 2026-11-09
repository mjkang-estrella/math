import pathlib,re,math,json,time
D=pathlib.Path(__file__).resolve().parents[1];src=(D/'sources/partition-generatingfunctions.txt').read_text();hs={}
for line in src.splitlines():
 m=re.match(r'h_(\d+)\(t\) := (.*)',line)
 if not m:continue
 d=int(m[1]);cs={}
 for term in re.findall(r'[+-]?[^+-]+',m[2].replace(' ','')):
  if 't' not in term:c=int(term);e=0
  else:
   a,b=term.split('t');a=a.rstrip('*');c=-1 if a=='-' else 1 if a in ['', '+'] else int(a);e=int(b[1:]) if b else 1
  cs[e]=c
 hs[d]=cs
seen={};N=50000
for d in range(4,31):
 def p(n):return sum(c*math.comb(n+d-2-j,d-1) for j,c in hs[d].items() if n-1>=j)
 vals=[p(n) for n in range(1,d+1)];diff=[]
 while vals:diff.append(vals[0]);vals=[b-a for a,b in zip(vals,vals[1:])]
 collisions=[]
 for n in range(1,N+1):
  v=diff[0]
  if n>=2:
   if v in seen and seen[v][0]!=d:collisions.append([seen[v],[d,n],v])
   seen[v]=(d,n)
  for j in range(d-1):diff[j]+=diff[j+1]
 print(json.dumps({'d':d,'n_min':2,'n_max':N,'last_value':v,'collisions':collisions}),flush=True)
print('sanity p30(666)',sum(c*math.comb(666+30-2-j,29) for j,c in hs[30].items()))
