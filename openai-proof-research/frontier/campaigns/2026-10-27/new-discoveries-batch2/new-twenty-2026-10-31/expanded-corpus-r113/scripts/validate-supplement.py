import pathlib,re,math,json
D=pathlib.Path(__file__).resolve().parents[1];src=(D/'sources/partition-generatingfunctions.txt').read_text();hs={}
for line in src.splitlines():
 m=re.match(r'h_(\d+)\(t\) := (.*)',line)
 if m:
  cs={}
  for term in re.findall(r'[+-]?[^+-]+',m[2].replace(' ','')):
   if 't' not in term:c=int(term);e=0
   else:
    a,b=term.split('t');a=a.rstrip('*');c=-1 if a=='-' else 1 if a in ['', '+'] else int(a);e=int(b[1:]) if b else 1
   cs[e]=c
  hs[int(m[1])]=cs
for dim in [2,3]:
 p=[0]*31;p[0]=1
 for j in range(1,31):
  for z in range(1 if dim==2 else j):
   for d in range(j,31):p[d]+=p[d-j]
 bad=[]
 for d in range(1,31):
  val=sum(c*math.comb(dim+d-2-j,d-1) for j,c in hs[d].items() if dim-1>=j)
  if val!=p[d]:bad.append([d,val,p[d]])
 print(json.dumps({'dim':dim,'sizes':'1..30','comparison':'Euler ordinary partition product' if dim==2 else 'MacMahon plane-partition product','mismatches':bad}),flush=True)
actual=sum(c*math.comb(666+30-2-j,29) for j,c in hs[30].items());printed=5390806817913544023450455014935417834529246670018145780
print(json.dumps({'supplement_p30_666':actual,'printed_p30_666':printed,'difference':actual-printed}))
