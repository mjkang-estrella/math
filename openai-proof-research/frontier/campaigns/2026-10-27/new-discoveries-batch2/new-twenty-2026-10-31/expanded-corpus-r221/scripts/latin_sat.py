import pathlib,json,itertools,sys
D=pathlib.Path(__file__).resolve().parents[1];parts=list(map(int,sys.argv[1].split(',')));key='-'.join(map(str,parts));n=sum(parts)
def v(i,j,k):return 1+(i*n+j)*n+k
clauses=[]
def exactly(xs):
 clauses.append(xs)
 clauses.extend([-a,-b] for a,b in itertools.combinations(xs,2))
for i in range(n):
 for j in range(n):exactly([v(i,j,k) for k in range(n)])
for i in range(n):
 for k in range(n):exactly([v(i,j,k) for j in range(n)])
for j in range(n):
 for k in range(n):exactly([v(i,j,k) for i in range(n)])
off=0
for h in parts:
 for i in range(off,off+h):
  for j in range(off,off+h):
   for k in range(n):
    if not off<=k<off+h:clauses.append([-v(i,j,k)])
 off+=h
p=D/f'outputs/latin-{key}.cnf';assert not p.exists()
with p.open('w') as f:
 f.write(f'p cnf {n**3} {len(clauses)}\n')
 for c in clauses:f.write(' '.join(map(str,c))+' 0\n')
print(json.dumps({'parts':parts,'order':n,'variables':n**3,'clauses':len(clauses),'path':str(p)}))
