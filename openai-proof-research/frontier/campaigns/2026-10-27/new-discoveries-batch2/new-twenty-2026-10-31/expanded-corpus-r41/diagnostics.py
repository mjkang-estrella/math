import pathlib,json,resource,os,time
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(75,75));os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2]);p=pathlib.Path(__file__).resolve().parent
out=[]
for j in range(3,181):
 # carry-free integer encoding of product (1+x^(2i+1)); coefficients at most 2^j
 bits=j+1; a=1
 for i in range(j):a+=a<<((2*i+1)*bits)
 mask=(1<<bits)-1;c=[(a>>(j*k*bits))&mask for k in range(1,j)]
 signs=[1 if b>a else -1 for a,b in zip(c,c[1:]) if a!=b];peaks=sum(s==1 and t==-1 for s,t in zip([1]+signs,signs+[-1]))
 out.append({'j':j,'coefficients':c,'plateau_peaks':peaks})
 if peaks>2: print('COUNTEREXAMPLE',out[-1],flush=True)
(p/'fraction-diagnostic.json').write_text(json.dumps(out,indent=2));print('completed',len(out),'max modes',max(x['plateau_peaks'] for x in out))
# path P_(d+1) independent subsets via elementary finite recurrence
counts=[]
for d in range(12):
 sets=[m for m in range(1<<(d+1)) if not(m&(m<<1))];sz=max(m.bit_count() for m in sets);counts.append({'n':2,'d':d,'alpha':sz,'max_sets':sum(m.bit_count()==sz for m in sets)})
(p/'path-diagnostic.json').write_text(json.dumps(counts,indent=2));print(counts)
