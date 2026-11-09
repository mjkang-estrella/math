# Independent exhaustive oracle: no CNF or encoder imports.
import sys,pathlib,itertools,json,time
D=pathlib.Path(sys.argv[1]);b=int(sys.argv[2]);start=time.monotonic();best=-1;witness=None;cases=0
for B in itertools.combinations(range(32),b):
 S=set(B);st=sum((x+y)%32 in S for x in B for y in B);cases+=1
 if st>best:best=st;witness=B
M=32-b;minimum=1024-96*b+3*b*b-best
# Independently count the attaining large set, rather than trust the formula alone.
A=set(range(32))-set(witness);assert sum((x+y)%32 in A for x in A for y in A)==minimum
r=dict(M=M,complement_size=b,subsets=cases,max_ST_complement=best,min_ST=minimum,complement_witness=witness,seconds=time.monotonic()-start)
(D/'outputs'/f'cube-exhaustive-{M}.json').write_text(json.dumps(r,indent=2));print(r)
