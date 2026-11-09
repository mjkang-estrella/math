from pathlib import Path
import sys,json,hashlib
r=Path(__file__).parent
for arg in sys.argv[1:]:
 rel,a,z=arg.rsplit(':',2);p=r/'private/primary'/rel;b=p.read_bytes();ls=b.splitlines(keepends=True);a=int(a)-1;z=int(z);assert 0<=a<z<=len(ls)
 start=sum(map(len,ls[:a]));end=sum(map(len,ls[:z]));x=b[start:end]
 print('\nPRIMARY EXACT SELECTION',rel,'lines',a+1,z,'bytes',start,end,'\n');print(x.decode())
 with (r/'primary-reads.jsonl').open('a') as f:f.write(json.dumps({'path':rel,'lines':[a+1,z],'bytes':[start,end],'sha256':hashlib.sha256(x).hexdigest()})+'\n')
