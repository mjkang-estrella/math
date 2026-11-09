from pathlib import Path
import json,sys,hashlib
r=Path(__file__).parent
mp=json.loads((r/'aliases.json').read_text())
for arg in sys.argv[1:]:
 parts=arg.split(':');key=parts[0];p=r/'private'/mp[key];b=p.read_bytes();ls=b.splitlines(keepends=True)
 a=int(parts[1])-1 if len(parts)>1 else 0;z=int(parts[2]) if len(parts)>2 else len(ls)
 assert 0<=a<z<=len(ls)
 start=sum(map(len,ls[:a]));end=start+sum(map(len,ls[a:z]));out=b[start:end];assert out==b''.join(ls[a:z])
 print('\nEXACT SEMANTIC SELECTION',key,'lines',a+1,z,'bytes',start,end,'of',len(b),'\n');print(out.decode())
 with (r/'reads.jsonl').open('a') as f:f.write(json.dumps({'key':key,'path':mp[key],'lines':[a+1,z],'bytes':[start,end],'sha256':hashlib.sha256(out).hexdigest(),'kind':'displayed canonical semantic selection; wrappers explicitly not mathematical coverage'})+'\n')
