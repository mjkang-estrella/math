from pathlib import Path
import sys,json,hashlib,datetime
R=Path(__file__).parent
for spec in sys.argv[1:]:
 n,a,z=spec.split(':');a=int(a);z=int(z);b=(R/'private/primary'/(n+'.txt')).read_bytes()
 limits={0,len(b)};p=0
 for l in b.splitlines(keepends=True):p+=len(l);limits.add(p)
 assert a in limits and z in limits
 print('\nPRIMARY SEMANTIC READ',n,f'[{a},{z})');print(b[a:z].decode())
 with (R/'primary-reads-private.jsonl').open('a') as f:f.write(json.dumps({'id':n,'start':a,'end':z,'sha256':hashlib.sha256(b[a:z]).hexdigest(),'parser':'bytes.splitlines(keepends=True)','time':datetime.datetime.now(datetime.timezone.utc).isoformat()})+'\n')
