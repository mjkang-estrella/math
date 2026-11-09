from pathlib import Path
import sys,json,hashlib,datetime
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r220')
for arg in sys.argv[1:]:
 name,start,end=arg.rsplit(':',2); p=R/name; b=p.read_bytes();lines=b.splitlines(keepends=True);a=int(start);z=int(end);assert 1<=a<=z<=len(lines)
 lo=sum(map(len,lines[:a-1])); hi=sum(map(len,lines[:z]));selection=b[lo:hi];assert selection==b''.join(lines[a-1:z])
 print('\nSELECTED',name,'lines',a,z,'bytes',lo,hi,'sha256',hashlib.sha256(selection).hexdigest())
 print(selection.decode())
 with (R/'private/reads.jsonl').open('a') as f:f.write(json.dumps(dict(path=name,lines=[a,z],bytes=[lo,hi],sha256=hashlib.sha256(selection).hexdigest(),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))+'\n')
