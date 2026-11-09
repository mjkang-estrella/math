import argparse,json,hashlib
from pathlib import Path
a=argparse.ArgumentParser();a.add_argument('name');a.add_argument('--start',type=int,default=0);a.add_argument('--end',type=int);x=a.parse_args()
r=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r207/packet')
m=json.loads((r.parent/'MANIFEST.json').read_text());assert x.name in m['files'];assert x.name!='private/history-selected/section-1.txt'
b=(r/x.name).read_bytes();end=len(b) if x.end is None else min(x.end,len(b))
print(x.name+' ['+str(x.start)+','+str(end)+')\n'+b[x.start:end].decode())
with Path('frontier/campaigns/2026-10-14/structural-r207-contribution-r1/packet/private/read-extents.jsonl').open('a') as z:z.write(json.dumps({'path':x.name,'start':x.start,'end':end,'sha256':hashlib.sha256(b).hexdigest(),'kind':'display-request; verify no truncation'})+'\n')
