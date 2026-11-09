import argparse,json,hashlib
from pathlib import Path
a=argparse.ArgumentParser();a.add_argument('family',type=int);a.add_argument('names',nargs='+');a.add_argument('--start',type=int,default=0);a.add_argument('--end',type=int);x=a.parse_args()
r=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r207/packet')
m=json.loads((r.parent/'MANIFEST.json').read_text())
s=json.loads((r/'private/selection.json').read_text());f=s['folders'][x.family-1]+'-September-27-2026'
log=Path('frontier/campaigns/2026-10-14/structural-r207-contribution-r1/packet/private/read-extents.jsonl')
for name in x.names:
 p='private/canonical/preprints/'+f+'/build/'+name
 assert p in m['files'];b=(r/p).read_bytes();end=len(b) if x.end is None else min(x.end,len(b))
 print('\n===== C'+str(x.family)+' '+name+' ['+str(x.start)+','+str(end)+') =====\n'+b[x.start:end].decode())
 with log.open('a') as z:z.write(json.dumps({'path':p,'start':x.start,'end':end,'sha256':hashlib.sha256(b).hexdigest(),'kind':'display-request; verify no tool truncation'})+'\n')
