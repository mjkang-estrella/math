from pathlib import Path
import json,sys,hashlib,datetime
R=Path(__file__).parent;D=R/'private/primary';c=json.loads((D/'selected-boundaries.json').read_text())
for name in sys.argv[1:]:
 b=(D/(name+'.txt')).read_bytes();ls=b.splitlines(keepends=True);offs=[0]
 for l in ls:offs.append(offs[-1]+len(l))
 for lo,hi in c['selections'][name]:
  masks=c['masks'][name];assert all(v!='EDITORIAL_CANDIDATE_NEEDS_RESOLUTION' for v in masks.values())
  print('\nPRIMARY',name,'lines',lo,hi,'bytes',offs[lo-1],offs[hi])
  ranges=[]
  for i in range(lo,hi+1):
   if str(i) in masks:continue
   print(ls[i-1].decode(),end='');ranges.append([offs[i-1],offs[i]])
  with (D/'semantic-reads.jsonl').open('a') as f:f.write(json.dumps({'id':name,'first_line':lo,'last_line':hi,'start':offs[lo-1],'end':offs[hi],'masks':masks,'read_ranges':ranges,'sha256':hashlib.sha256(b[offs[lo-1]:offs[hi]]).hexdigest(),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'parser':'bytes.splitlines(keepends=True)'})+'\n')
