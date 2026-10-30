from checks import cover,verify
from itertools import combinations
from pathlib import Path
import json,sys
L=Path(__file__).resolve().parent
out=[];total=0;mode=sys.argv[1] if len(sys.argv)>1 else 'corrected'
for t in (range(16,33,2) if mode=='initial' else range(16,49,2)):
 for n in range(t+3,2*t+2):
  if not(n%4 in (1,2) or (t%4==2 and n%4==3)):continue
  s=n-t;r=((3 if n%2 else 4) if mode=='initial' else ((3 if (n-t)%4==3 else 5) if n%2 else 4));found=None;attempts=[]
  if s<r:continue
  for mid in combinations(range(2,min(s,9)),r-2):
   starts=(1,)+mid+(s,);c,z=cover(n,t,starts);total+=z;attempts.append([starts,z])
   if c is not None:found=dict(starts=starts,cycle=c);break
  out.append(dict(t=t,n=n,found=found,attempts=attempts))
(L/('explore-'+mode+'.json')).write_text(json.dumps(dict(records=out,states=total),indent=2)+'\n')
print('records',len(out),'states',total,'failed',[(x['t'],x['n']) for x in out if x['found'] is None])
