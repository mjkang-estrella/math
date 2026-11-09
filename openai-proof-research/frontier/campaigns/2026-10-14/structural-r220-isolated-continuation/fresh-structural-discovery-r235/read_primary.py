from pathlib import Path
import sys,json,hashlib,re
R=Path('frontier/campaigns/2026-10-14/structural-r220-isolated-continuation/fresh-structural-discovery-r235')
for arg in sys.argv[1:]:
 name,first,last=arg.split(':');p=R/'private/primary'/f'{name}.txt';b=p.read_bytes();lines=b.splitlines(keepends=True);lo=int(first)-1;hi=int(last);assert 0<=lo<hi<=len(lines)
 s=sum(map(len,lines[:lo]));e=sum(map(len,lines[:hi]));off=s;spans=[]
 print(f'PRIMARY {name} lines[{lo+1},{hi}] bytes[{s},{e})')
 for i,l in enumerate(lines[lo:hi],lo+1):
  t=l.decode();mask=bool(re.search(r'This is a free offprint|License or copyright|^\s*INVARIANT METRICS ON|^\s*DAMIN WU AND SHING|^\s*\d+\s+E\. CALABI|^\s*4.e S[ÉEéEe]RIE|^\s*ANNALES SCIENTIFIQUES|^\s*\d+\s+H\. SESHADRI',t))
  if mask:print(f'[MASKED running furniture line {i}]')
  else:print(t,end='')
  spans.append({'start':off,'end':off+len(l),'displayed':not mask});off+=len(l)
 print()
 with (R/'private/primary-read-extents.jsonl').open('a') as f:f.write(json.dumps({'name':name,'lines':[lo+1,hi],'bytes':[s,e],'sha256':hashlib.sha256(b[s:e]).hexdigest(),'spans':spans,'parser':'bytes.splitlines(keepends=True)'})+'\n')
