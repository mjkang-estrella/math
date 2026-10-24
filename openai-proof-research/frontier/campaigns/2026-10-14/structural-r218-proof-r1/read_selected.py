import sys,json,hashlib,re
from pathlib import Path
ROOT=Path(__file__).resolve().parent
PROJECT=Path.cwd()
AUTHOR=PROJECT/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r218'
MANIFEST_SHA='43459b97cf417a8ad9356615ec82ff34b1be390d9af635cc2e331e3be340f058'
b=(AUTHOR/'MANIFEST.json').read_bytes();assert hashlib.sha256(b).hexdigest()==MANIFEST_SHA
M=json.loads(b)
def data(path):
 p=Path(path)
 if p.is_absolute():p=p.relative_to(AUTHOR)
 assert str(p) in M['files'] or str(p) in ['MANIFEST.json','REPORT.md','ANCHORS.json']
 b=(AUTHOR/p).read_bytes()
 if str(p) in M['files']:assert hashlib.sha256(b).hexdigest()==M['files'][str(p)]['sha256']
 lines=b.splitlines(keepends=True); offsets=[0]
 for line in lines:offsets.append(offsets[-1]+len(line))
 return b,lines,offsets
if __name__=='__main__':
 f=sys.argv[1];b,ll,oo=data(f)
 if len(sys.argv)==2 or sys.argv[2]=='classify':
  print('BOUNDARIES',f,'bytes',len(b),'lines',len(ll))
  for i,l in enumerate(ll,1):
   t=l.decode().strip()
   if re.search(r'^#{1,6} |^\\(?:sub)*section|^\\(?:begin|end)\{(?:document|abstract)\}|^\s*(?:[0-9]+\.)*\s*[0-9]+\.?\s+[A-Z]|acknowledg|aknowledg|acknowleg|licen[sc]|publisher|private communication|personal communication|discussions? with|thank|received|downloaded',t,re.I):print(f'{i} [{oo[i-1]},{oo[i]}) {t}')
 else:
  ranges=[tuple(map(int,s.split(':'))) for s in sys.argv[2:]]
  rec=[]
  for start,end in ranges:
   assert 1<=start<=end<=len(ll)
   print(f'READ {f} L{start}-{end} bytes [{oo[start-1]},{oo[end]})')
   for i in range(start-1,end):print(f'{i+1:4d} '+ll[i].decode(),end='')
   rec.append({'path':f,'lines_inclusive':[start,end],'bytes_half_open':[oo[start-1],oo[end]],'sha256':hashlib.sha256(b).hexdigest()})
  with (ROOT/'private/read-selections.jsonl').open('a') as h:
   for x in rec:h.write(json.dumps(x)+'\n')
