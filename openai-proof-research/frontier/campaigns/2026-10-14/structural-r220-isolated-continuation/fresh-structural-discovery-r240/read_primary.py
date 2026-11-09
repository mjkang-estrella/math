from pathlib import Path
import sys,json,hashlib,re
R=Path('frontier/campaigns/2026-10-14/structural-r220-isolated-continuation/fresh-structural-discovery-r240')
for arg in sys.argv[1:]:
 name,a,z=arg.split(':');a=int(a);z=int(z);p=R/'private/primary'/(name+'.txt');b=p.read_bytes();ls=b.splitlines(keepends=True);assert 1<=a<=z<=len(ls)
 omitted=[];lo=sum(map(len,ls[:a-1]));hi=sum(map(len,ls[:z]));print('READ',name,'lines',a,z,'bytes',lo,hi)
 for i in range(a-1,z):
  s=ls[i].decode();t=s.strip().replace('\x0c','').strip()
  furniture=bool(re.fullmatch(r'\d{1,2}',t) or re.fullmatch(r'\d*\s*RAVIL GABDURAKHMANOV AND GERASIM KOKAREV\s*\d*',t) or re.fullmatch(r"ON CALDERO.N.S PROBLEM FOR THE CONNECTION LAPLACIAN\s*\d*",t))
  explicit=(name=='GK' and i+1 in [82,83,84,85]) or (name=='Rondi' and 1301<=i+1<=1305)
  furniture = furniture or (name=="GK" and "CONNECTION LAPLACIAN" in t and "CALDER" in t)
  if furniture or explicit:omitted.append(i+1)
  else:print(s,end='')
 with (R/'private/primary-reads.jsonl').open('a') as f:f.write(json.dumps({'id':name,'start_line':a,'end_line':z,'start_byte':lo,'end_byte':hi,'masked_furniture':omitted,'sha256':hashlib.sha256(b).hexdigest()})+'\n')
