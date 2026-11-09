from pathlib import Path
import re,sys,json,hashlib
R=Path('frontier/campaigns/2026-10-14/structural-r220-isolated-continuation/fresh-structural-discovery-r226')
for arg in sys.argv[1:]:
 name,a,z=arg.split(':');a,z=int(a),int(z);p=R/'private/primary'/(name+'.txt');b=p.read_bytes();off=0;chunks=[];omissions=[];endpoints={0};rows=[]
 for l in b.splitlines(keepends=True):
  st=off;off+=len(l);endpoints.add(off);rows.append((st,off,l))
 assert a in endpoints and z in endpoints
 for st,en,l in rows:
  if st<a or en>z:continue
  s=l.decode().strip()
  if re.search(r'^(?:[0-9]+\s+)?(?:(?:[0-9]+\s+)?Y\. MUTO|Riemannian\s+submersions\s+and|NILS DENCKER|N\. DENCKER|DENCKER,|HEZARI|GUILLAUME ROY-FORTIN|ALBERTO ENCISO AND DANIEL PERALTA-SALAS|NODAL SETS AND GROWTH|EIGENFUNCTIONS WITH PRESCRIBED|UPPER BOUNDS ON|PSEUDOSPECTRA OF SEMI)',s) and len(s)<150:
   omissions.append([st,en,'classified running header']);continue
  chunks.append(l)
 print('\nPRIMARY EXACT SELECTION',name,a,z,'OMITTED HEADERS',omissions);print(b''.join(chunks).decode())
 with (R/'PRIMARY-READS.jsonl').open('a') as f:f.write(json.dumps({'name':name,'start':a,'end':z,'sha256':hashlib.sha256(b[a:z]).hexdigest(),'omissions':omissions,'parser':'bytes.splitlines(keepends=True)','timing':'prefreeze; strongest comparison before extended derivation'})+'\n')
