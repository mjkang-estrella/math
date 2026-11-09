from pathlib import Path
import hashlib,json,urllib.request,datetime
L=Path(__file__).resolve().parent
# Freeze one relevant classical switching primary body, without historical tree copies.
S=L.parent/'sol-seidel-switching-breadth-depth-r228/sources'
rows=[]
for name in ['1403.2155v3.pdf','1403.2155v3.txt']:
 p=S/name;b=p.read_bytes();h=hashlib.sha256(b).hexdigest();q=L/'primary'/name;q.write_bytes(b)
 assert hashlib.sha256(p.read_bytes()).hexdigest()==h==hashlib.sha256(q.read_bytes()).hexdigest()
 rows.append({'original':str(p),'copy':str(q.relative_to(L)),'sha256':h})
(L/'extra-freeze.json').write_text(json.dumps(rows,indent=2)+'\n')
# Distinct lawful publisher route for the 2019 paper; never bypass an access denial.
url='https://link.springer.com/article/10.1007/s10910-020-01193-4'
try:
 with urllib.request.urlopen(url,timeout=20) as r:b=r.read(2000000);status=r.status
 q=L/'primary/2019-publisher.html';q.write_bytes(b)
 row={'url':url,'status':status,'sha256':hashlib.sha256(b).hexdigest(),'copy':str(q.relative_to(L))}
except Exception as e:row={'url':url,'failure':repr(e),'retry':False}
row['utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
(L/'publisher-access.json').write_text(json.dumps(row,indent=2)+'\n')
print(json.dumps(row))
