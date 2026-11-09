from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent;S=L.parent/'pi-mathdb-primary-qualified-breadth-r335/sources'
refs=[]
for name in ['provenance.json','fetch-utc.txt','384757/aimpl-polypartition-p2.html']:
 p=S/name;b=p.read_bytes();refs.append(dict(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest()))
assert refs[-1]['sha256']=='b9744a5a7b2d6a67a8253ee484dab5abc80be47ff2f0f8330852c58a2198c766'
(L/'primary-bindings.json').write_text(json.dumps({'frozen_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':'http://aimpl.org/polypartition/2/','version':'r335 cached body; fetch time in bound fetch-utc.txt; not live clearance','references':refs},indent=2)+'\n')
(L/'primary/polypartition2.html').write_bytes((S/'384757/aimpl-polypartition-p2.html').read_bytes())
