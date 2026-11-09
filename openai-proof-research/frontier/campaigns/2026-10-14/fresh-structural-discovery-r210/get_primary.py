from pathlib import Path
from urllib.request import urlopen,Request
from concurrent.futures import ThreadPoolExecutor
import json,hashlib,subprocess
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r210')
items=[('ny2002','https://arxiv.org/pdf/math/0208127v1'),('ny2008','https://sites.math.washington.edu/~yuan/papers/2008CVPDE.pdf'),('khuri2007','https://www.math.stonybrook.edu/~khuri/Khuri_Comm_PDE.pdf'),('khuri2009','https://www.math.stonybrook.edu/~khuri/Khuri_AIMS_Darboux.pdf'),('nakamura_maeda1989','https://www.ams.org/tran/1989-313-01/S0002-9947-1989-0992597-8/S0002-9947-1989-0992597-8.pdf'),('lin1985','https://projecteuclid.org/journals/journal-of-differential-geometry/volume-21/issue-2/The-local-isometric-embedding-in-R3-of-2-dimensional-Riemannian/10.4310/jdg/1214439563.pdf')]
def get(item):
 name,url=item; record={'id':name,'url':url}
 try:
  with urlopen(Request(url,headers={'User-Agent':'Mozilla/5.0'}),timeout=40) as f:b=f.read();record['resolved_url']=f.url
  record.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
  if not b.startswith(b'%PDF'):raise ValueError('Endpoint response is not PDF')
  p=R/'private/primary'/name;p.parent.mkdir(parents=True,exist_ok=True);p.with_suffix('.pdf').write_bytes(b)
  s=subprocess.run(['pdftotext','-layout',str(p.with_suffix('.pdf')),str(p.with_suffix('.txt'))],capture_output=True,text=True,check=False)
  record.update(extract_returncode=s.returncode,extract_stderr=s.stderr)
 except Exception as e: record['failure']=repr(e)
 return record
with ThreadPoolExecutor(max_workers=4) as ex: records=list(ex.map(get,items))
(R/'private/primary-access.json').write_text(json.dumps(records,indent=2)+'\n');print(json.dumps(records,indent=2))
p='lean/ComparatorChallenges/IsometricImmersion.lean';pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb';url='https://api.github.com/repos/openai/math/contents/'+p+'?ref='+pin
try:
 meta=json.loads(urlopen(Request(url,headers={'User-Agent':'Research-source-reader'}),timeout=40).read());b=urlopen('https://raw.githubusercontent.com/openai/math/'+pin+'/'+p,timeout=40).read()
 sha=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert sha==meta['sha']
 (R/'private/IsometricImmersion.lean').write_bytes(b)
 (R/'private/comparator-authentication.json').write_text(json.dumps({'path':p,'metadata_url':url,'git_blob':sha,'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)},indent=2)+'\n')
 print('\nCOMPLETE COMPARATOR\n'+b.decode())
except Exception as e:print('Comparator access failure',repr(e))
