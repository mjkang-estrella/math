"""Acquisition only: version-pinned primary HTML, no PDF extraction."""
from pathlib import Path
import urllib.request,json,re,hashlib,datetime,runpy
S=Path('frontier/sources/i129_disordered_fk_occupation'); E=S/'external';E.mkdir(exist_ok=True)
conv=runpy.run_path('frontier/experiments/i114_quantum_information_discovery/html_text.py')['convert']
log=[]
for aid in ['0809.3985','2509.08938','1804.07286']:
 for kind in ['abs','html']:
  url='https://arxiv.org/'+kind+'/'+(aid if kind=='abs' else version)
  try:
   with urllib.request.urlopen(url,timeout=45) as response:b=response.read();status=response.status;headers=dict(response.headers)
   name=aid+'-abs' if kind=='abs' else version
   p=E/(name+'.html');p.write_bytes(b);p.with_suffix('.txt').write_text(conv(b.decode(errors='replace')))
   if kind=='abs':
    vs=re.findall(re.escape(aid)+r'v(\d+)',b.decode());version=aid+'v'+str(max(map(int,vs)))
   log.append(dict(url=url,status=status,local=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),headers=headers,utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))
   print(url,status,len(b),flush=True)
  except Exception as e:log.append(dict(url=url,error=repr(e)));print(url,repr(e),flush=True)
(S/'http-log.json').write_text(json.dumps(log,indent=2)+'\n')
