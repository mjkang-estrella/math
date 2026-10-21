from pathlib import Path
import json,urllib.request,hashlib
R=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r145'); pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
prefix='preprints/A-counterexample-to-the-Monge-ansatz-for-the-three-marginal-Coulomb-cost-September-25-2026/'
rows=[]
for t in json.loads(Path('sources/preprints-tree.json').read_text())['tree']:
 if t['path'].startswith(prefix) and t['type']=='blob' and not t['path'].endswith('.pdf'):
  url='https://raw.githubusercontent.com/openai/math/'+pin+'/'+t['path']; b=urllib.request.urlopen(url,timeout=45).read(); git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest(); assert len(b)==t['size'] and git==t['sha']
  dest=R/'private/source'/t['path'][len(prefix):];dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
  rows.append({'path':t['path'],'url':url,'size':len(b),'git_blob':git,'sha256':hashlib.sha256(b).hexdigest(),'selected_copy':str(dest.relative_to(R))})
(R/'SOURCE-AUTH.json').write_text(json.dumps(rows,indent=2)+'\n'); print('Authenticated',len(rows),'canonical blobs')
