from pathlib import Path
import json,urllib.request,hashlib,re
root=Path(__file__).resolve().parents[1]; repo=root.parents[3]
tree=json.loads((repo/'sources/preprints-tree.json').read_text());assert len(tree['tree'])==13223 and tree['truncated'] is False
terms=['Foulkes','Donovan','singular-normal-affine','stable-coordinate','high-arity','klt-complements','Uniform-Cartier','Anticanonical','anticanonical','periodic-group','residually-finite-2']
selected=[x for x in tree['tree'] if x['type']=='blob' and x['path'].endswith('.tex') and any(t in x['path'] for t in terms) and '/source/' not in x['path']]
print('SELECTED',len(selected))
records=[]
for x in selected:
 if '/sections/' in x['path'] or x['path'].count('/')==2:
  url='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+x['path'];dest=root/'packet/private/upstream'/x['path'].removeprefix('preprints/')
  try:
   data=urllib.request.urlopen(url,timeout=40).read();h=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest();assert h==x['sha'];dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
   records.append({'canonical':x,'url':url,'sha256':hashlib.sha256(data).hexdigest(),'local':str(dest.relative_to(root/'packet'))});print(x['path'],len(data))
  except Exception as e: records.append({'canonical':x,'url':url,'error':repr(e)}); print('FAIL',repr(e))
(root/'packet/private/acquisition.json').write_text(json.dumps(records,indent=2)+'\n')
