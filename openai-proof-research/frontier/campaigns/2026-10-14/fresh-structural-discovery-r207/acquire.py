from pathlib import Path
import json,hashlib,urllib.request,concurrent.futures,time,os
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r207'); S=json.loads((R/'private/selection.json').read_text()); PIN=S['pin']
os.umask(0o077)
def one(e):
 p=e['path']; u='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+p; dest=R/'private/canonical'/p
 dest.parent.mkdir(parents=True,exist_ok=True)
 if dest.exists(): b=dest.read_bytes()
 else:
  with urllib.request.urlopen(u,timeout=45) as f:b=f.read()
  dest.write_bytes(b)
 sha=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 assert sha==e['sha'] and len(b)==e['size'],p
 return {'path':p,'url':u,'bytes':len(b),'git_blob':sha,'sha256':hashlib.sha256(b).hexdigest(),'authenticated':True}
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as ex:
 receipts=list(ex.map(one,[e for e in S['entries'] if e['type']=='blob']))
(R/'private/authentication.json').write_text(json.dumps(receipts,indent=2)+'\n')
url='https://raw.githubusercontent.com/openai/math/'+PIN+'/lean/docs/331.md'
with urllib.request.urlopen(url,timeout=45) as f:b=f.read()
(R/'private/lean-331.md').write_bytes(b)
print('Authenticated',len(receipts),'blobs;',sum(x['bytes'] for x in receipts),'bytes')
print('Lean navigation URL',url,'SHA256',hashlib.sha256(b).hexdigest())
print(b.decode())
