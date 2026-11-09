from pathlib import Path
import json,hashlib,urllib.request,concurrent.futures,os
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research');R=P/'frontier/campaigns/2026-10-14/structural-r218-contribution-r1';A=P/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r218'
b=(P/'sources/preprints-tree.json').read_bytes();assert len(b)==4858136 and hashlib.sha256(b).hexdigest()=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
t=json.loads(b);es=t['tree'];assert len(es)==13223
pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb';families=['Taming-implies-compatibility-on-four-manifolds-October-6-2026','Taming-implies-compatibility-on-four-manifolds-September-23-2026']
selected=[e for e in es if any(e['path'].startswith(f+'/') or e['path'].startswith('preprints/'+f+'/') for f in families) and e['type']=='blob'];assert len(selected)==25
out=R/'private/independent';out.mkdir(mode=0o700,exist_ok=True)
def fetch(e):
 path=e['path'];path=path if path.startswith('preprints/') else 'preprints/'+path
 url='https://raw.githubusercontent.com/openai/math/'+pin+'/'+path
 with urllib.request.urlopen(url,timeout=40) as z:b=z.read()
 blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert blob==e['sha'],path
 dst=out/path;dst.parent.mkdir(mode=0o700,parents=True,exist_ok=True);dst.write_bytes(b);dst.chmod(0o400)
 ap=A/'private/canonical'/path;assert b==ap.read_bytes(),path
 return {'path':path,'url':url,'bytes':len(b),'git_blob':blob,'sha256':hashlib.sha256(b).hexdigest(),'author_equal':True}
with concurrent.futures.ThreadPoolExecutor(max_workers=5) as ex:results=list(ex.map(fetch,selected))
(R/'private/independent-authentication.json').write_text(json.dumps(results,indent=2)+'\n')
print('Independently downloaded and pinned-tree authenticated all',len(results),'Source342 blobs; actual bytes equal to admitted author originals.')
for family in families:
 base=out/'preprints'/family/'build'
 for name in ['main.tex','preamble.tex']:
  print(family,name);print((base/name).read_text())
