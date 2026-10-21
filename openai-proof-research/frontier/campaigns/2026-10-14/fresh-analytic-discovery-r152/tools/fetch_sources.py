from pathlib import Path
import json,hashlib,urllib.request,concurrent.futures
root=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r152');pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
tree=json.loads(Path('sources/preprints-tree.json').read_bytes())['tree']
prefixes={'fluctuations':'preprints/Hard-sphere-fluctuations-on-the-regular-Boltzmann-lifespan-September-23-2026/build/','companion':'preprints/The-Boltzmann-Grad-limit-for-stable-radial-potentials-on-regular-kinetic-intervals-September-23-2026/build/'}
jobs=[]
for name,prefix in prefixes.items():
 for e in tree:
  if e['type']=='blob' and e['path'].startswith(prefix) and e['path'].endswith(('.tex','.bib')) and '/figures/' not in e['path']:jobs.append((name,prefix,e))
def run(job):
 name,prefix,e=job;url=f'https://raw.githubusercontent.com/openai/math/{pin}/'+e['path']
 b=urllib.request.urlopen(url,timeout=40).read();blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 assert len(b)==e['size'] and blob==e['sha'],e['path']
 dst=root/'private/source'/name/e['path'][len(prefix):];dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(b)
 return {'path':e['path'],'url':url,'local':str(dst.relative_to(root)),'bytes':len(b),'git_blob':blob,'sha256':hashlib.sha256(b).hexdigest()}
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:out=list(ex.map(run,jobs))
(root/'SOURCE-AUTH.json').write_text(json.dumps({'pin':pin,'tree_sha256':'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b','objects':out},indent=2)+'\n')
print('Authenticated objects',len(out),'bytes',sum(x['bytes'] for x in out))
