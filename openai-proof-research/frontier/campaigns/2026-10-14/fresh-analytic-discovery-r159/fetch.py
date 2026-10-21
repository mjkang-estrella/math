from pathlib import Path
import json,urllib.request,hashlib,concurrent.futures
r=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r159/private/source');items=json.loads((r/'tree-selection.json').read_text())
names={
'Pointwise-Multiple-Ergodic-Averages-for-Mixing-Transformations-October-4-2026':'multiple',
'Pointwise-convergence-of-fourfold-ergodic-averages-for-mixing-transformations-October-4-2026':'fourfold',
'Triple-ergodic-averages-with-distinct-integer-slopes-October-4-2026':'slopes',
'Pointwise-convergence-of-triple-ergodic-averages-for-mixing-transformations-October-4-2026':'triple'}
def fetch(x):
 url='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+x['path'];b=urllib.request.urlopen(url,timeout=40).read()
 blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 assert len(b)==x['size'] and blob==x['sha'],x['path']
 parts=Path(x['path']).parts;local=r/names[parts[1]]/Path(*parts[3:]);local.parent.mkdir(parents=True,exist_ok=True);local.write_bytes(b)
 return dict(canonical=x['path'],url=url,bytes=len(b),git_blob=blob,sha256=hashlib.sha256(b).hexdigest(),local=str(local),lines=len(b.splitlines()))
sel=[x for x in items if x['type']=='blob' and x['path'].endswith(('.tex','.bib')) and '/figures/' not in x['path']]
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:out=list(ex.map(fetch,sel))
(r/'authentication.json').write_text(json.dumps(out,indent=2))
for x in out:print(Path(x['local']).relative_to(r),x['bytes'],x['lines'])
