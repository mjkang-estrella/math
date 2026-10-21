from pathlib import Path
import urllib.request,json,hashlib,concurrent.futures
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r157')
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
PREFIX='preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/'
tree=json.loads(Path('sources/preprints-tree.json').read_text())['tree']
# Narrow selected canonical-source exception; no project history traversal.
entries=[e for e in tree if e['path'].startswith(PREFIX) and e['type']=='blob' and not e['path'].endswith('.pdf')]
(R/'private/source168').mkdir()
def fetch(e):
 url='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+e['path']
 b=urllib.request.urlopen(url,timeout=35).read()
 sha=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 assert sha==e['sha'] and len(b)==e['size']
 dest=R/'private/source168'/e['path'][len(PREFIX):];dest.parent.mkdir(exist_ok=True,parents=True);dest.write_bytes(b)
 return {'canonical_path':e['path'],'url':url,'size':len(b),'git_blob_sha1':sha,'sha256':hashlib.sha256(b).hexdigest(),'selected_path':str(dest.relative_to(R))}
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex: out=list(ex.map(fetch,entries))
(R/'private/source168-identities.json').write_text(json.dumps(out,indent=2)+'\n')
print('Authenticated',len(out),'canonical text blobs',sum(x['size'] for x in out),'bytes')
