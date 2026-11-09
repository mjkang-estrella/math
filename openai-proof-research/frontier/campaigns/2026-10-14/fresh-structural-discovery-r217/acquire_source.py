from pathlib import Path
import json, hashlib, urllib.request, concurrent.futures
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r217')
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
entries=json.loads((R/'private/source-tree-selection.json').read_text())
blobs=[x for x in entries if x['type']=='blob'];assert len(entries)==42 and len(blobs)==34

def fetch(x):
    url='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+x['path']
    req=urllib.request.Request(url,headers={'User-Agent':'r217-local-research'})
    with urllib.request.urlopen(req,timeout=45) as r:b=r.read()
    git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
    assert len(b)==x['size'] and git==x['sha'],x['path']
    p=R/'private'/x['path'];p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
    return {'path':x['path'],'url':url,'bytes':len(b),'git_blob':git,'sha256':hashlib.sha256(b).hexdigest()}
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as pool:records=list(pool.map(fetch,blobs))
(R/'private/source-authentication.json').write_text(json.dumps(records,indent=2)+'\n')
O='preprints/Deforming-hypersymplectic-four-manifolds-to-hyperkahler-triples-October-7-2026/'
S=O.replace('October-7','September-23')
comparisons=[]
for x in blobs:
    if x['path'].startswith(O):
        suffix=x['path'][len(O):];a=(R/'private'/x['path']).read_bytes();b=(R/'private'/S/suffix).read_bytes()
        comparisons.append({'suffix':suffix,'actual_byte_equal':a==b,'october_bytes':len(a),'september_bytes':len(b)})
assert sum(x['actual_byte_equal'] for x in comparisons)==12
(R/'private/version-equality.json').write_text(json.dumps(comparisons,indent=2)+'\n')
print('Authenticated 34/34 blobs against complete pinned tree; actual byte equality:',json.dumps(comparisons))
url='https://api.github.com/repos/openai/math/contents/lean/docs/341.md?ref='+PIN
with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'r217-local-research'}),timeout=45) as r:meta=json.load(r)
record=fetch({'path':'lean/docs/341.md','size':meta['size'],'sha':meta['sha']})
(R/'private/lean-authentication.json').write_text(json.dumps({'api_url':url,'record':record},indent=2)+'\n')
print('lean doc authenticated',record)
