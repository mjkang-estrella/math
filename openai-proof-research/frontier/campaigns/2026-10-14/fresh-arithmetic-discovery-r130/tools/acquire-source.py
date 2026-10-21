from pathlib import Path
import json, hashlib, urllib.request, concurrent.futures
R=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r130')
sel=json.loads((R/'private/navigation/source017-tree-selection.json').read_text())
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
def get(e):
    u='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+e['path']
    b=urllib.request.urlopen(u,timeout=45).read()
    blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
    assert len(b)==e['size'] and blob==e['sha'],e['path']
    p=R/'private/source'/e['path'].split('/build/')[1];p.parent.mkdir(exist_ok=True,parents=True);p.write_bytes(b)
    return {'canonical_path':e['path'],'url':u,'size':len(b),'git_blob':blob,'sha256':hashlib.sha256(b).hexdigest(),'copy':str(p.relative_to(R))}
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
    records=list(pool.map(get,[e for e in sel if e['type']=='blob' and (e['path'].endswith('.tex') or e['path'].endswith('.bib'))]))
(R/'private/source/authentication.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps(records,indent=2))
