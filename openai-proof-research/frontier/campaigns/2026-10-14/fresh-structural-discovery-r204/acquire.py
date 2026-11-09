from pathlib import Path
from urllib.request import urlopen,Request
from concurrent.futures import ThreadPoolExecutor
import json,hashlib,datetime
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r204')
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
PREFIX='preprints/Fixed-Points-of-Nonexpansive-Maps-in-Reflexive-Banach-Spaces-September-24-2026/'
def get(url):
    with urlopen(Request(url,headers={'User-Agent':'local-mathematical-research'}),timeout=40) as h:return h.read()
def fetch(e):
    url='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+e['path']
    b=get(url); g=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
    assert len(b)==e['size'] and g==e['sha'],e['path']
    dst=R/'private/canonical'/e['path'][len(PREFIX):]; dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(b)
    return dict(e,url_raw=url,sha256=hashlib.sha256(b).hexdigest(),local=str(dst.relative_to(R)),authenticated=True)
entries=json.loads((R/'private/selected-tree.json').read_text())['entries']
with ThreadPoolExecutor(max_workers=4) as ex: out=list(ex.map(fetch,[e for e in entries if e['type']=='blob']))
p='lean/docs/328.md'; api='https://api.github.com/repos/openai/math/contents/'+p+'?ref='+PIN
m=json.loads(get(api)); b=get('https://raw.githubusercontent.com/openai/math/'+PIN+'/'+p)
g=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert g==m['sha'] and len(b)==m['size']
(R/'private/lean-328.md').write_bytes(b);(R/'private/lean-328-metadata.json').write_text(json.dumps(m,indent=2)+'\n')
(R/'private/authenticated.json').write_text(json.dumps({'pin':PIN,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'blobs':out,'lean_doc':{'path':p,'size':len(b),'git_blob':g,'sha256':hashlib.sha256(b).hexdigest(),'api':api}},indent=2)+'\n')
print('Authenticated canonical blobs:',len(out)); print('LEAN 328 EXACT FULL BODY');print(b.decode())
