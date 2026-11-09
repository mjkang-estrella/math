from pathlib import Path
from urllib.request import urlopen, Request
from concurrent.futures import ThreadPoolExecutor
import json,hashlib
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r210')
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
entries=json.loads((R/'private/tree-selection.json').read_text())
folder='preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/'
def fetch(e):
 url='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+e['path']
 b=urlopen(Request(url,headers={'User-Agent':'Research-source-reader'}),timeout=45).read()
 sha=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 assert len(b)==e['size'] and sha==e['sha'], e['path']
 dest=R/'private/source334'/e['path'][len(folder):]; dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
 return dict(path=e['path'],url=url,bytes=len(b),git_blob=sha,sha256=hashlib.sha256(b).hexdigest(),local=str(dest))
with ThreadPoolExecutor(max_workers=4) as ex: out=list(ex.map(fetch,[e for e in entries if e['type']=='blob']))
assert len(out)==12
(R/'private/source-authentication.json').write_text(json.dumps(out,indent=2)+'\n')
print('All 12 pinned blobs authenticated, total bytes',sum(x['bytes'] for x in out))
p='lean/docs/334.md'; url='https://api.github.com/repos/openai/math/contents/'+p+'?ref='+PIN
meta=json.loads(urlopen(Request(url,headers={'User-Agent':'Research-source-reader'}),timeout=45).read())
b=urlopen('https://raw.githubusercontent.com/openai/math/'+PIN+'/'+p,timeout=45).read()
s=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert s==meta['sha']
(R/'private/334.md').write_bytes(b)
(R/'private/334-authentication.json').write_text(json.dumps({'path':p,'metadata_url':url,'git_blob':s,'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)},indent=2)+'\n')
print('\nLEAN NAVIGATION\n'+b.decode())
print('\nSOURCE README\n'+(R/'private/source334/README.md').read_text())
print('\nMAIN COMPLETE\n'+(R/'private/source334/build/main.tex').read_text())
print('\nBIBLIOGRAPHY COMPLETE\n'+(R/'private/source334/build/references.bib').read_text())
