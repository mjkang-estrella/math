from pathlib import Path
import json,hashlib,urllib.request,concurrent.futures
r=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r161/packet/private'); rows=json.loads((r/'family-tree.json').read_text()); pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
assert len(rows)==13 and sum(x['type']=='blob' for x in rows)==10
prefix=rows[0]['path']
def fetch(x):
 url='https://raw.githubusercontent.com/openai/math/'+pin+'/'+x['path']
 with urllib.request.urlopen(url,timeout=45) as f: b=f.read()
 sha=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 assert len(b)==x['size'] and sha==x['sha'],x['path']
 p=r/'canonical'/x['path'][len(prefix)+1:];p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
 return {**x,'raw_url':url,'sha256':hashlib.sha256(b).hexdigest(),'local':p.as_posix()}
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex: out=list(ex.map(fetch,[x for x in rows if x['type']=='blob']))
(r/'canonical-authentication.json').write_text(json.dumps(out,indent=2)+'\n');print('Authenticated all ten blobs,',sum(x['size'] for x in out),'bytes.')
for name in ['README.md','build/main.tex','build/sections/introduction.tex','build/sections/setup.tex']:
 p=r/'canonical'/name;print('\nCOMPLETE',name,p.stat().st_size,'bytes\n'+p.read_text())
