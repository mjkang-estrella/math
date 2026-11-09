from pathlib import Path
import json,hashlib,urllib.request,concurrent.futures
r=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162/packet/private')
a=json.loads((r/'canonical-tree.json').read_text()); stem=a[0]['path']; pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
def get(e):
 url=f"https://raw.githubusercontent.com/openai/math/{pin}/{e['path']}"
 with urllib.request.urlopen(url,timeout=45) as s: b=s.read()
 h=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 assert len(b)==e['size'] and h==e['sha'],e['path']
 dst=r/'canonical'/e['path'][len(stem)+1:]; dst.parent.mkdir(parents=True,exist_ok=True); dst.write_bytes(b)
 return dict(path=e['path'],local=str(dst),url=url,bytes=len(b),git_blob=h,sha256=hashlib.sha256(b).hexdigest())
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool: records=list(pool.map(get,[e for e in a if e['type']=='blob']))
for d in [e for e in a if e['type']=='tree']:
 children=[x for x in a if x['path'].rsplit('/',1)[0]==d['path']]
 children.sort(key=lambda x:x['path'].rsplit('/',1)[1]+('/' if x['type']=='tree' else ''))
 body=b''.join(('40000' if x['type']=='tree' else x['mode']).encode()+b' '+x['path'].rsplit('/',1)[1].encode()+b'\0'+bytes.fromhex(x['sha']) for x in children)
 assert hashlib.sha1(b'tree '+str(len(body)).encode()+b'\0'+body).hexdigest()==d['sha']
(r/'canonical-authentication.json').write_text(json.dumps(records,indent=2)+'\n')
print('Authenticated all',len(records),'blobs and all 4 tree objects.')
for n in ['README.md','build/main.tex','build/sections/01-introduction.tex']:
 b=(r/'canonical'/n).read_bytes(); print('\nCANONICAL FULL',n,'[0,',len(b),')\n'+b.decode())
