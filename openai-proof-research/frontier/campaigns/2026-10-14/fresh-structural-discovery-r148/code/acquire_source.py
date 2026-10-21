from pathlib import Path
import urllib.request,hashlib,json
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research'); R=P/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r148'; dest=R/'private/source';dest.mkdir(exist_ok=True)
b=(P/'sources/preprints-tree.json').read_bytes(); assert hashlib.sha256(b).hexdigest()=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
j=json.loads(b);assert len(j['tree'])==13223 and not j['truncated'];out=[]
for e in j['tree']:
 if e['type']!='blob' or 'A-counterexample-to-Sidorenkos-conjecture-' not in e['path'] or not e['path'].endswith(('.tex','.bib','.md')):continue
 url='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
 data=urllib.request.urlopen(url,timeout=40).read(); blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
 assert len(data)==e['size'] and blob==e['sha']
 rel=e['path'].split('/',2)[2]; f=dest/rel; f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(data)
 out.append({'path':e['path'],'url':url,'size':len(data),'git_blob':blob,'sha256':hashlib.sha256(data).hexdigest(),'local':str(f.relative_to(R))})
(dest/'receipts.json').write_text(json.dumps(out,indent=2)+'\n'); print('Authenticated',len(out),'blobs')
