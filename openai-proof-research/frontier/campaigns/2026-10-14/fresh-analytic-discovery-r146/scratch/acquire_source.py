from pathlib import Path
import json,hashlib,urllib.request
r=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r146')
pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
sel=json.loads((r/'scratch/source-selection.json').read_text())
records=[]
for e in sel:
 if e['type']!='blob' or '/verification/' in e['path'] or e['path'].endswith('.pdf'):continue
 url='https://raw.githubusercontent.com/openai/math/'+pin+'/'+e['path']
 b=urllib.request.urlopen(url,timeout=40).read()
 sha1=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 assert len(b)==e['size'] and sha1==e['sha']
 rel=Path('private/source')/e['path'].split('-September-24-2026/',1)[1]
 p=r/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
 records.append(dict(canonical_path=e['path'],url=url,size=len(b),gitblob_sha1=sha1,sha256=hashlib.sha256(b).hexdigest(),selected_path=str(rel)))
(r/'SOURCE-AUTH.json').write_text(json.dumps(dict(pin=pin,tree_sha256='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b',entries=records),indent=2)+'\n')
print('authenticated',len(records),'source bodies')
