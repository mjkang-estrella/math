from fetch import get,D
import json,hashlib,pathlib
r=json.loads((D/'reservation.json').read_text());out={}
for name in ['D5','Problems']:
 p=D.parent/f'expanded-corpus-r65/sources/omega-{name}.json';b=p.read_bytes();o=json.loads(b);out[name]={'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'truncated':o.get('truncated'),'entries':len(o['tree']),'id_hits':{str(i):[v['path'] for v in o['tree'] if str(i) in v['path']] for i in r['ids']},'semantic_leads':[v['path'] for v in o['tree'] if any(k in v['path'].lower() for k in ['catalan','annihilation','kleitman','snevily','antipath','mixedmetric','poncelet','illumination','arborescence'])]}
p=D.parent/'fresh-corpus-r10/sources/registry-preprints.json';b=p.read_bytes();o=json.loads(b);out['openai']={'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'id_hits':{str(i):[v['path'] for v in o.get('tree',[]) if str(i) in v['path']] for i in r['ids']},'note':'HEAD unchanged; path screen only, no global novelty clearance'}
out['omega_update']='compare/790d20daa36ba56dd2bd55777592ac36cf8a92ef...8d9d5d9ee811f5c54fdd5ef5f2e1c59bf2b32d95 fetched; 15 commits, seven changed paths; added PathCatalanFunctional semantic lead'
(D/'outputs/registry-screen.json').write_text(json.dumps(out,indent=2)+'\n')
print(get(('omega-PathCatalanFunctional.lean','https://raw.githubusercontent.com/the-omega-institute/trureturing/8d9d5d9ee811f5c54fdd5ef5f2e1c59bf2b32d95/D5/S3/Combinatorics/Graph/LinearForests/PathCatalanFunctional.lean')))
print(get(('2607.26956.html','https://arxiv.org/html/2607.26956')))
print(get(('direction-prior.pdf','https://chinaxiv.org/user/download.htm?uuid=37a1f9f5cffc4c87b8c93a0ca4f15889&filetype=pdf')))
