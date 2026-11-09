exec(open('frontier/campaigns/2026-10-14/fresh-structural-discovery-r125/scratch/acquire.py').read().split('sel=[]')[0])
sel=[]
for e in tree['tree']:
 p=e['path']
 if e['type']!='blob':continue
 if 'Conditional-coordinate-sweeps-and-analytic-transfer' in p and p.endswith('.tex') and '/figures/' not in p:sel.append(e)
 if 'Signed-tensor-densities-and-diagram-budgets' in p and any(p.endswith(s) for s in ['00-introduction.tex','01-preliminaries.tex','02-static.tex']):sel.append(e)
 if 'Compatibility-entropy-and-the-spectrum' in p and any(p.endswith(s) for s in ['00-introduction.tex','01-preliminaries.tex','03-spectral-conversion.tex']):sel.append(e)
def f(e):
 u='https://raw.githubusercontent.com/openai/math/'+pin+'/'+e['path']; b=urllib.request.urlopen(u,timeout=45).read(); assert len(b)==e['size']; assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['sha']; dst=O/'packet/private/upstream'/e['path']; dst.parent.mkdir(parents=True,exist_ok=True); dst.write_bytes(b); return dict(canonical=e,url=u,local=str(dst.relative_to(O/'packet')),sha256=hashlib.sha256(b).hexdigest())
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as ex: records=list(ex.map(f,sel))
p=O/'packet/private/upstream-register.json';old=json.loads(p.read_text());p.write_text(json.dumps(old+records,indent=2)+'\n');print('added',len(records))
