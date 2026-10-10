from pathlib import Path
import json,hashlib,subprocess,shutil
R=Path(__file__).resolve().parents[3]; S=R/'frontier/sources/i80_geometric_flows_computation_discovery'; C=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
def h(b):return hashlib.sha256(b).hexdigest()
def save(p,o):p.write_text(json.dumps(o,indent=2,ensure_ascii=False)+'\n')
inputs=[]
for n in ['AGENTS.md','README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json','frontier/iterations/iteration80-geometric-flows-computation-discovery-task.json']:
 p=R/n;b=p.read_bytes();q=S/'ledgers'/n;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b);inputs.append(dict(path=n,sha256=h(b),snapshot=str(q.relative_to(R)),mutable=n in ['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']))
(S/'full-brief.txt').write_text(json.loads((R/'frontier/iterations/iteration80-geometric-flows-computation-discovery-task.json').read_text())['brief']+'\n')
t=json.loads((R/'sources/preprints-tree.json').read_text()); blobs={e['path']:e for e in t['tree'] if e['type']=='blob'}
paths=subprocess.check_output(['rg','--files','--no-ignore',str(C)],text=True).splitlines();domain=[]
for f in sorted(paths):
 p=Path(f);b=p.read_bytes();n=str(p.relative_to(C));sha=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert blobs[n]['sha']==sha;domain.append(dict(path=str(p.relative_to(R)),upstream_path=n,sha256=h(b),git_blob=sha,bytes=len(b)))
missing=[e for n,e in blobs.items() if n not in {x['upstream_path'] for x in domain}]
assert len(t['tree'])==13223 and len(blobs)==10373 and len(domain)==9340 and len(missing)==1033
save(S/'corpus-domain.json',dict(entries=13223,manuscripts=len({e['path'].split('/')[1] for e in t['tree']}),blobs=10373,files=domain,outside=missing))
queries={
'geometry':r'hypersymplectic|hyperk.{0,3}hler|taming.implies|bounded.scalar|Ricci.flow',
'fluid':r'Turing|computab|computation|Navier.Stokes|finite.total|eventually.stationary|slow.clock',
'mechanisms':r'parametric|equivariant|monodromy|curvature.concentration|finite.resolution|robust.detec|analytic.forcing|Gevrey|noise.robust|forcing.budget'}
searches=[]
for key,pat in queries.items():
 p=subprocess.run(['rg','--no-ignore','-n','-i','--',pat,str(C)],capture_output=True,text=True);assert p.returncode in (0,1)
 out=p.stdout.replace(str(C)+'/', '');q=S/(key+'-search.txt');q.write_text(out);searches.append(dict(name=key,pattern=pat,flags=['--no-ignore','-n','-i'],output=str(q.relative_to(R)),lines=len(out.splitlines()),sha256=h(q.read_bytes())))
save(S/'searches.json',searches);save(S/'inputs.json',inputs)
print({'corpus':len(domain),'outside':len(missing),'searches':[(s['name'],s['lines']) for s in searches]})
