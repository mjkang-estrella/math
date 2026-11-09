from pathlib import Path
import subprocess,json,hashlib
r=Path(__file__).resolve().parents[1]; repo=r.parents[3]
queries={
 '078':r'Gevrey|pseudo.?conformal|smooth.{0,30}(phase|Bochner)|Taylor.{0,40}(amplitude|phase)',
 '219':r'conditional.{0,3}(centering|mean)|Bernoulli.{0,35}(Anderson|disorder)|continuous.switching|environment.{0,20}(matching|rotation)|weak.Anderson',
 '366':r'crack.tip|weak.{0,2}L.{0,2}4|tip.count|Mumford.Shah',
 '341':r'hypersymplectic|compatible.family|equivariant.{0,25}(hyperk|K3)',
 '083':r'selected.diagonal|Hilbert.{0,30}Lipschitz|straight.segment|maximal.truncation',
 '090':r'Palm|stationary.{0,30}(crystall|lattice)|deleted.jet|original.cell|mesoscopic.atlas'}
base=['rg','-l','-i','--hidden','-g','*.md','-g','*.tex','-g','*.txt','-g','*.json','-g','*.py']
for g in ['!**/private/**','!**/inputs/**','!**/sources/**','!**/frozen/**','!**/*control*/**','!**/copies/**','!**/fresh-analytic-discovery-r120/**']:base+=['-g',g]
out=[]
for fam,q in queries.items():
 cmd=base+[q,'frontier/campaigns','frontier/iterations','frontier/experiments']
 p=subprocess.run(cmd,cwd=repo,capture_output=True,text=True);assert p.returncode in [0,1],p.stderr
 hits=[]
 for f in p.stdout.splitlines():
  z=repo/f; b=z.read_bytes();hits.append(dict(path=f,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()))
 out.append(dict(family=fam,pattern=q,command=cmd,returncode=p.returncode,hits=hits));print(fam,len(hits),'largest',sorted([(h['bytes'],h['path']) for h in hits],reverse=True)[:3])
(r/'packet/public/search-register.json').write_text(json.dumps({'no_size_cutoff':True,'includes_work_and_large_authored_files':True,'method':'Filename hits are navigation only, not semantic reading. Exclusions remove known reference/copy areas, not large originals. Earlier broad searches also occurred; this final reproducible pass records exact file identities at search time.','queries':out},indent=2)+'\n')
