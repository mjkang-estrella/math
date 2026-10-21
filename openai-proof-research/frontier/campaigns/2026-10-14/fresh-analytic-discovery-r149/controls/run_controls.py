"""Build a small independently sealed copied selection; exercise verifier read-only behavior."""
from pathlib import Path
import hashlib,json,shutil,subprocess,stat
R=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r149')
F=R/'private/copied-controls';F.mkdir(parents=True,exist_ok=True)
source=R/'private/source/Equality-cases-in-the-sharp-one-dimensional-matrix-Lieb-Thirring-inequality-October-5-2026/sections/preliminaries.tex'
(F/'protected-source.tex').write_bytes(source.read_bytes());(F/'original-note.md').write_bytes((R/'GAPS.md').read_bytes())
for name in ['FINAL.md','REPORT.md']:(F/name).write_text('Small copied control selection; not the original packet or a mathematical review.\n')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
entries=[{'path':p.name,'size':p.stat().st_size,'sha256':sha(p)} for p in sorted(F.iterdir()) if p.is_file() and p.name not in ['FINAL.md','MANIFEST.json','REPORT.md']]
(F/'MANIFEST.json').write_text(json.dumps({'schema':'r149-exact-payload-v1','outside_envelopes':['FINAL.md','MANIFEST.json','REPORT.md'],'files':entries},indent=2)+'\n')
anchors=[sha(F/n) for n in ['FINAL.md','MANIFEST.json','REPORT.md']]
args=['python3',str(R/'verify.py'),str(F),'--final-sha256',anchors[0],'--manifest-sha256',anchors[1],'--report-sha256',anchors[2]]
def snapshot():
 return {str(p.relative_to(F)):{'sha256':sha(p),'size':p.stat().st_size,'mode':stat.S_IMODE(p.stat().st_mode),'nlink':p.stat().st_nlink} for p in F.rglob('*') if p.is_file()}
results=[]
def check(name,expected,cmd=None):
 before=snapshot();s=subprocess.run(cmd or args,capture_output=True,text=True,timeout=10);after=snapshot()
 if (s.returncode==0)!=expected or before!=after:raise RuntimeError(name+' failed: '+s.stdout+s.stderr)
 results.append({'case':name,'accepted':s.returncode==0,'expected':expected,'readonly_snapshot_equal':before==after,'output':(s.stdout+s.stderr).strip()})
check('baseline',True)
p=F/'original-note.md';original=p.read_bytes();p.write_bytes(original+b'changed\n');check('changed payload',False);p.write_bytes(original)
p.unlink();check('missing payload',False);p.write_bytes(original)
(F/'.hidden-extra').write_text('extra');check('hidden extra',False);(F/'.hidden-extra').unlink()
bad=args.copy();bad[bad.index('--manifest-sha256')+1]='0'*64;check('wrong detached manifest anchor',False,bad)
check('restored',True)
rec={'fixture_kind':'two independently selected copied payloads; independent new manifest, no inherited original manifest','protected_source_original':str(source.relative_to(R)),'original_note': 'GAPS.md','fixture_anchors':dict(zip(['FINAL.md','MANIFEST.json','REPORT.md'],anchors)),'cases':results,'scope':'Artifact bytes/membership/read-only behavior only; not mathematical gates.'}
(R/'controls/results.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps({'controls':len(results),'outcomes_as_expected':True,'read_only':True}))
