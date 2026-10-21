from pathlib import Path
import hashlib,json,subprocess,shutil,sys
R=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r153').resolve();C=R/'private/controls';C.mkdir(parents=True,exist_ok=True)
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def snap(d):return {str(p.relative_to(d)):h(p) for p in sorted(d.rglob('*')) if p.is_file()}
b=C/'selected-baseline';b.mkdir();sources=[R/'notes/GEOMETRIC-CHECKS.md',R/'private/canonical/preprints/An-L2-Einstein-Gap-for-Nonnegatively-Curved-Four-Manifolds-October-5-2026/build/source/main.tex']; originals={str(p):h(p) for p in sources}
for p,n in zip(sources,['own-note.md','private-source.tex']):shutil.copyfile(p,b/n)
(b/'FINAL.md').write_text('Selected two-member copied-control fixture only. Not an original packet.\n')
(b/'REPORT.md').write_text('Independent selected membership; source remains private under original rights.\n')
files=[{'path':n,'bytes':(b/n).stat().st_size,'sha256':h(b/n)} for n in ['own-note.md','private-source.tex']]
(b/'MANIFEST.json').write_text(json.dumps({'outside_envelopes':sorted(['FINAL.md','MANIFEST.json','REPORT.md']),'files':files},indent=2)+'\n')
anchors={n:h(b/n) for n in ['FINAL.md','MANIFEST.json','REPORT.md']};results=[]
for name in ['baseline','changed','missing','hidden-extra','wrong-anchor','restored']:
 d=C/name;shutil.copytree(b,d);aa=dict(anchors)
 if name=='changed':(d/'own-note.md').write_bytes((d/'own-note.md').read_bytes()+b'X')
 if name=='missing':(d/'private-source.tex').unlink()
 if name=='hidden-extra':(d/'.extra').write_bytes(b'extra')
 if name=='wrong-anchor':aa['REPORT.md']='0'*64
 if name=='restored':
  (d/'own-note.md').write_bytes(b'mutation');shutil.copyfile(b/'own-note.md',d/'own-note.md')
 before=snap(d)
 cmd=[sys.executable,str(R/'tools/verify.py'),str(d),'--final-sha',aa['FINAL.md'],'--manifest-sha',aa['MANIFEST.json'],'--report-sha',aa['REPORT.md']]
 run=subprocess.run(cmd,capture_output=True,text=True,timeout=15);after=snap(d);want=0 if name in ['baseline','restored'] else 1
 assert run.returncode==want and before==after,(name,run.stdout,run.stderr)
 results.append({'case':name,'exit_code':run.returncode,'expected':want,'copy_unchanged':before==after,'output':run.stdout.strip()})
assert originals=={str(p):h(p) for p in sources}
(C/'results.json').write_text(json.dumps({'scope':'two selected members, never whole-original packet','anchors':anchors,'originals_unchanged':True,'cases':results,'mathematical_gate':False},indent=2)+'\n')
print(json.dumps(results,indent=2))
