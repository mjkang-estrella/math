from pathlib import Path
import hashlib,json,os,shutil,subprocess,stat
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r163')
P=R/'private/controls';P.mkdir(exist_ok=True)
BASE=P/'base';BASE.mkdir();(BASE/'private').mkdir()
shutil.copyfile(R/'notes/02-integrated-calculations.md',BASE/'notes.txt')
shutil.copyfile(R/'private/source/uniform/build/manuscript/setup.tex',BASE/'private/setup.tex')
E={'FINAL.md','MANIFEST.json','REPORT.md'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def mkmanifest(root):
 fs={};ds={}
 for b,dirs,files in os.walk(root):
  for n in dirs:
   p=Path(b)/n;p.chmod(0o555);ds[p.relative_to(root).as_posix()]=0o555
  for n in files:
   p=Path(b)/n;p.chmod(0o444);s=p.stat();fs[p.relative_to(root).as_posix()]={'bytes':s.st_size,'sha256':sha(p),'mode':0o444}
 return {'format':'r163-exact-v1','root_mode':0o555,'files':dict(sorted(fs.items())),'directories':dict(sorted(ds.items()))}
m=mkmanifest(BASE)
(BASE/'MANIFEST.json').write_text(json.dumps(m,indent=2)+'\n')
(BASE/'FINAL.md').write_text('Selected copied fixture only. Not an original packet manifest or mathematical gate.\n')
(BASE/'REPORT.md').write_text('Own selected fixture manifest; source rights remain private.\n')
for n in E:(BASE/n).chmod(0o444)
BASE.chmod(0o555)
anchors={n:sha(BASE/n) for n in E}
def run(root,anc=anchors):
 cmd=['python','-B',str(R/'evidence/verify.py'),str(root),'--final-sha',anc['FINAL.md'],'--manifest-sha',anc['MANIFEST.json'],'--report-sha',anc['REPORT.md']]
 z=subprocess.run(cmd,capture_output=True,text=True,timeout=15)
 return {'exit':z.returncode,'output':z.stdout+z.stderr}
def writable(p):p.chmod(0o644)
def cleanup(p):
 for b,ds,fs in os.walk(p):
  Path(b).chmod(0o755)
 shutil.rmtree(p)
records=[{'case':'positive selected copy','expected':0,'observed':run(BASE)}]
for name in ['bytes','missing','extra','symlink','file-mode','directory-mode','manifest-anchor','final-anchor','report-anchor']:
 target=P/name;shutil.copytree(BASE,target)
 if name=='bytes':
  p=target/'notes.txt';writable(p);p.write_bytes(p.read_bytes()+b'changed\n');p.chmod(0o444)
 elif name=='missing':target.chmod(0o755);(target/'notes.txt').unlink();target.chmod(0o555)
 elif name=='extra':target.chmod(0o755);(target/'extra').write_text('extra');(target/'extra').chmod(0o444);target.chmod(0o555)
 elif name=='symlink':target.chmod(0o755);(target/'link').symlink_to('notes.txt');target.chmod(0o555)
 elif name=='file-mode':(target/'notes.txt').chmod(0o644)
 elif name=='directory-mode':(target/'private').chmod(0o755)
 else:
  n={'manifest-anchor':'MANIFEST.json','final-anchor':'FINAL.md','report-anchor':'REPORT.md'}[name]
  p=target/n;writable(p);p.write_bytes(p.read_bytes()+b'\n');p.chmod(0o444)
 records.append({'case':name,'expected':1,'observed':run(target)})
 cleanup(target)
records.append({'case':'positive unchanged baseline replay','expected':0,'observed':run(BASE)})
assert all(x['expected']==x['observed']['exit'] for x in records)
assert anchors=={n:sha(BASE/n) for n in E}
(R/'evidence/copied-controls.json').write_text(json.dumps({'controls':records,'fixture_detached_anchors':anchors,'scope':'two positive and nine negative selected-copy controls; actual packet not yet sealed; negative copies deleted, baseline retained; no original manifest inherited'},indent=2)+'\n')
print('11 copied controls matched expectations; actual originals untouched.')
