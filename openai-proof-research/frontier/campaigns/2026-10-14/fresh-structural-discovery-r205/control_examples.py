"""Tiny fresh manifests for copied author files; never use an inherited/reduced manifest."""
from pathlib import Path
import hashlib,json,os,shutil,sys
ROOT=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r205')
sys.path.insert(0,str(ROOT));from verify_packet import verify
os.umask(0o077)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
before={f:sha(ROOT/f) for f in ['FINAL.md','derivations.md']}
c=ROOT/'controls';c.mkdir(mode=0o700);base=c/'baseline';base.mkdir(mode=0o700)
for f in before:shutil.copyfile(ROOT/f,base/f);(base/f).chmod(0o444)
(base/'REPORT.md').write_text('Tiny copied-author-file artifact control. No mathematical gate.\n')
m={'schema':'r205-exact-selection-v1','files':[{'path':f,'bytes':(base/f).stat().st_size,'sha256':sha(base/f),'mode':'0444'} for f in sorted(before)],'directories':{'.':'0700'},'outside_files':['MANIFEST.json','REPORT.md'],'outside_directories':[]}
(base/'MANIFEST.json').write_text(json.dumps(m,indent=2)+'\n')
anchors=[sha(base/f) for f in ['FINAL.md','MANIFEST.json','REPORT.md']]
results={'baseline':verify(base,*anchors),'negative_controls':{}}
for name in ['changed-content','changed-mode','extra-selection']:
 d=c/name;shutil.copytree(base,d)
 if name=='changed-content':
  f=d/'derivations.md';f.chmod(0o644);f.write_bytes(f.read_bytes()+b'\nchanged copied bytes\n');f.chmod(0o444)
 elif name=='changed-mode':(d/'derivations.md').chmod(0o644)
 else:(d/'extra.txt').write_text('unselected copied control extra\n')
 try:verify(d,*anchors)
 except ValueError as e:results['negative_controls'][name]={'rejected':True,'reason':str(e)}
 else:raise AssertionError('Control not rejected: '+name)
assert before=={f:sha(ROOT/f) for f in before}
results['original_author_files_unchanged']=True
results['fresh_control_manifest_not_reduced_inherited_manifest']=True
(c/'results.json').write_text(json.dumps(results,indent=2)+'\n');print(json.dumps(results,indent=2))
