"""Tiny copied fixture with its own selection/manifest, never inherited anchors."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,sys
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r214').resolve()
C=R/'controls'/'fixture'
assert not C.exists(), 'control fixture already exists'
C.mkdir(parents=True,mode=0o700);(C/'private').mkdir(mode=0o700)
for name in ['verify_packet.py','FINAL.md']: shutil.copyfile(R/name,C/name)
(C/'private'/'control.bin').write_bytes((R/'private/source/build/main.tex').read_bytes()[:16])
(C/'REPORT.md').write_text('Tiny artifact fixture only. Original source rights retained for16 copied bytes. No mathematical validation.\n')
names=sorted(['verify_packet.py','FINAL.md','private/control.bin','SELECTION.json'])
(C/'SELECTION.json').write_text(json.dumps({'files':names,'outside_files':sorted(['MANIFEST.json','REPORT.md','ANCHORS.json','verification.json']),'outside_directories':['controls']},indent=2)+'\n')
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
entries=[]
for name in names:
 p=C/name;private=name.startswith('private/') or name=='SELECTION.json';p.chmod(0o400 if private else 0o444)
 entries.append({'path':name,'bytes':p.stat().st_size,'sha256':sha(p),'mode':'0400' if private else '0444','rights':'private-original-rights' if private else 'original-local'})
(C/'MANIFEST.json').write_text(json.dumps({'schema':'r214-exact-selection-v1','files':entries,'directories':[{'path':'private','mode':'0700'}]},indent=2)+'\n')
(C/'MANIFEST.json').chmod(0o400);(C/'REPORT.md').chmod(0o444)
anchors={'manifest':sha(C/'MANIFEST.json'),'final':sha(C/'FINAL.md'),'report':sha(C/'REPORT.md')}
def run(overrides=None):
 a=dict(anchors);a.update(overrides or {})
 cmd=[sys.executable,str(C/'verify_packet.py'),'--root',str(C)]
 for k,v in a.items():cmd.extend(['--'+k+'-sha256',v])
 p=subprocess.run(cmd,capture_output=True,text=True,timeout=20)
 return {'exit_code':p.returncode,'stdout':p.stdout.strip(),'stderr':p.stderr.strip()}
results={'fixture_only':True,'baseline':run()};assert results['baseline']['exit_code']==0
p=C/'private/control.bin';before=p.read_bytes();p.chmod(0o600);p.write_bytes(before+b'X');p.chmod(0o400)
results['changed_copy']=run();assert results['changed_copy']['exit_code']!=0
p.chmod(0o600);p.write_bytes(before);p.chmod(0o400)
p.chmod(0o444);results['wrong_mode']=run();assert results['wrong_mode']['exit_code']!=0;p.chmod(0o400)
p=C/'unselected.txt';p.write_text('extra copied-fixture file\n');p.chmod(0o444)
results['extra_file']=run();assert results['extra_file']['exit_code']!=0;p.unlink()
results['wrong_anchor']=run({'final':'0'*64});assert results['wrong_anchor']['exit_code']!=0
results['restored']=run();assert results['restored']['exit_code']==0
(R/'controls/results.json').write_text(json.dumps(results,indent=2)+'\n');(R/'controls/results.json').chmod(0o400)
print(json.dumps({'baseline':True,'changed_copy_rejected':True,'wrong_mode_rejected':True,'extra_file_rejected':True,'wrong_anchor_rejected':True,'restored':True,'fixture_selected_bytes':sum(x['bytes'] for x in entries)}))
