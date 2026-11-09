"""Proportionate copied fixture controls using the final verifier's exact core logic."""
from pathlib import Path
import json, os, runpy, shutil
R=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ct')
v=runpy.run_path(str(R/'verify.py'))
c=R/'private/controls'; c.mkdir(mode=0o700)
f=c/'fixture'; f.mkdir(mode=0o700)
original=c/'original.txt'; original.write_bytes(b'bounded artifact control\n'); os.chmod(original,0o644)
shutil.copy2(original,f/'copy.txt')
files,dirs=v['inventory'](f)
m={'schema':1,'pin':v['PIN'],'files':files,'directories':dirs}
(f/'MANIFEST.json').write_text(json.dumps(m,indent=2)+'\n')
check=lambda:v['check_payload'](f,m,{'MANIFEST.json'})
check(); tests=[]
def reject(name,fn):
 try: fn()
 except ValueError: tests.append({'test':name,'result':'REJECT as intended'}); return
 raise RuntimeError('control falsely accepted: '+name)
(f/'copy.txt').write_bytes(b'changed\n'); reject('changed copied bytes',check)
shutil.copy2(original,f/'copy.txt'); check()
os.chmod(f/'copy.txt',0o600); reject('changed full mode',check)
os.chmod(f/'copy.txt',0o644); check()
(f/'extra').write_bytes(b'x'); reject('extra member',check); (f/'extra').unlink(); check()
for label in ['FINAL','MANIFEST','REPORT']:
 reject('wrong detached '+label,lambda:v['anchor'](original,'0'*64))
assert original.read_bytes()==(f/'copy.txt').read_bytes()==b'bounded artifact control\n'
assert original.stat().st_mode==(f/'copy.txt').stat().st_mode==0o100644
check()
(c/'RESULTS.json').write_text(json.dumps({'tests':tests,'restored_fixture':'MATCH','original_unchanged':True,'mathematical_gate':False},indent=2)+'\n')
print(json.dumps({'negative_controls':len(tests),'restored_fixture':'MATCH','original_unchanged':True}))
