from pathlib import Path
import subprocess,sys,json,hashlib
r=Path(__file__).resolve().parents[1];s=r/'public-source';e=r/'work/test-envelope';x=r/'work/clean-extraction'
a=['--final',str(e/'FINAL.json'),'--final-sha256','5291310ff0379f636db161393c3e98e19fc0895f80bc32580b816516e899a6a0','--manifest',str(r/'MANIFEST.json'),'--manifest-sha256','018d81cc1895f6fdaa4c2429403b2811e2f7b2428df60696ca6497e4f5e22d95','--report',str(e/'REPORT.md'),'--report-sha256','59f638c368b2a3c808d124f52c89fc18e91c787c8a56508a2aa0e24a6b4356c8','--archive',str(r/'release.zip'),'--archive-sha256','0248221680c2c06a7031c98105b837562b5f184bab5c0bbdbde955f1b36ee096']
def run(cmd):subprocess.run([str(v) for v in cmd],check=True)
if sys.argv[-1]=='extract':
 run([sys.executable,'-B',s/'verify.py',*a,'--root',s]);run([sys.executable,'-B',s/'archive.py','extract','--archive',r/'release.zip','--manifest',r/'MANIFEST.json','--output',x]);run([sys.executable,'-B',x/'verify.py',*a,'--root',x])
elif sys.argv[-1]=='controls':run([sys.executable,'-B',x/'integrity_controls.py','--root',x,'--output',r/'work/controls-1',*a])
elif sys.argv[-1]=='reassemble':
 run([sys.executable,'-B',x/'archive.py','assemble','--source',x,'--output',r/'work/assembly-2']);assert (r/'release.zip').read_bytes()==(r/'work/assembly-2/release.zip').read_bytes();print('ZIP REASSEMBLY BYTE IDENTICAL')
