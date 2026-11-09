from pathlib import Path
import hashlib,json,os
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r220')
ns={'__name__':'r220_readonly_verifier'};exec(compile((R/'verify_packet.py').read_bytes(),'verify_packet.py','exec'),ns)
C=R/'controls';C.mkdir();P=C/'packet';P.mkdir();(P/'sample.txt').write_bytes(b'local copied control\n');(P/'FINAL.md').write_bytes(b'control only\n');(C/'REPORT.md').write_bytes(b'control outside report\n')
files,dirs=ns['inspect_packet'](P);(C/'MANIFEST.json').write_text(json.dumps(dict(format='r220-exact-selection-v1',files=files,directories=dirs),sort_keys=True,indent=2)+'\n')
sha=ns['digest'];anchors=[sha(C/'MANIFEST.json'),sha(P/'FINAL.md'),sha(C/'REPORT.md')]
ns['verify'](C,*anchors);results=['baseline matched']
def reject(label,args=None):
 try:ns['verify'](C,*(args or anchors))
 except ValueError:results.append(label+' rejected')
 else:raise AssertionError(label+' unexpectedly accepted')
p=P/'sample.txt';original=p.read_bytes();mode=p.stat().st_mode&0o777
p.write_bytes(original+b'changed\n');reject('copied byte mutation');p.write_bytes(original)
x=P/'extra.txt';x.write_bytes(b'extra');reject('copied extra member');x.unlink()
p.chmod(0o640 if mode!=0o640 else 0o600);reject('copied mode mutation');p.chmod(mode)
reject('wrong detached anchor',['0'*64,anchors[1],anchors[2]])
ns['verify'](C,*anchors);results.append('restored copied baseline matched')
(R/'private/copied-controls.json').write_text(json.dumps({'purpose':'tiny copied artifact controls; no mathematical grade','results':results},indent=2)+'\n');print(json.dumps(results))
