"""Run once, after all research edits. No inherited manifest."""
from pathlib import Path
import json, runpy, sys, os
sys.dont_write_bytecode=True
R=Path(__file__).resolve().parents[1];P=Path.cwd()
v=runpy.run_path(str(R/'verify.py'))
for n in ['MANIFEST.json','REPORT.md','ANCHORS.json']:
    if (R/n).exists():raise SystemExit('Refusing to reseal')
# Small copied control, with the same collect/verify/anchor functions.
C=R/'scratch/integrity-control';C.mkdir(exist_ok=True)
(C/'original.txt').write_bytes(b'R163 tiny integrity fixture\n');(C/'copy.txt').write_bytes((C/'original.txt').read_bytes())
files,dirs=v['collect'](C); fixture={'pin':v['PIN'],'files':files,'directories':dirs}
v['verify_payload'](C,fixture)
checks=[]
def reject(name,action):
    try:action()
    except ValueError:checks.append({'control':name,'rejected':True})
    else:raise AssertionError('control not rejected '+name)
(C/'copy.txt').write_bytes(b'R163 tiny integrity fixturE\n');reject('changed-byte',lambda:v['verify_payload'](C,fixture));(C/'copy.txt').write_bytes((C/'original.txt').read_bytes())
os.chmod(C/'copy.txt',0o600);reject('changed-full-mode',lambda:v['verify_payload'](C,fixture));os.chmod(C/'copy.txt',0o644)
(C/'extra.txt').write_bytes(b'x');reject('extra-member',lambda:v['verify_payload'](C,fixture));(C/'extra.txt').unlink()
for name in ['FINAL','MANIFEST','REPORT']:reject('wrong-'+name+'-anchor',lambda:v['check_anchor'](C/'copy.txt','0'*64))
v['verify_payload'](C,fixture)
(R/'private/integrity-controls.json').write_text(json.dumps({'controls':checks,'restored_fixture':'MATCH','mathematical_gate':False},indent=2)+'\n')
# Private mode tightening is recorded before the final single seal.
for base,dirs,files in os.walk(R/'private'):os.chmod(base,0o700)
f,d=v['collect'](R); manifest={'format':1,'pin':v['PIN'],'files':f,'directories':d}
counts=v['verify_payload'](R,manifest);bindings=v['verify_bindings'](R,P)
# Preflight complete. These detached objects are written once only.
(R/'MANIFEST.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
final_sha=v['digest']((R/'FINAL.md').read_bytes());manifest_sha=v['digest']((R/'MANIFEST.json').read_bytes())
(R/'REPORT.md').write_text(f'''# R163-Sol detached report

PREFREEZE / no nominee. No mathematical gate or count assigned. Parent alone grades/counts. All old scopes/dispositions unchanged.

FINAL.md SHA256: {final_sha}

MANIFEST.json SHA256: {manifest_sha}

Same-logic preflight MATCH: {counts[0]} payload files, {counts[1]} bytes, {counts[2]} directories including root; {bindings[0]} source blobs/{bindings[1]} source entries; {bindings[2]} exact completed originals/copies. Sorted safe membership, hashes, lengths, full modes, pin and Git bindings checked. Tiny changed-byte, changed-mode, extra-member and three wrong-anchor controls rejected; restored tiny copied fixture MATCH. Artifact integrity only.

This REPORT is outside the payload manifest. Its own SHA256 is detached in ANCHORS.json and the handoff. verify.py is read-only and requires all three explicit external anchors. No inherited manifest or self-grade. Protected bodies/metadata remain private/local.
''')
report_sha=v['digest']((R/'REPORT.md').read_bytes());anchors={'FINAL.md':final_sha,'MANIFEST.json':manifest_sha,'REPORT.md':report_sha}
(R/'ANCHORS.json').write_text(json.dumps(anchors,indent=2,sort_keys=True)+'\n')
print(json.dumps(anchors,indent=2));print('PREFLIGHT',counts,bindings)
