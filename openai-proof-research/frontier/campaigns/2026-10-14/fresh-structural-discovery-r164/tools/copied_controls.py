"""Small selected-copy controls; never reuse an incoming original manifest."""
from pathlib import Path
import json,hashlib,stat,subprocess,sys,importlib.util
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r164')
sp=importlib.util.spec_from_file_location('verifier',R/'tools/verify_packet.py');v=importlib.util.module_from_spec(sp);sp.loader.exec_module(v)
C=R/'seal/selected-control';(C/'tools').mkdir(parents=True,exist_ok=True);(C/'original').mkdir();(C/'protected').mkdir()
selection=[('tools/verify_packet.py','tools/verify_packet.py'),('notes/02-integrated-calculations.md','original/calculation.md'),('private/source/list/sections/02-preliminaries.tex','protected/source.tex')]
for old,new in selection:(C/new).write_bytes((R/old).read_bytes())
(C/'FINAL.md').write_text('Selected-copy integrity fixture only; no mathematical assertion.\n')
(C/'REPORT.md').write_text('Three selected copies, individually identified. Original whole-packet manifests are not inherited.\n')
files,dirs=v.inventory(C);m={'schema':'r164-exact-selection-v1','files':files,'directories':dirs,'envelope_modes':{n:0o644 for n in v.ENV},'selection_origin':selection}
(C/'MANIFEST.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
anchors={n:v.sha((C/n).read_bytes()) for n in v.ENV};rows=[]
def run(label,expected,overrides=None):
 a=dict(anchors);a.update(overrides or {})
 cmd=[sys.executable,'-B',str(C/'tools/verify_packet.py'),'--root',str(C),'--final-sha256',a['FINAL.md'],'--manifest-sha256',a['MANIFEST.json'],'--report-sha256',a['REPORT.md']]
 z=subprocess.run(cmd,capture_output=True,text=True,timeout=15);ok=(z.returncode==0)
 assert ok==expected,(label,z.stdout,z.stderr)
 rows.append({'control':label,'expected_accept':expected,'accepted':ok,'output':(z.stdout+z.stderr).strip()})
run('baseline-selected-copies',True)
p=C/'original/calculation.md';original=p.read_bytes();p.write_bytes(original+b'\nchanged\n');run('payload-byte-mutation',False);p.write_bytes(original)
p.unlink();run('missing-selected-member',False);p.write_bytes(original)
e=C/'extra';e.write_text('extra');run('extra-member',False);e.unlink()
p.unlink();p.symlink_to('../protected/source.tex');run('symlink-in-place-of-member',False);p.unlink();p.write_bytes(original)
for n in ['FINAL.md','MANIFEST.json','REPORT.md']:run('wrong-detached-'+n,False,{n:'0'*64})
# Read-only direct replay after restoring bytes; report as a separate positive check.
v.verify(C,anchors);rows.append({'control':'restored-baseline-read-only-replay','accepted':True,'expected_accept':True})
receipt={'selection_only':True,'detached_fixture_anchors':anchors,'controls':rows,'control_count':len(rows),'limits':'Fixture controls check artifacts only, not mathematics or independent reviews.'}
(R/'seal/control-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'controls':len(rows),'all_expected_outcomes':True,'fixture_payload_files':len(files)},indent=2))
