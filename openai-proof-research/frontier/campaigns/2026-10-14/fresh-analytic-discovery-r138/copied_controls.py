"""Proportionate copied integrity controls. Writes only under this owned root."""
from pathlib import Path
import hashlib,json,shutil
from verify import inventory,verify,digest
ROOT=Path(__file__).resolve().parent
FIX=ROOT/'private/control-fixture'
if FIX.exists(): raise SystemExit('fixture already exists; no rerun/repair')
FIX.mkdir(parents=True)
for n in ['H-SCOPE.md','DERIVATION.md','freeze-receipt.json']: shutil.copyfile(ROOT/n,FIX/n)
original={n:digest((ROOT/n).read_bytes()) for n in ['H-SCOPE.md','DERIVATION.md','freeze-receipt.json']}
(FIX/'REPORT.md').write_text('Copied artifact-control fixture only; no mathematical claim.\n')
files,dirs=inventory(FIX)
(FIX/'MANIFEST.json').write_text(json.dumps({'schema':1,'files':files,'directories':dirs},sort_keys=True,indent=2)+'\n')
anchors={n:digest((FIX/n).read_bytes()) for n in ['REPORT.md','MANIFEST.json']}
(FIX/'FINAL.json').write_text(json.dumps({'manifest_sha256':anchors['MANIFEST.json'],'report_sha256':anchors['REPORT.md']},sort_keys=True,indent=2)+'\n')
anchors['FINAL.json']=digest((FIX/'FINAL.json').read_bytes())
results=[]
def expect(name,accepted,used=anchors):
 try: verify(FIX,used);actual=True;reason='accepted'
 except (ValueError,OSError) as e: actual=False;reason=str(e)
 results.append({'control':name,'expected_acceptance':accepted,'actual_acceptance':actual,'reason':reason})
 if actual!=accepted: raise RuntimeError('control discrepancy')
expect('unchanged copied baseline',True)
p=FIX/'H-SCOPE.md';b=p.read_bytes()
try:
 p.write_bytes(b+b'altered\n');expect('altered copied payload',False)
finally: p.write_bytes(b)
try:
 p.unlink();expect('missing copied payload',False)
finally: p.write_bytes(b)
p=FIX/'unexpected.txt'
try:
 p.write_text('extra');expect('extra copied payload',False)
finally: p.unlink()
p=FIX/'unexpected-directory'
try:
 p.mkdir();expect('extra directory',False)
finally: p.rmdir()
p=FIX/'symbolic-copy'
try:
 p.symlink_to('H-SCOPE.md');expect('symbolic payload',False)
finally: p.unlink()
bad=dict(anchors);bad['FINAL.json']='0'*64
expect('wrong detached anchor',False,bad)
expect('restored copied baseline',True)
after={n:digest((ROOT/n).read_bytes()) for n in original}
if original!=after: raise RuntimeError('original changed')
(ROOT/'controls-results.json').write_text(json.dumps({'kind':'artifact integrity only','fixture':'private/control-fixture','fixture_detached_anchors':anchors,'controls':results,'originals_before':original,'originals_after':after},indent=2)+'\n')
print(json.dumps({'controls':len(results),'originals_unchanged':True,'mathematical_gate':False}))
