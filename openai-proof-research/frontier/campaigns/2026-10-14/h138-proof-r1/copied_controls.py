"""Copied fixture integrity controls only. Writes confined to owned private/controls.
Never invokes the incoming verifier, modifies originals, or counts mathematics.
"""
from pathlib import Path
import json,hashlib,tempfile,shutil,importlib.util
R=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('owned_verifier',R/'verify.py');v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
A=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/fresh-analytic-discovery-r138')
orig={n:v.digest((A/n).read_bytes()) for n in ['H-SCOPE.md','AUTHOR-PROOF.md','DERIVATION.md']}
base=R/'private/controls';base.mkdir(exist_ok=True,parents=True)
results=[]
with tempfile.TemporaryDirectory(dir=base,prefix='fixture-') as td:
 t=Path(td)
 for n in ['H-SCOPE.md','AUTHOR-PROOF.md']:(t/n).write_bytes((A/n).read_bytes())
 (t/'REPORT.md').write_text('Copied integrity fixture only; no mathematical disposition.\n')
 files,dirs=v.inventory(t);(t/'MANIFEST.json').write_text(json.dumps({'schema':1,'files':files,'directories':dirs},sort_keys=True)+'\n')
 anchors={n:v.digest((t/n).read_bytes()) for n in ['REPORT.md','MANIFEST.json']}
 (t/'FINAL.json').write_text(json.dumps({'manifest_sha256':anchors['MANIFEST.json'],'report_sha256':anchors['REPORT.md']},sort_keys=True)+'\n');anchors['FINAL.json']=v.digest((t/'FINAL.json').read_bytes())
 def check(name,reject=False,aa=None):
  try:v.verify(t,aa or anchors); rejected=False;message='verified'
  except ValueError as e:rejected=True;message=str(e)
  assert rejected==reject,name
  results.append({'case':name,'expected':'reject' if reject else 'verify','observed':message,'passed':True})
 check('baseline')
 p=t/'AUTHOR-PROOF.md';b=p.read_bytes();p.write_bytes(b+b'\ncopy mutation\n');check('changed proof',True);p.write_bytes(b)
 p=t/'H-SCOPE.md';b=p.read_bytes();p.unlink();check('missing scope',True);p.write_bytes(b)
 (t/'EXTRA').write_text('copy only');check('unexpected file',True);(t/'EXTRA').unlink()
 aa=dict(anchors);aa['MANIFEST.json']='0'*64;check('wrong detached manifest anchor',True,aa)
 check('restored baseline')
for n,h in orig.items():assert v.digest((A/n).read_bytes())==h,n
(R/'controls-results.json').write_text(json.dumps({'cases':results,'all_passed':True,'negative_cases':4,'originals_before_and_after':orig,'fixture_removed':True,'mathematical_gate':False},indent=2)+'\n')
print('6 copied artifact controls passed, including 4 expected rejections; 3 selected original files unchanged')
