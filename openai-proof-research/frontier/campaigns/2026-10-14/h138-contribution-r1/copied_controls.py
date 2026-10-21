"""Small copied integrity fixture; never mutates the author root or selected originals."""
from pathlib import Path
import json,hashlib
from verify import inventory,verify,digest
R=Path(__file__).resolve().parent;F=R/'private/integrity-fixture';F.mkdir(exist_ok=False)
for src,dest in [(R/'private/incoming/H-SCOPE.md','originals/H-SCOPE.md'),(R/'private/incoming/AUTHOR-PROOF.md','originals/AUTHOR-PROOF.md')]:
 p=F/dest;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(src.read_bytes())
source=next((R/'private/source/preprints').glob('A-Three-Dimensional*/build/sections/transfer.tex'));p=F/'source/transfer.tex';p.parent.mkdir();p.write_bytes(source.read_bytes())
files,dirs=inventory(F);(F/'MANIFEST.json').write_text(json.dumps({'schema':1,'files':files,'directories':dirs},sort_keys=True)+'\n');(F/'REPORT.md').write_text('Copied integrity fixture only; no mathematical gate.\n')
anchors={n:digest((F/n).read_bytes()) for n in ['MANIFEST.json','REPORT.md']};(F/'FINAL.json').write_text(json.dumps({'schema':1,'manifest_sha256':anchors['MANIFEST.json'],'report_sha256':anchors['REPORT.md']},sort_keys=True)+'\n');anchors['FINAL.json']=digest((F/'FINAL.json').read_bytes())
baseline={q.relative_to(F).as_posix():q.read_bytes() for q in F.rglob('*') if q.is_file()};results=[]
def check(label,want,aa=anchors):
 try:verify(F,aa);ok=True;reason=None
 except ValueError as e:ok=False;reason=str(e)
 assert ok==want,(label,ok,reason)
 results.append({'case':label,'expected_accept':want,'observed_accept':ok,'reason':reason})
check('baseline copied payload',True)
p=F/'originals/AUTHOR-PROOF.md';p.write_bytes(p.read_bytes()+b'altered');check('altered copied proof',False);p.write_bytes(baseline['originals/AUTHOR-PROOF.md'])
p=F/'source/transfer.tex';p.unlink();check('missing copied source',False);p.write_bytes(baseline['source/transfer.tex'])
p=F/'unexpected';p.write_text('extra');check('unexpected file',False);p.unlink()
p=F/'unexpected-dir';p.mkdir();check('unexpected empty directory',False);p.rmdir()
check('wrong detached report anchor',False,dict(anchors,**{'REPORT.md':'0'*64}))
check('restored baseline',True)
assert baseline=={q.relative_to(F).as_posix():q.read_bytes() for q in F.rglob('*') if q.is_file()}
for src,rel in [(R/'private/incoming/H-SCOPE.md','originals/H-SCOPE.md'),(R/'private/incoming/AUTHOR-PROOF.md','originals/AUTHOR-PROOF.md'),(source,'source/transfer.tex')]:assert src.read_bytes()==baseline[rel]
(R/'controls-results.json').write_text(json.dumps({'cases':results,'fixture_baseline_restored':True,'copied_inputs_unchanged':True,'fixture_detached_anchors':anchors,'mathematical_gate':False},indent=2)+'\n');print(json.dumps({'cases':len(results),'negatives':sum(not x['expected_accept'] for x in results),'baseline_restored':True}))
