from pathlib import Path
import hashlib,json,sys,re
P=Path(__file__).resolve().parent;S=P.parent/'sol-steiner-gp-offline-citation-closure-r4'
sys.path.insert(0,str(S))
from offline_audit import blocks,parse
def sha(p):
 with Path(p).open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def check(r,p):assert Path(p).stat().st_size==r['bytes'] and sha(p)==r['sha256'],str(p)
m=json.loads((S/'final-manifest.json').read_text())
for r in m['files']:check(r,S/r['path'])
assert {r['path'] for r in m['files']}=={str(p.relative_to(S)) for p in S.rglob('*') if p.is_file() and str(p.relative_to(S)) not in m['exclusions']}
b=json.loads((S/'before.json').read_text())
for r in b['files']:check(r,r['path']);check(r,S/r['copy'])
for r in b['freezes']:assert sha(r['path'])==r['sha256']
oc=json.loads((S/'offlinecoverage.json').read_text());assert oc['decision']=='HOLD' and not oc['independent_complete_coverage_certificate']
R=S/'inputs/sol-steiner-gp-fixed-gap-closure-r3';count=0
for rec in oc['new_mail_delta_audit']:
 p=R/'retrieved/patches'/(rec['commit']+'.patch');actual=[parse(x) for x in blocks(p)];assert actual==rec['files'];count+=len(actual)
nb=nh=0
for rec in oc['retained_diff_census']:
 p=S/rec['file'];assert sha(p)==rec['sha256'];a=c=0
 with p.open('rb') as f:
  for l in f:a+=l.startswith(b'diff --git ');c+=l.startswith(b'@@ ')
 assert (a,c)==(rec['blocks'],rec['hunks']);nb+=a;nh+=c
assert (count,nb,nh)==(446,14133,14633)
assert len(b['files'])==617 and len(m['files'])==654
files=[{'path':str(p),'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(S.rglob('*')) if p.is_file()]
(P/'review-freeze.json').write_text(json.dumps({'files':files},indent=2)+'\n')
out={'status':'PASS','originals_and_copies':617,'manifest':654,'review_files':len(files),'mail_blocks':count,'diff_blocks':nb,'hunks':nh,'historical_clearance':'HOLD_PARKED','citations_10_19':'HOLD','credit':0}
(P/'verification-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
