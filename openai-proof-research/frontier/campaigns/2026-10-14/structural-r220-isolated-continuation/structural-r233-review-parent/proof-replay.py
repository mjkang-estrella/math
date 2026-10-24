#!/usr/bin/env python3
"""Read-only replay of the independent r233 correctness packet and original baseline."""
from pathlib import Path
import datetime,hashlib,json,os,runpy,stat,tempfile
P=Path(__file__).resolve().parent;W=P.parent;R=W/'structural-r233-proof-r1';A=W/'fresh-structural-discovery-r233'
sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(p.read_bytes())
anchors={'FINAL.md':'f27b65f9889346f58b5d8227b8645ae19885360a24d41347c3d1779c02ee036d','MANIFEST.json':'8595d0e59d874c7fa979e51f1e2c36c72a7de9edff3f86368ad5c35ea9de7e26','REPORT.md':'49a32965e2a11f75bdfdfa3df41c413d9747085947b4165667e86bf6228ef2f3'}
def inventory(root):
 out={'files':{},'directories':{},'root_mode':stat.S_IMODE(root.stat().st_mode)}
 for d,ds,fs in os.walk(root,followlinks=False):
  for n in ds+fs:
   p=Path(d)/n;s=p.lstat();rel=p.relative_to(root).as_posix();assert not stat.S_ISLNK(s.st_mode)
   if stat.S_ISDIR(s.st_mode):out['directories'][rel]=stat.S_IMODE(s.st_mode)
   else:
    assert stat.S_ISREG(s.st_mode);b=p.read_bytes();out['files'][rel]={'bytes':len(b),'mode':stat.S_IMODE(s.st_mode),'sha256':sha(b)}
 return out
before=inventory(R);abefore=inventory(A);assert abefore==read(W/'discovery-structural-r233-parent/observed-root.json')
baseline=read(R/'author-baseline.json');assert baseline['directories']==len(abefore['directories'])==12
assert {x['path']:dict(bytes=x['bytes'],mode=int(x['mode'],8),sha256=x['sha256']) for x in baseline['files']}==abefore['files']
api=runpy.run_path(str(R/'verify_packet.py'));verified=api['verify'](R,anchors)
assert len(before['files'])==len(read(R/'MANIFEST.json')['entries'])+5==24
assert sha((R/'REVIEW.md').read_bytes())=='bed8f9913f9c1b583e86ad5f19388eeb647c8e1781a626b5ee876d9ac54d532a'
original_check=runpy.run_path(str(R/'check_author.py'))['check']();assert original_check==read(R/'SEAL-CHECK.json')['author_originals']
author_api=runpy.run_path(str(A/'verify_packet.py'));author_verified=author_api['verify_packet'](A,read(A/'ANCHORS.json'))
g=read(R/'guards.json');ag=read(A/'guards.json');assert set(g['wildcards'])==set(ag['wildcards']) and set(g['substrings'])==set(ag['substrings']);assert len(g['wildcards'])==389 and len(g['substrings'])==162
reads=[json.loads(x) for x in (R/'semantic-reads.jsonl').read_bytes().splitlines()];coverage={}
for x in reads:
 b=(A/x['name']).read_bytes();lines=b.splitlines(keepends=True);lo,hi=x['lines']
 assert 1<=lo<=hi<=len(lines)
 if 'sha256' in x:
  assert sha(b)==x['sha256'] and [sum(map(len,lines[:lo-1])),sum(map(len,lines[:hi]))]==x['bytes']
 else:
  assert x['name']=='private-source/build/source/paper.tex' and x['lines']==[1,57] and x['masked_lines']==[[37,42],[55,57]]
  assert sha(b)==abefore['files'][x['name']]['sha256']
 coverage.setdefault(x['name'],set()).update(range(lo,hi+1))
for n,total in [('introduction.tex',258),('coordinates.tex',1166),('pinching.tex',1149),('renormalization.tex',839)]:
 assert coverage['private-source/build/source/'+n]==set(range(1,total+1))
assert set(range(1,58))==coverage['private-source/build/source/paper.tex']
boundary_count=0
for name,x in read(R/'primary-boundary-classification.json').items():
 b=(A/'private-primary'/name/'article.tex').read_bytes();lines=b.splitlines(keepends=True);assert len(b)==x['bytes'] and len(lines)==x['lines']
 for m in x['markers']:
  i=m['line'];assert [sum(map(len,lines[:i-1])),sum(map(len,lines[:i]))]==m['bytes'];boundary_count+=1
assert 1358 not in coverage['private-primary/MN19/article.tex']
controls=[]
with tempfile.TemporaryDirectory(dir=P,prefix='proof-copied-controls-') as td:
 root=Path(td);f=root/'sample.txt';b=b'parent independent copied control\n';f.write_bytes(b);f.chmod(0o444);entries=[{'path':'sample.txt','bytes':len(b),'sha256':sha(b),'mode':'0444'}]
 def case(name,fn,reject=False):
  try:fn()
  except ValueError:assert reject;controls.append({'case':name,'observed':'rejected'})
  else:assert not reject;controls.append({'case':name,'observed':'accepted'})
 payload=lambda:api['verify_payload'](root,entries,['sample.txt'])
 case('valid copied payload',payload);case('valid copied surface',lambda:api['verify_surface'](root,['sample.txt']))
 f.chmod(0o644);f.write_bytes(bytes([b[0]^1])+b[1:]);f.chmod(0o444);case('same-size byte mutation',payload,True)
 f.chmod(0o644);f.write_bytes(b);case('mode mutation',payload,True);f.chmod(0o444)
 case('selection omission',lambda:api['verify_payload'](root,entries,[]),True)
 extra=root/'extra.txt';extra.write_bytes(b'x');case('undeclared file',lambda:api['verify_surface'](root,['sample.txt']),True);extra.unlink()
 case('restored copied payload',payload)
assert inventory(R)==before and inventory(A)==abefore
(P/'proof-observed-root.json').write_text(json.dumps(before,indent=2)+'\n')
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'review_sha256':sha((R/'REVIEW.md').read_bytes()),'selected_manifest_entries':19,'review_total_files':24,'review_subdirectories':len(before['directories']),'review_verifier':verified,'author_verifier':author_verified,'original_baseline':original_check,'inherited_guards_match':True,'reviewer_read_records':len(reads),'hashed_byte_range_records':32,'driver_line_only_record_bound_to_baseline':1,'source_read_extents_bound':sum(x['name'].startswith('private-source/') for x in reads),'primary_read_extents_bound':sum(x['name'].startswith('private-primary/') for x in reads),'complete_operative_tex_extents':5,'primary_boundary_offsets_verified':boundary_count,'reviewer_copied_controls':len(read(R/'artifact-controls.json')['tests']),'independent_copied_controls':controls,'author_originals_unchanged':True,'review_originals_unchanged':True,'replay_schema_diagnostics':'Initial strict list-order comparison found reordered but identical guard sets; one driver read record has line/mask coordinates without its own byte/hash fields, so it was separately bound to the authenticated author baseline. No originals changed.','semantic_scope':'Parent read full REVIEW, working analysis, READING-LIMITS, FINAL and REPORT without truncation. Artifact/range checks do not transfer independent primary/source semantic coverage. Reviewer source proofs are stipulated true; review analyses new deductions. No contribution verdict, formal support or history clearance.'}
(P/'proof-replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
