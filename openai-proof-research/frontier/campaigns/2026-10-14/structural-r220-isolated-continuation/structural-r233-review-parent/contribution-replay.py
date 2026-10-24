#!/usr/bin/env python3
"""Read-only contribution intake with independent tiny copied artifact controls."""
from pathlib import Path
import datetime,gzip,hashlib,json,os,runpy,stat,tempfile
P=Path(__file__).resolve().parent;W=P.parent;R=W/'structural-r233-contribution-r1';A=W/'fresh-structural-discovery-r233';PROJECT=P.parents[3]
sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(p.read_bytes())
anchors={'FINAL.md':'a587d37dbea88a46af87e9638b59692c3b5833202abc62f60fb0f241beaf3b43','MANIFEST.json':'0e0f33e801c7770dce046d0f0e49ac23668fc39c5d2572652aeb6ebf387a1ec7','REPORT.md':'f28c44b5dfd1fb5c9267717fe7abb705237b99d3a6e86c6a2579c2d0806b15f8'}
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
baseline=read(R/'original-baseline.json');assert {e['path']:dict(bytes=e['bytes'],mode=int(e['mode'],8),sha256=e['sha256']) for e in baseline['entries']}==abefore['files']
assert sha((R/'original-baseline.json').read_bytes())==read(R/'SEAL-CHECK.json')['postseal_original_recheck']['baseline_sha256']
api=runpy.run_path(str(R/'verify_packet.py'));verified=api['verify'](R,*anchors.values());assert len(before['files'])==29
assert set(before['files'])==set(read(R/'selection.json')['files'])|{'FINAL.md','MANIFEST.json','REPORT.md','ANCHORS.json','SEAL-CHECK.json'}
assert sha((R/'REVIEW.md').read_bytes())=='9f5eaa9197727539be8c9af467051c49eab51e4d333e15002902fedd10caeb34'
g=read(R/'guard-installation.json');ag=read(A/'guards.json');assert set(g['wildcards'])==set(ag['wildcards']) and set(g['substrings'])==set(ag['substrings']);assert len(g['wildcards'])==389 and len(g['substrings'])==162
assert (R/'inherited-guards.json').read_bytes()==(A/'guards.json').read_bytes()
reads=[json.loads(x) for x in (R/'reads.jsonl').read_bytes().splitlines()];coverage={}
for x in reads:
 p=R/x['name'][4:] if x['name'].startswith('OWN/') else A/x['name'];b=p.read_bytes();lines=b.splitlines(keepends=True);lo,hi=x['lines']
 assert sha(b)==x['sha256'] and 1<=lo<=hi<=len(lines) and [sum(map(len,lines[:lo-1])),sum(map(len,lines[:hi]))]==x['bytes']
 coverage.setdefault(x['name'],set()).update(set(range(lo,hi+1))-set(x['masked_lines']))
for n,total in [('introduction.tex',258),('coordinates.tex',1166),('pinching.tex',1149),('renormalization.tex',839)]:assert coverage['private-source/build/source/'+n]==set(range(1,total+1))
assert coverage['author-proof.md']==set(range(1,252))-{1,3}
assert coverage['private-source/build/source/paper.tex']==set(range(1,58))-{1,6,39,42,55,56}
canon=read(R/'canonical-authentication.json');assert len(canon['entries'])==8
for e in canon['entries']:
 b=(A/e['local']).read_bytes();assert len(b)==e['bytes'] and sha(b)==e['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['sha1']
access=read(R/'private-primary/CN2/access.json');b=(R/'private-primary/CN2/source.bin').read_bytes();tex=(R/'private-primary/CN2/article.tex').read_bytes()
assert len(b)==access['bytes'] and sha(b)==access['sha256'] and gzip.decompress(b)==tex and len(tex)==access['text_bytes'] and sha(tex)==access['tex_sha256'] and len(tex.splitlines(keepends=True))==access['lines']
boundary_count=0
def check_markers(p,markers):
 global boundary_count
 lines=p.read_bytes().splitlines(keepends=True)
 for row in markers:
  i,start,end=row[:3];assert [sum(map(len,lines[:i-1])),sum(map(len,lines[:i]))]==[start,end];boundary_count+=1
for x in read(R/'source-boundaries.json').values():check_markers(A/x['name'],x['markers'])
for x in read(R/'primary-boundaries.json').values():check_markers(A/x['name'],x['markers'])
check_markers(A/'private-primary/DT12/article.tex',read(R/'dt-boundaries.json'));check_markers(R/'private-primary/CN2/article.tex',read(R/'cn2-boundaries.json'))
controls=[]
with tempfile.TemporaryDirectory(dir=P,prefix='contribution-copied-controls-') as td:
 root=Path(td);b=b'parent tiny copied control\n';(root/'sample.txt').write_bytes(b);(root/'verify_packet.py').write_bytes((R/'verify_packet.py').read_bytes());names=['sample.txt','selection.json','verify_packet.py'];(root/'selection.json').write_text(json.dumps({'files':names}))
 entries=[{'path':n,'bytes':(root/n).stat().st_size,'mode':'0444','sha256':sha((root/n).read_bytes())} for n in names];(root/'MANIFEST.json').write_text(json.dumps({'entries':entries}));(root/'FINAL.md').write_text('Manifest SHA256: '+sha((root/'MANIFEST.json').read_bytes())+'\nSelection SHA256: '+sha((root/'selection.json').read_bytes())+'\n');(root/'REPORT.md').write_text('Copied integrity control only.\n')
 exp={n:sha((root/n).read_bytes()) for n in anchors}
 for p in root.iterdir():p.chmod(0o444)
 def case(label,reject=False,override=None):
  try:api['verify'](root,*(override or exp).values())
  except AssertionError:assert reject;controls.append({'case':label,'observed':'rejected'})
  else:assert not reject;controls.append({'case':label,'observed':'accepted'})
 case('valid tiny copied packet');f=root/'sample.txt';f.chmod(0o644);f.write_bytes(bytes([b[0]^1])+b[1:]);f.chmod(0o444);case('same-size byte mutation',True)
 f.chmod(0o644);f.write_bytes(b);case('file-mode mutation',True);f.chmod(0o444)
 extra=root/'extra.txt';extra.write_bytes(b'x');extra.chmod(0o444);case('undeclared file',True);extra.unlink()
 extra_dir=root/'empty';extra_dir.mkdir();case('undeclared directory',True);extra_dir.rmdir()
 case('wrong detached anchor',True,dict(exp,**{'REPORT.md':'0'*64}));case('restored copied packet')
assert inventory(R)==before and inventory(A)==abefore
(P/'contribution-observed-root.json').write_text(json.dumps(before,indent=2)+'\n')
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'review_sha256':sha((R/'REVIEW.md').read_bytes()),'selected_manifest_entries':24,'review_total_files':29,'review_subdirectories':len(before['directories']),'review_verifier':verified,'admitted_original_files':53,'baseline_matches_parent':True,'inherited_guards_match':True,'reviewer_hashed_read_records':len(reads),'source_read_records':sum(x['name'].startswith('private-source/') for x in reads),'primary_read_records':sum('private-primary/' in x['name'] for x in reads),'canonical_blobs_bound':8,'additional_primary_container_and_tex_bound':1,'complete_source_tex_files':5,'boundary_offsets_verified':boundary_count,'reviewer_copied_controls':5,'independent_copied_controls':controls,'author_originals_unchanged':True,'review_originals_unchanged':True,'semantic_scope':'Parent read full REVIEW, working math, READING-LIMITS, SEAL-PROTOCOL, FINAL and REPORT without truncation. Byte/range/container binding is not additional primary/source semantic reading. Conditional contribution only; no correctness finding by reviewer, formal support, history clearance or exhaustive literature conclusion.'}
(P/'contribution-replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
