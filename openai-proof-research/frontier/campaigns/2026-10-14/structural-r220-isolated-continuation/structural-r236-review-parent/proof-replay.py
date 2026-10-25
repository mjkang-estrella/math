#!/usr/bin/env python3
"""Read-only replay of the S236 correctness packet; outputs only in parent root."""
from pathlib import Path
import datetime,hashlib,json,os,runpy,shutil,stat,tempfile
P=Path(__file__).resolve().parent;W=P.parent;C=P.parents[1];PROJECT=C.parents[2]
R=W/'structural-r236-proof-r1';A=W/'fresh-structural-discovery-r236'
sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(p.read_bytes())
anchors={'FINAL.md':'3fe1e9d928ae563eda7c79920ccf12553e83b181e709df8f95fdf222e521bbce','MANIFEST.json':'1aa6fbbb962630d541f30c7fa58c695f847afb26a632d06d4082dd8ae6edab27','REPORT.md':'78091238a390b141c9e0191676904010ab9c3526fbe6365a3d8e9646a6f0af08','SELECTION.json':'50835dcc89068232a3deb8046d317c4121bd929ed87b3d5d5be7312c5c57f258'}
def inventory(root):
 assert not root.is_symlink();out={'root_mode':stat.S_IMODE(root.stat().st_mode),'files':{},'directories':{}}
 for base,ds,fs in os.walk(root,followlinks=False):
  for name in ds+fs:
   p=Path(base)/name;s=p.lstat();rel=p.relative_to(root).as_posix();assert not stat.S_ISLNK(s.st_mode)
   if stat.S_ISDIR(s.st_mode):out['directories'][rel]=stat.S_IMODE(s.st_mode)
   else:
    assert stat.S_ISREG(s.st_mode);b=p.read_bytes();out['files'][rel]={'bytes':len(b),'sha256':sha(b),'mode':stat.S_IMODE(s.st_mode)}
 return out
before=inventory(R);abefore=inventory(A)
assert abefore==read(W/'discovery-structural-r236-parent/observed-root.json')
assert len(abefore['files'])==114 and len(before['files'])==30
assert set(before['files'])==set(read(R/'SELECTION.json')['paths'])|{'MANIFEST.json','REPORT.md','ANCHORS.json','SEAL-VERIFICATION.json'}
assert sha((R/'verify_packet.py').read_bytes())==sha((A/'verify_packet.py').read_bytes())=='5787dedceac55f5b66b247bec0fb552497f2f4ff9ec8dd9c7426a4d4d0eacad8'
verify=runpy.run_path(str(R/'verify_packet.py'))['verify']
def args(x):return [x['MANIFEST.json'],x['FINAL.md'],'SELECTION.json',x['SELECTION.json'],x['REPORT.md']]
verified=verify(R,*args(anchors));assert verified['selected_files']==26
assert all(read(R/'ANCHORS.json')[k]==v for k,v in anchors.items())
for name in ['REVIEW.md','READING-LIMITS.md']:assert sha((R/name).read_bytes())==read(R/'ANCHORS.json')[name]
author_anchors=read(W/'discovery-structural-r236-parent/replay.json')['anchors'];averified=verify(A,*args(author_anchors));assert averified['selected_files']==102
baseline=read(R/'private/author-baseline.json');rows={x['path']:x for x in baseline['entries']}
assert baseline['root']==A.relative_to(PROJECT).as_posix()
assert len(rows)==106 and set(rows)==set(read(A/'SELECTION.json')['paths'])|{'MANIFEST.json','REPORT.md','ANCHORS.json','SEAL-VERIFICATION.json'}
assert {k:dict(bytes=x['bytes'],sha256=x['sha256'],mode=int(x['mode'],8)) for k,x in rows.items()}=={k:abefore['files'][k] for k in rows}
assert sha((R/'private/author-baseline.json').read_bytes())==read(R/'SEAL-VERIFICATION.json')['originals_recheck']['baseline_sha256']
g=read(R/'private/guards.json');ag=read(A/'private/guards.json')
assert set(g['wildcards'])==set(ag['wildcards']) and set(g['substrings'])==set(ag['substrings']);assert len(g['wildcards'])==395 and len(g['substrings'])==162
treebytes=(PROJECT/'sources/preprints-tree.json').read_bytes();tree=json.loads(treebytes)['tree'];auth=read(R/'private/canonical-authentication.json')
assert sha(treebytes)==auth['tree_sha256']=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b' and len(tree)==13223
assert auth['pin']=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb';by={x['path']:x for x in tree};assert len(auth['blobs'])==28
for x in auth['blobs']:
 assert x['local'] in rows;b=(A/x['local']).read_bytes();e=by[x['canonical']]
 assert len(b)==e['size'] and sha(b)==x['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['sha']==x['git_blob']
reads=[json.loads(x) for x in (R/'private/read-log.jsonl').read_bytes().splitlines()];coverage={}
for x in reads:
 assert x['file'] in rows;b=(A/x['file']).read_bytes();lines=b.splitlines(keepends=True);lo,hi=x['lines_inclusive']
 assert 1<=lo<=hi<=len(lines) and [sum(map(len,lines[:lo-1])),sum(map(len,lines[:hi]))]==x['bytes_half_open']
 coverage.setdefault(x['file'],set()).update(range(lo,hi+1))
reported=read(R/'private/read-coverage.json')['inclusive_line_ranges'];assert set(reported)==set(coverage)
for name,spans in reported.items():assert coverage[name]==set(i for lo,hi in spans for i in range(lo,hi+1))
full=[]
for x in auth['blobs']:
 name=x['local']
 if name.endswith('.tex') and not name.endswith('/build/paper.tex'):
  assert coverage[name]==set(range(1,len((A/name).read_bytes().splitlines(keepends=True))+1));full.append(name)
assert len(full)==19
visual=read(R/'private/visual-reads.json')['images'];assert len(visual)==5
for x in visual:assert x['path'] in rows and sha((A/x['path']).read_bytes())==x['sha256']
# Validate metadata coordinates without displaying protected source/history text.
boundary_counts={}
for meta in ['source-boundaries','primary-boundaries','history-selected-boundaries']:
 items=read(R/('private/'+meta+'.json'));boundary_counts[meta]=len(items)
 for x in items:
  assert x['file'] in rows;lines=(A/x['file']).read_bytes().splitlines(keepends=True);assert len(lines)==x['lines']
  for h in x['headings']:assert 1<=h[0]<=len(lines)
controls=[];tiny=R/'private/controls/tiny';tiny_anchors={n:sha((tiny/n).read_bytes()) for n in anchors}
assert verify(tiny,*args(tiny_anchors))['selected_files']==3
with tempfile.TemporaryDirectory(dir=P,prefix='proof-copied-controls-') as td:
 root=Path(td)/'tiny';shutil.copytree(tiny,root,copy_function=shutil.copy2);f=root/'payload.txt';payload=f.read_bytes();mode=stat.S_IMODE(f.stat().st_mode)
 def case(label,expected=tiny_anchors,reject=False):
  try:verify(root,*args(expected));failed=False
  except ValueError:failed=True
  assert failed==reject;controls.append({'case':label,'observed':'rejected' if reject else 'accepted'})
 case('intact copied tiny selection');f.chmod(0o600);f.write_bytes(bytes([payload[0]^1])+payload[1:]);f.chmod(mode);case('same-size selected byte mutation',reject=True)
 f.chmod(0o600);f.write_bytes(payload);case('selected mode mutation',reject=True);f.chmod(mode)
 selection=root/'SELECTION.json';sb=selection.read_bytes();selection.chmod(0o600);d=json.loads(sb);d['paths'].remove('payload.txt');selection.write_text(json.dumps(d)+'\n');selection.chmod(0o400)
 reduced=dict(tiny_anchors,**{'SELECTION.json':sha(selection.read_bytes())});case('reduced selection against unchanged fixture manifest',reduced,True)
 selection.chmod(0o600);selection.write_bytes(sb);selection.chmod(0o400);case('restored copied selection')
 case('wrong detached report anchor',dict(tiny_anchors,**{'REPORT.md':'0'*64}),True)
assert inventory(R)==before and inventory(A)==abefore
(P/'proof-observed-root.json').write_text(json.dumps(before,indent=2)+'\n')
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'review_sha256':sha((R/'REVIEW.md').read_bytes()),'statement_sha256':rows['STATEMENT.md']['sha256'],'author_proof_sha256':rows['AUTHOR-PROOF.md']['sha256'],'selected_review_files':26,'entire_review_files':30,'review_subdirectories':len(before['directories']),'review_verifier':verified,'author_verifier':averified,'admitted_author_files_unchanged':106,'entire_author_files_unchanged':114,'entire_author_subdirectories_unchanged':12,'inherited_guards_match':True,'canonical_blobs_authenticated':28,'reviewer_read_ranges_baseline_bound':len(reads),'complete_non_driver_operative_tex_extents':len(full),'reviewer_visual_identities_bound':len(visual),'boundary_metadata_file_counts':boundary_counts,'reviewer_copied_controls':len(read(R/'private/control-results.json')['results']),'independent_copied_controls':controls,'author_originals_unchanged':True,'review_originals_unchanged':True,'verifier_scope':'Exact explicit file selection, bytes, modes and detached anchors; directories and unselected extras are not bound by this verifier. Parent independently compares full observed roots.','semantic_scope':'Parent read complete REVIEW, derivations, READING-LIMITS, FINAL, REPORT and access incidents; independently checked the unchanged statement and proof. Parent combined reread output was truncated and recovered with bounded proof reads. Byte/line/visual identity checks do not inherit reviewer semantic or visual reading. Comparison limitations, editorial exposures and late reads remain disclosed; no history clearance, formal support or contribution verdict.'}
out['replay_schema_diagnostics']='Initial guard-array order assertion stopped before controls; arrays were confirmed reordered with identical 395 unique wildcard and 162 unique substring sets. Set comparison then passed. No originals changed.'
(P/'proof-replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
