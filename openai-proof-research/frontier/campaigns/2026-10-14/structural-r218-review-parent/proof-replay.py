#!/usr/bin/env python3
"""Replay the completed correctness packet without altering either original."""
from pathlib import Path
import datetime,hashlib,json,os,stat,subprocess,sys,tempfile
P=Path(__file__).resolve().parent; C=P.parent; PROJECT=C.parents[2]
R=C/'structural-r218-proof-r1'; A=C/'fresh-structural-discovery-r218'
read=lambda p:json.loads(p.read_bytes()); sha=lambda b:hashlib.sha256(b).hexdigest()
anchors={'FINAL':'fd994d6dadf799c4ebfa5edb10046fbbb3598e1d573af458325708c74d7661ae','MANIFEST':'c4c1ba4def2f213c0e5ba9a622931783fe5b69e8769e8e5a0e438310bf96b907','REPORT':'94c25a6378d8341fa368738019f193e5aa3744d413e1df58b5bbe46e15eeaf80'}
def snapshot(root):
 out={'files':{},'directories':{}}
 for base,ds,fs in os.walk(root,followlinks=False):
  b=Path(base);out['directories'][b.relative_to(root).as_posix()]=oct(stat.S_IMODE(b.stat().st_mode))
  for n in ds+fs:assert not (b/n).is_symlink()
  for n in fs:
   f=b/n;out['files'][f.relative_to(root).as_posix()]={'bytes':f.stat().st_size,'sha256':sha(f.read_bytes()),'mode':oct(stat.S_IMODE(f.stat().st_mode))}
 return out
before=snapshot(R);author_before=snapshot(A)
assert author_before==read(C/'discovery-structural-r218-parent/observed-root.json')
verifier=R/'verify_packet.py';assert sha(verifier.read_bytes())=='4e4748497589cbb22dc8c5457dd45391e8d14f06709463aaa1a146a42eb59e98'
def run(root,an):
 return subprocess.run([sys.executable,'-I','-B',str(verifier),'--root',str(root),'--final-sha',an['FINAL'],'--manifest-sha',an['MANIFEST'],'--report-sha',an['REPORT']],capture_output=True,text=True)
v=run(R,anchors);assert v.returncode==0,v.stderr;verified=json.loads(v.stdout);assert (verified['files'],verified['directories'])==(56,15)
ab=read(R/'private/author-before.json');aa=read(R/'private/author-after.json');assert ab==aa and len(ab['files'])==88 and len(ab['directories'])==16
assert stat.S_IMODE(A.stat().st_mode)==int(ab['root_mode'],8)
for n,e in ab['files'].items():
 f=A/n;assert f.stat().st_size==e['bytes'] and sha(f.read_bytes())==e['sha256'] and stat.S_IMODE(f.stat().st_mode)==int(e['mode'],8)
for n,mode in ab['directories'].items():assert stat.S_IMODE((A/n).stat().st_mode)==int(mode,8)
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree={x['path']:x for x in json.loads(tb)['tree']}
canonical=read(R/'private/retrieved-canonical.json');other=read(R/'private/companion-comparator-retrieval.json')
for x in canonical+other:
 b=(R/'private/retrieved'/x['path']).read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256'] and b==(A/'private/canonical'/x['path']).read_bytes()
 if x['path'].startswith('preprints/'):
  h=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert h==tree[x['path']]['sha'] and len(b)==tree[x['path']]['size']
reads=[]
for line in (R/'private/read-selections.jsonl').read_text().splitlines():
 x=json.loads(line);f=A/x['path']
 if not f.is_file():f=R/x['path']
 assert f.is_file();b=f.read_bytes();lo,hi=x['bytes_half_open'];assert 0<=lo<hi<=len(b)
 lines=b.splitlines(keepends=True);start,end=x['lines_inclusive'];assert [sum(map(len,lines[:start-1])),sum(map(len,lines[:end]))]==[lo,hi]
 if 'sha256' in x:assert sha(b)==x['sha256']  # read_selected.py records whole-file identity, not range hash
 excluded=set(x.get('exclude_lines',[]));selected=b''.join(lines[i-1] for i in range(start,end+1) if i not in excluded)
 reads.append(dict(x,bound_whole_file_sha256=sha(b),bound_selected_sha256=sha(selected)))
primary=read(R/'private/primary-selections.json');primary_bindings=[]
for name,ranges in primary['ranges'].items():
 b=(A/'private/primary'/(name+'.txt')).read_bytes();lines=b.splitlines(keepends=True);excluded=set(primary['exclude_lines'].get(name,[]))
 for lo,hi in ranges:
  assert 1<=lo<=hi<=len(lines);selected=b''.join(lines[i-1] for i in range(lo,hi+1) if i not in excluded)
  primary_bindings.append({'name':name,'lines':[lo,hi],'selected_sha256':sha(selected)})
controls=[]
for case in ['intact','wrong-anchor','changed-bytes','extra-file','missing-file','file-mode','directory-mode','root-mode']:
 with tempfile.TemporaryDirectory(prefix='proof218-tiny-',dir=P) as td:
  root=Path(td);(root/'d').mkdir(mode=0o700);(root/'FINAL.md').write_bytes(b'final\n');(root/'d/item.txt').write_bytes(b'payload\n');(root/'REPORT.md').write_bytes(b'outside report\n')
  for f in [root/'FINAL.md',root/'d/item.txt',root/'REPORT.md']:f.chmod(0o444)
  mm={'format':'structural218-proof-r1-exact-v1','root_mode':'0700','files':{n:{'bytes':(root/n).stat().st_size,'sha256':sha((root/n).read_bytes()),'mode':'0444'} for n in ['FINAL.md','d/item.txt']},'directories':{'d':'0700'}}
  (root/'MANIFEST.json').write_text(json.dumps(mm));(root/'MANIFEST.json').chmod(0o444)
  an={k:sha((root/(k+'.md' if k!='MANIFEST' else 'MANIFEST.json')).read_bytes()) for k in anchors}
  if case=='wrong-anchor':an['FINAL']='0'*64
  elif case=='changed-bytes':(root/'d/item.txt').chmod(0o644);(root/'d/item.txt').write_bytes(b'changed\n');(root/'d/item.txt').chmod(0o444)
  elif case=='extra-file':(root/'extra.txt').write_bytes(b'x')
  elif case=='missing-file':(root/'d/item.txt').unlink()
  elif case=='file-mode':(root/'d/item.txt').chmod(0o644)
  elif case=='directory-mode':(root/'d').chmod(0o750)
  elif case=='root-mode':root.chmod(0o750)
  accepted=run(root,an).returncode==0;assert accepted==(case=='intact');controls.append({'case':case,'accepted':accepted,'expected':case=='intact'})
assert snapshot(R)==before and snapshot(A)==author_before
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'verifier_sha256':sha(verifier.read_bytes()),'verification':verified,'review_root_files':len(before['files']),'review_root_directories_including_root':len(before['directories']),'review_originals_bytes_modes_unchanged':True,'whole_author_root_unchanged_since_parent_intake':True,'whole_author_root_files':len(author_before['files']),'reviewer_admitted_author_files':88,'reviewer_admitted_author_subdirectories':16,'reviewer_before_after_matches_actual_author':True,'canonical_source_bindings':len(canonical),'companion_and_comparator_bindings':len(other),'read_extent_bindings':len(reads),'primary_selection_bindings':len(primary_bindings),'copied_controls':controls,'formal_coverage':'Reviewer reports direct full reading of the pinned linked comparator ending in sorry; no formal support or compilation.','parent_read_limits':'Parent read complete REVIEW, FINAL, REPORT, private READING-LIMITS, initial-math, recoveries-and-exposures, preservation/validation reports and verifier. Combined initial output truncated the middle of REVIEW; bytes [9000,24743) were then recovered in full. Canonical/primary/comparator bodies and read extents identity-bound only, without inherited semantic reading. No peer or contribution review lookup.'}
out['parent_replay_schema_recovery']='Initial replay assumed each read-log sha256 was a contiguous-range digest. Inspection of the authored helper established whole-file digests and unhashed primary records with excluded lines; corrected replay validates whole-file identity, exact byte/line offsets, and independently binds actual selected bytes. No original was changed and no packet-anchor mismatch occurred.'
for name,obj in [('proof-replay.json',out),('proof-observed-root.json',before),('proof-primary-bindings.json',primary_bindings),('proof-read-bindings.json',reads)]:
 f=P/name;f.write_text(json.dumps(obj,indent=2)+'\n');f.chmod(0o600)
print(json.dumps(out,indent=2))
