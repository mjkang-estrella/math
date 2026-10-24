#!/usr/bin/env python3
"""Read-only contribution packet replay and author-preservation verification."""
from pathlib import Path
import datetime,hashlib,json,os,stat,subprocess,sys,tempfile
P=Path(__file__).resolve().parent;C=P.parent;PROJECT=C.parents[2];R=C/'structural-r218-contribution-r1';A=C/'fresh-structural-discovery-r218'
read=lambda p:json.loads(p.read_bytes());sha=lambda b:hashlib.sha256(b).hexdigest()
anchors={'FINAL':'549d18ee555ae4c4e64c70f540fc2cb2302fffad844adae3e1f1b59a0b1c2cf8','MANIFEST':'cc139cbf0223c280000ccc2f6fa9ef42dfbc970ac2ff894e14dc6fab9bfa7b44','REPORT':'06a54acae2daaa83afc7759eb2c04e2c5ed0c8c4ad1fb5f5c7000235c18201bb'}
def snapshot(root):
 out={'files':{},'directories':{}}
 for base,ds,fs in os.walk(root,followlinks=False):
  b=Path(base);out['directories'][b.relative_to(root).as_posix()]=oct(stat.S_IMODE(b.stat().st_mode))
  for n in ds+fs:assert not (b/n).is_symlink()
  for n in fs:
   f=b/n;out['files'][f.relative_to(root).as_posix()]={'bytes':f.stat().st_size,'sha256':sha(f.read_bytes()),'mode':oct(stat.S_IMODE(f.stat().st_mode))}
 return out
before=snapshot(R);author_before=snapshot(A);assert author_before==read(C/'discovery-structural-r218-parent/observed-root.json')
verifier=R/'verify_packet.py';assert sha(verifier.read_bytes())=='4fc6c32c7350e694b8075393a5336e2773cdf87d0a451f7464c55453dcdc78c1'
def run(root,an):return subprocess.run([sys.executable,'-I','-B',str(verifier),'--root',str(root),'--final-sha',an['FINAL'],'--manifest-sha',an['MANIFEST'],'--report-sha',an['REPORT']],capture_output=True,text=True)
v=run(R,anchors);assert v.returncode==0,v.stderr;m=read(R/'MANIFEST.json');assert (len(m['files']),len(m['directories']))==(55,19)
ab=read(R/'private/author-selected-before.json');initial=read(R/'private/author-before.json');assert len(ab['files'])==85 and len(ab['directories'])==16
def bind(f,e):assert f.stat().st_size==e['bytes'] and sha(f.read_bytes())==e['sha256'] and stat.S_IMODE(f.stat().st_mode)==int(e['mode'],8)
for n,e in ab['files'].items():bind(A/n,e)
for n,mode in ab['directories'].items():assert stat.S_IMODE((A/n).stat().st_mode)==int(mode,8)
for n,e in initial['anchors'].items():bind(A/n,e)
bind(A/'ANCHORS.json',read(R/'private/author-anchors-observed.json'))
assert stat.S_IMODE(A.stat().st_mode)==int(ab['root_mode'],8)==int(initial['root_mode'],8)
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree={x['path']:x for x in json.loads(tb)['tree']}
sources=read(R/'private/independent-authentication.json');companions=read(R/'private/companion-authentication.json');lean=read(R/'private/lean-authentication.json')
for group in [sources,companions,lean]:
 for x in group:
  path=x['path'];path=path if path.startswith(('preprints/','lean/')) else 'preprints/'+path
  b=(R/'private/independent'/path).read_bytes();h=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
  assert len(b)==x['bytes'] and sha(b)==x['sha256'] and h==x['git_blob']
  if path.startswith('preprints/'):assert h==tree[path]['sha'] and len(b)==tree[path]['size']
  other=A/'private/canonical'/path
  if other.exists():assert b==other.read_bytes()
seidel=read(R/'private/primary/access.json');b=(R/'private/primary/Seidel2003v3.pdf').read_bytes();assert len(b)==seidel['pdf_bytes'] and sha(b)==seidel['sha256'];assert (R/'private/primary/Seidel2003v3.txt').stat().st_size==seidel['text_bytes']
versions=read(R/'private/primary-versions.json')
for x in versions:
 b=(A/x['path']).read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256']
read_bindings=[];headers=0
for line in (R/'private/reads.jsonl').read_text().splitlines():
 x=json.loads(line);f=PROJECT/x['path'];assert f.is_relative_to(A) or f.is_relative_to(R)
 b=f.read_bytes();lines=b.splitlines(keepends=True);offsets=[0]
 for row in lines:offsets.append(offsets[-1]+len(row))
 if 'running_headers_excluded' in x:
  for n,lo,hi in x['running_headers_excluded']:assert offsets[n-1:n+1]==[lo,hi]
  headers+=1;continue
 lo,hi=x['bytes'];start,end=x['lines'];assert sha(b)==x['sha256'] and [offsets[start-1],offsets[end]]==[lo,hi]
 read_bindings.append(dict(x,range_sha256=sha(b[lo:hi])))
controls=[]
for case in ['intact','wrong-anchor','changed-bytes','extra-file','missing-file','file-mode','directory-mode','root-mode']:
 with tempfile.TemporaryDirectory(prefix='contribution218-tiny-',dir=P) as td:
  root=Path(td);(root/'d').mkdir(mode=0o700);(root/'FINAL.md').write_bytes(b'final\n');(root/'d/item.txt').write_bytes(b'payload\n');(root/'REPORT.md').write_bytes(b'outside report\n')
  for f in [root/'FINAL.md',root/'d/item.txt',root/'REPORT.md']:f.chmod(0o444)
  mm={'root_mode':'0700','files':{n:{'bytes':(root/n).stat().st_size,'sha256':sha((root/n).read_bytes()),'mode':'0444'} for n in ['FINAL.md','d/item.txt']},'directories':{'d':'0700'}}
  (root/'MANIFEST.json').write_text(json.dumps(mm));an={k:sha((root/(k+'.md' if k!='MANIFEST' else 'MANIFEST.json')).read_bytes()) for k in anchors}
  if case=='wrong-anchor':an['FINAL']='0'*64
  elif case=='changed-bytes':(root/'d/item.txt').chmod(0o644);(root/'d/item.txt').write_bytes(b'changed\n');(root/'d/item.txt').chmod(0o444)
  elif case=='extra-file':(root/'extra.txt').write_bytes(b'x')
  elif case=='missing-file':(root/'d/item.txt').unlink()
  elif case=='file-mode':(root/'d/item.txt').chmod(0o644)
  elif case=='directory-mode':(root/'d').chmod(0o750)
  elif case=='root-mode':root.chmod(0o750)
  accepted=run(root,an).returncode==0;assert accepted==(case=='intact');controls.append({'case':case,'accepted':accepted,'expected':case=='intact'})
assert snapshot(R)==before and snapshot(A)==author_before
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'verifier_sha256':sha(verifier.read_bytes()),'verification':{'files':55,'directories_excluding_root':19,'root_mode':'0700','stdout':v.stdout.strip()},'review_root_files':len(before['files']),'review_root_directories_including_root':len(before['directories']),'review_originals_bytes_modes_unchanged':True,'whole_author_root_unchanged_since_parent_intake':True,'whole_author_root_files':len(author_before['files']),'reviewer_selected_author_files':85,'reviewer_selected_author_subdirectories':16,'reviewer_late_ANCHORS_baseline_preserved':True,'parent_original_ANCHORS_baseline_preserved':True,'canonical_source_bindings':len(sources),'companion_bindings':len(companions),'lean_bindings':len(lean),'independent_primary_pdf_bindings':1,'author_primary_version_bindings':len(versions),'read_extent_bindings':len(read_bindings),'running_header_records_bound':headers,'copied_controls':controls,'formal_coverage':'Linked comparator reported read fully and ends in sorry; no formal support or compilation.','parent_read_limits':'Full REVIEW, REDUCTION, FINAL, REPORT, private READING-LIMITS, verifier and review_io read. Underlying canonical/primary/comparator/history bodies identity-bound only, no inherited semantic reading or exhaustive clearance. Reviewer late first observation of author ANCHORS remains explicit; parent independently confirms its original pre-review baseline.'}
for name,obj in [('contribution-replay.json',out),('contribution-observed-root.json',before),('contribution-read-bindings.json',read_bindings)]:
 f=P/name;f.write_text(json.dumps(obj,indent=2)+'\n');f.chmod(0o600)
print(json.dumps(out,indent=2))
