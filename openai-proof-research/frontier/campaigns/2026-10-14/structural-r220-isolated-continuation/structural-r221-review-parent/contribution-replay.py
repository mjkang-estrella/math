#!/usr/bin/env python3
"""Read-only parent replay of the settled contribution review."""
from pathlib import Path
import datetime,hashlib,json,os,runpy,stat,subprocess,sys,tempfile
P=Path(__file__).resolve().parent;W=P.parent;C=P.parents[1];PROJECT=C.parents[2];R=W/'structural-r221-contribution-r1';A=W/'fresh-structural-discovery-r221';D=W/'discovery-structural-r221-parent'
sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(p.read_bytes())
anchors={'FINAL.md':'48f597a13f9b145ebcba09a3ce4387b790b1941118bac14f250a7c7a4a5c65cb','MANIFEST.json':'eb33735a06f114e360744d55e555aed62ad32c1ba06025ec628bbd106d5f10c1','REPORT.md':'62af48e79e3f13512533026958039895ee5194ed707515111b6c92d0809a89e1'}
def inventory(root):
 assert root.is_dir() and not root.is_symlink();out={'files':{},'directories':{'':stat.S_IMODE(root.stat().st_mode)}}
 for base,dirs,files in os.walk(root,followlinks=False):
  for n in dirs+files:
   f=Path(base)/n;rel=f.relative_to(root).as_posix();s=f.lstat();assert not stat.S_ISLNK(s.st_mode)
   if stat.S_ISDIR(s.st_mode):out['directories'][rel]=stat.S_IMODE(s.st_mode)
   else:
    assert stat.S_ISREG(s.st_mode);b=f.read_bytes();out['files'][rel]={'bytes':len(b),'sha256':sha(b),'mode':stat.S_IMODE(s.st_mode)}
 return out
before=inventory(R);author=inventory(A)
assert author==read(D/'observed-root.json')==read(R/'private/author-baseline.json')
assert sha((R/'private/author-baseline.json').read_bytes())==read(R/'private/author-unchanged-after-reading.json')['author_baseline_sha256']
for n,h in anchors.items():assert before['files'][n]['sha256']==h
assert read(R/'ANCHORS.json')==anchors;m=read(R/'MANIFEST.json');outside={'MANIFEST.json','REPORT.md','ANCHORS.json'}
assert set(before['files'])=={x['path'] for x in m['files']}|outside
assert before['directories']=={x['path']:x['mode'] for x in m['directories']}
for x in m['files']:assert before['files'][x['path']]=={k:x[k] for k in ('bytes','sha256','mode')}
assert m['reviewed_frozen_sha256']==author['files']['FROZEN.md']['sha256']=='0031fe7106971855b2c1b98e3e1bc40574ed249ad8b17e9ac028d1f30bfae1ce'
def verify(root,vals):
 cmd=[sys.executable,'-I','-B',str(root/'verify_packet.py'),'--root',str(root),'--final-sha',vals['FINAL.md'],'--manifest-sha',vals['MANIFEST.json'],'--report-sha',vals['REPORT.md']]
 r=subprocess.run(cmd,capture_output=True,text=True);assert r.returncode==0,(r.stdout,r.stderr);return json.loads(r.stdout)
verifier=verify(R,anchors);author_verifier=verify(A,read(D/'intake.json')['artifact_replay']['anchors'])
tree_bytes=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tree_bytes)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=json.loads(tree_bytes);assert len(tree['tree'])==13223
auth=read(R/'private/source-binding.json');assert auth['pin']=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb' and auth['tree_sha256']==sha(tree_bytes)
prefix='preprints/Infinitely-many-closed-geodesic-images-on-every-Riemannian-sphere-September-24-2026';expected=[x for x in tree['tree'] if x['path'].startswith(prefix)];assert auth['selected']==expected
blobs=[x for x in expected if x['type']=='blob'];assert len(blobs)==17
for x in blobs:
 b=(A/'private/canonical'/x['path'][len(prefix)+1:]).read_bytes();assert len(b)==x['size'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['sha']
reads=[json.loads(x) for x in (R/'private/reads.jsonl').read_text().splitlines()]
for x in reads:
 b=((R/'private/primary/GS.txt') if x['file']=='@GS' else (A/x['file'])).read_bytes();lines=b.splitlines(keepends=True);i,j=x['lines'];lo,hi=x['bytes'];assert [sum(map(len,lines[:i-1])),sum(map(len,lines[:j]))]==[lo,hi] and sha(b[lo:hi])==x['sha256'];assert all(i<=z<=j for z in x['masked_lines'])
gs=read(R/'private/primary/GS-acquisition.json')
for suffix in ('pdf','txt'):
 data=(R/('private/primary/GS.'+suffix)).read_bytes();key='pdf' if suffix=='pdf' else 'text';assert len(data)==gs[key+'_bytes'] and sha(data)==gs[key+'_sha256']
namespace=runpy.run_path(str(R/'verify_packet.py'),run_name='parent_read_only_import');check=namespace['check_entries'];controls=[]
with tempfile.TemporaryDirectory(dir=P,prefix='contribution-copied-controls-') as td:
 root=Path(td);sample=root/'sample.txt';data=(R/'FINAL.md').read_bytes()[:192];sample.write_bytes(data);sample.chmod(0o644)
 fixture={'files':[{'path':'sample.txt','bytes':len(data),'sha256':sha(data),'mode':0o644}],'directories':[{'path':'','mode':stat.S_IMODE(root.stat().st_mode)}]}
 def case(label,reject=False):
  try:check(root,fixture,outside=set());ok=True
  except ValueError:ok=False
  assert ok!=reject,label;controls.append({'case':label,'observed':'rejected' if reject else 'accepted'})
 case('unaltered tiny copied payload');sample.write_bytes(bytes([data[0]^1])+data[1:]);case('same-size byte mutation',True);sample.write_bytes(data);sample.chmod(0o600);case('file mode mutation',True);sample.chmod(0o644);(root/'extra').write_text('x');case('extra file',True);(root/'extra').unlink();case('restored copied payload')
assert inventory(R)==before and inventory(A)==author
(P/'contribution-observed-root.json').write_text(json.dumps(before,indent=2)+'\n')
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'independent_selection_check':True,'selected_files':len(m['files']),'directories':len(m['directories']),'whole_review_files':len(before['files']),'whole_review_directories':len(before['directories']),'review_sha256':before['files']['REVIEW.md']['sha256'],'review_verifier_sha256':before['files']['verify_packet.py']['sha256'],'verifier':verifier,'canonical_blobs_authenticated':len(blobs),'read_extents_bound':len(reads),'new_primary_pdf_and_text_bound':True,'copied_controls':controls,'review_originals_unchanged':True,'author_files':len(author['files']),'author_directories':len(author['directories']),'author_baselines_agree':True,'author_originals_unchanged':True,'author_verifier':author_verifier,'semantic_scope':'Parent read complete REVIEW, FINAL, REPORT, reading/access limits prose, verifier and append-writing read helper. Identity checks do not inherit source/primary/visual reading. No contribution grade or count from artifact checks.'}
(P/'contribution-replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
