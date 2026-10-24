#!/usr/bin/env python3
"""Read-only correctness-review replay. Mutations and arithmetic run only on tiny copies."""
from pathlib import Path
import datetime,hashlib,json,os,shutil,stat,subprocess,sys,tempfile
P=Path(__file__).resolve().parent;W=P.parent;C=P.parents[1];PROJECT=C.parents[2];R=W/'structural-r232-proof-r1';S=R/'selected';A=W/'fresh-structural-discovery-r232'
sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(p.read_bytes())
anchors={'FINAL.md':'8723fe4dc6d467ce9a12931928b39d1be488f4c24446ab0a6a4887f547553ac5','MANIFEST.json':'0a6aacab6ff67d6cf6182682eeff119ef10416a84faaf72706fcbb8d2b436618','REPORT.md':'609ea59784856cc24208fceb36c3201c4ec6138bd2bf4aadade9b3deb4275269'}
def inventory(root):
 out={'files':{},'directories':{},'root_mode':stat.S_IMODE(root.stat().st_mode)}
 for base,ds,fs in os.walk(root,followlinks=False):
  for n in ds+fs:
   p=Path(base)/n;rel=p.relative_to(root).as_posix();st=p.lstat();assert not stat.S_ISLNK(st.st_mode)
   if stat.S_ISDIR(st.st_mode):out['directories'][rel]=stat.S_IMODE(st.st_mode)
   else:
    assert stat.S_ISREG(st.st_mode);b=p.read_bytes();out['files'][rel]={'bytes':len(b),'sha256':sha(b),'mode':stat.S_IMODE(st.st_mode)}
 return out
review_before=inventory(R);author_before=inventory(A);selected=inventory(S)
assert author_before==read(W/'discovery-structural-r232-parent/observed-root.json')
detached=read(R/'DETACHED-ANCHORS.json')
for key,n in [('FINAL','FINAL.md'),('MANIFEST','MANIFEST.json'),('REPORT','REPORT.md')]:
 assert detached[key]['sha256']==anchors[n] and sha((R/detached[key]['path']).read_bytes())==anchors[n]
for key in ['REVIEW','READING_LIMITS']:
 x=detached[key];assert sha((R/x['path']).read_bytes())==x['sha256']
assert detached['seal_runs']==1
for n,k in [('SEAL-VERIFICATION.json','verification_record_sha256'),('ORIGINALS-UNCHANGED.json','originals_unchanged_record_sha256')]:
 assert sha((R/n).read_bytes())==detached[k]
m=read(S/'MANIFEST.json');expected={e['path']:e for e in m['files']}
assert set(selected['files'])==set(expected)|{'FINAL.md','MANIFEST.json'}
for n,e in expected.items():assert selected['files'][n]==dict(bytes=e['bytes'],sha256=e['sha256'],mode=int(e['mode'],8))
assert {'.':selected['root_mode'],**selected['directories']}=={n:int(v,8) for n,v in m['directories'].items()}
def invoke(root,report,exp):
 r=subprocess.run([sys.executable,'-I','-B',str(S/'code/verify_packet.py'),'--root',str(root),'--final-sha256',exp['FINAL.md'],'--manifest-sha256',exp['MANIFEST.json'],'--report',str(report),'--report-sha256',exp['REPORT.md']],capture_output=True,text=True)
 return r.returncode,json.loads(r.stdout)
code,verified=invoke(S,R/'REPORT.md',anchors);assert code==0
baseline=read(S/'private/author-baseline.json')
am=read(A/'selected/MANIFEST.json')
admitted={'selected/'+e['path'] for e in am['files']}|{'selected/FINAL.md','selected/MANIFEST.json','REPORT.md','DETACHED-ANCHORS.json','SEAL-VERIFICATION.json'}
assert set(baseline['files'])==admitted and len(admitted)==82
for n,e in baseline['files'].items():assert author_before['files'][n]==dict(bytes=e['bytes'],sha256=e['sha256'],mode=int(e['mode'],8))
for n,e in baseline['directories'].items():assert stat.S_IMODE((A/n).stat().st_mode)==int(e['mode'],8)
assert sha((S/'private/author-baseline.json').read_bytes())==read(R/'ORIGINALS-UNCHANGED.json')['baseline_sha256']
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree={e['path']:e for e in json.loads(tb)['tree']};assert len(tree)==13223
canon=read(S/'private/canonical-blob-recheck.json')['files'];assert len(canon)==22
for x in canon:
 b=(A/'selected/private'/x['path']).read_bytes();e=tree[x['path']]
 assert len(b)==x['bytes']==e['size'] and sha(b)==x['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob']==e['sha']
logs=[json.loads(x) for x in (S/'private/reviewer-semantic-reads.jsonl').read_bytes().splitlines()]
for x in logs:
 assert x['path'] in admitted
 b=(A/x['path']).read_bytes();ls=b.splitlines(keepends=True);lo,hi=x['lines_inclusive'];start,end=x['bytes_half_open']
 assert 1<=lo<=hi<=len(ls) and [sum(map(len,ls[:lo-1])),sum(map(len,ls[:hi]))]==[start,end]
 assert sha(b)==x['sha256'] # helper records the whole-file hash, not the selected extent hash
for name in ['GRS','AKP','Gigli2019']:
 bc=read(S/'private'/(name+'-boundary-classification.json'));ls=(A/'selected/private/primary'/(name+'.txt')).read_bytes().splitlines(keepends=True)
 for mask in bc['masks']:
  assert 1<=mask[0]<=len(ls)
g=read(S/'private/guards.json');ag=read(A/'selected/private/evidence/guards.json')
assert set(g['wildcards'])==set(ag['wildcards']) and len(g['wildcards'])==387
assert set(g['substrings'])==set(ag['substrings']) and len(g['substrings'])==162
controls=[]
with tempfile.TemporaryDirectory(dir=P,prefix='proof-copied-controls-') as td:
 root=Path(td)/'packet';root.mkdir();f=root/'sample.txt';content=b'independent copied review control\n';f.write_bytes(content);f.chmod(0o400);(root/'FINAL.md').write_bytes(b'Copied final\n');(root/'FINAL.md').chmod(0o400);report=Path(td)/'REPORT.md';report.write_bytes(b'Copied report\n');report.chmod(0o400)
 mf=root/'MANIFEST.json';mf.write_text(json.dumps({'files':[dict(path='sample.txt',bytes=len(content),sha256=sha(content),mode='0400')],'directories':{'.':'0500'}}));mf.chmod(0o400);root.chmod(0o500)
 exp={n:sha((report if n=='REPORT.md' else root/n).read_bytes()) for n in anchors}
 def case(label,reject=False,override=None):
  code,result=invoke(root,report,override or exp);assert bool(code)==reject,(label,result);controls.append({'case':label,'observed':'rejected' if reject else 'accepted'})
 case('valid independent copied selection')
 f.chmod(0o600);f.write_bytes(bytes([content[0]^1])+content[1:]);f.chmod(0o400);case('same-size byte mutation',True)
 f.chmod(0o600);f.write_bytes(content);f.chmod(0o400)
 f.chmod(0o600);case('file mode mutation',True);f.chmod(0o400)
 root.chmod(0o700);extra=root/'extra';extra.write_bytes(b'x');root.chmod(0o500);case('extra file',True);root.chmod(0o700);extra.unlink();root.chmod(0o500)
 case('wrong detached anchor',True,dict(exp,**{'FINAL.md':'0'*64}))
 root.chmod(0o700);case('directory mode mutation',True);root.chmod(0o500)
 case('restored copies');root.chmod(0o700)
with tempfile.TemporaryDirectory(dir=P,prefix='proof-copied-arithmetic-') as td:
 root=Path(td);relative=R.relative_to(PROJECT);(root/relative/'private').mkdir(parents=True)
 script=root/'check_constants.py';shutil.copyfile(S/'private/check_constants.py',script)
 run=subprocess.run([sys.executable,'-I','-B',str(script)],cwd=root,capture_output=True,text=True);assert run.returncode==0,run.stderr
 arithmetic=json.loads(run.stdout);assert arithmetic==read(root/relative/'private/constants-check.json')==read(S/'private/constants-check.json')
assert inventory(R)==review_before and inventory(A)==author_before
(P/'proof-observed-root.json').write_text(json.dumps(review_before,indent=2)+'\n')
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'selected_manifest_entries':len(expected),'selected_total_files':len(selected['files']),'selected_subdirectories':len(selected['directories']),'entire_review_files':len(review_before['files']),'entire_review_subdirectories':len(review_before['directories']),'entire_author_files':len(author_before['files']),'admitted_author_files':len(admitted),'admitted_author_baseline_matches_parent':True,'verifier':verified,'verifier_sha256':sha((S/'code/verify_packet.py').read_bytes()),'canonical_blobs_authenticated':len(canon),'read_extents_bound':len(logs),'primary_read_extents_bound':sum('/primary/' in x['path'] for x in logs),'read_log_hash_semantics':'Whole-file SHA256 plus exact line/byte extents; inspected helper before replay. Masked furniture is preserved separately.','independent_copied_controls':controls,'exact_rational_arithmetic_replayed_on_copy':arithmetic,'author_originals_unchanged':True,'review_originals_unchanged':True,'semantic_scope':'Parent read the complete independent REVIEW, READING-ACCESS-LIMITS, FINAL and outside REPORT. Artifact replay does not inherit reviewer source/primary semantic or visual coverage. No contribution verdict.'}
(P/'proof-replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))

