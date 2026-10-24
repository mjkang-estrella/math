#!/usr/bin/env python3
"""Read-only parent replay of the completed correctness review."""
from pathlib import Path
import datetime,hashlib,json,os,stat,subprocess,sys,tempfile
P=Path(__file__).resolve().parent;W=P.parent;C=P.parents[1];PROJECT=C.parents[2]
R=W/'structural-r229-proof-r1';S=R/'packet';A=W/'fresh-structural-discovery-r229';D=W/'discovery-structural-r229-parent'
sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(p.read_bytes())
anchors={'FINAL.md':'df0914cb75aaec060bebef351ea2f32b877c1d2a05979364825a59723451e01d','MANIFEST.json':'764549028f85e1018737c1b5f15070a7bd5f5a1e7d4dc22054a116491c7005fa','REPORT.md':'d181ec7e914545db82c661aba8b1a6f89535f45ddb3efc39ac1a6ef0a16e3f5f'}
def inventory(root):
 out={'files':{},'directories':{},'root_mode':stat.S_IMODE(root.stat().st_mode)}
 for base,ds,fs in os.walk(root,followlinks=False):
  for n in ds+fs:
   p=Path(base)/n;rel=p.relative_to(root).as_posix();st=p.lstat();assert not stat.S_ISLNK(st.st_mode)
   if stat.S_ISDIR(st.st_mode):out['directories'][rel]=stat.S_IMODE(st.st_mode)
   else:
    assert stat.S_ISREG(st.st_mode);b=p.read_bytes();out['files'][rel]={'bytes':len(b),'sha256':sha(b),'mode':stat.S_IMODE(st.st_mode)}
 return out
before=inventory(R);selected=inventory(S);author=inventory(A);assert author==read(D/'observed-root.json')
for key,n in [('FINAL','FINAL.md'),('MANIFEST','MANIFEST.json'),('REPORT','REPORT.md')]:
 x=read(R/'ANCHORS.json')[key];assert x['sha256']==anchors[n] and sha((R/x['path']).read_bytes())==anchors[n]
m=read(S/'MANIFEST.json');entries=[]
for rel,e in selected['files'].items():
 if rel!='MANIFEST.json':entries.append(dict(path=rel,type='file',mode=format(e['mode'],'04o'),bytes=e['bytes'],sha256=e['sha256']))
for rel,mode in selected['directories'].items():entries.append(dict(path=rel,type='directory',mode=format(mode,'04o')))
assert sorted(entries,key=lambda x:x['path'])==m['entries'] and selected['root_mode']==int(m['root_mode'],8)
baseline=read(S/'private/original-baseline.json');allowed={str(x.relative_to(PROJECT)) for x in (A/'packet').rglob('*')}|{str((A/'packet').relative_to(PROJECT))}|{str((A/n).relative_to(PROJECT)) for n in ['REPORT.md','ANCHORS.json','artifact-verification.json']}
assert {x['path']for x in baseline}==allowed
for x in baseline:
 f=PROJECT/x['path'];assert not f.is_symlink() and format(stat.S_IMODE(f.stat().st_mode),'04o')==x['mode']
 if x['type']=='file':assert len(f.read_bytes())==x['bytes'] and sha(f.read_bytes())==x['sha256']
 else:assert x['type']=='directory' and f.is_dir()
def invoke(script,packet,report,vals):
 run=subprocess.run([sys.executable,'-I','-B',str(script),'--packet',str(packet),'--manifest-sha256',vals['MANIFEST.json'],'--final-sha256',vals['FINAL.md'],'--report',str(report),'--report-sha256',vals['REPORT.md']],capture_output=True,text=True)
 return run.returncode,json.loads(run.stdout) if run.returncode==0 else run.stderr.strip()
code,verified=invoke(S/'verify_packet.py',S,R/'REPORT.md',anchors);assert code==0
code,author_verified=invoke(A/'packet/private/methods/verify_packet.py',A/'packet',A/'REPORT.md',read(D/'intake.json')['artifact_replay']['anchors']);assert code==0
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=json.loads(tb)['tree'];assert len(tree)==13223;by={x['path']:x for x in tree}
records=read(S/'private/canonical-authentication.json');assert len(records)==14
for x in records:
 b=(A/'packet'/x['selected_copy']).read_bytes();e=by[x['source']];assert len(b)==x['bytes']==e['size'] and sha(b)==x['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob']==e['sha']
reads=[json.loads(x) for x in (S/'private/reads.jsonl').read_bytes().splitlines()]
for x in reads:
 f=A/x['path'];assert str(f.relative_to(PROJECT)) in allowed;b=f.read_bytes();ls=b.splitlines(keepends=True);lo=x['start_byte'];hi=x['end_byte'];i=x['start_line'];j=x['end_line'];assert [sum(map(len,ls[:i-1])),sum(map(len,ls[:j]))]==[lo,hi] and sha(b)==x['sha256']
initial=read(S/'private/initial-displays.json')
for x in initial:
 f=A/x['path'];assert str(f.relative_to(PROJECT)) in allowed;b=f.read_bytes();ls=b.splitlines(keepends=True);i,j=x['lines'];lo,hi=x['bytes'];assert [sum(map(len,ls[:i-1])),sum(map(len,ls[:j]))]==[lo,hi] and sha(b[lo:hi])==x['sha256']
primary_extents=read(S/'private/final-primary-extents.json');nprimary=0
for name,rs in primary_extents.items():
 b=(A/'packet/private/primary'/(name+'.txt')).read_bytes();ls=b.splitlines(keepends=True)
 for x in rs:
  i,j=x['lines'];assert [sum(map(len,ls[:i-1])),sum(map(len,ls[:j]))]==x['bytes'];nprimary+=1
semantic=[json.loads(x) for x in (S/'private/primary-semantic-reads.jsonl').read_bytes().splitlines()]
for x in semantic:assert all(x['start']<=i<=x['end'] for i in x['masked_lines'])
fixture=R/'copied-controls/fixture';report=R/'copied-controls/REPORT.md';vals={'FINAL.md':sha((fixture/'FINAL.md').read_bytes()),'MANIFEST.json':sha((fixture/'MANIFEST.json').read_bytes()),'REPORT.md':sha(report.read_bytes())};code,result=invoke(S/'verify_packet.py',fixture,report,vals);assert code==0
controls=[]
with tempfile.TemporaryDirectory(dir=P,prefix='proof-copied-controls-') as td:
 r=Path(td);packet=r/'packet';packet.mkdir();content=packet/'MATH.txt';original=b'independent copied control\n';content.write_bytes(original);content.chmod(0o444);(packet/'FINAL.md').write_bytes(b'Copied fixture\n');(packet/'FINAL.md').chmod(0o444);report=r/'REPORT.md';report.write_bytes(b'Copied report\n');report.chmod(0o444)
 inv=inventory(packet);es=[dict(path=n,type='file',mode=format(e['mode'],'04o'),bytes=e['bytes'],sha256=e['sha256']) for n,e in inv['files'].items()];mf=packet/'MANIFEST.json';mf.write_text(json.dumps(dict(format='structural229-correctness-r1-exact-v1',root_mode='0500',entries=es)));mf.chmod(0o400);packet.chmod(0o500);vals={'FINAL.md':sha((packet/'FINAL.md').read_bytes()),'MANIFEST.json':sha(mf.read_bytes()),'REPORT.md':sha(report.read_bytes())}
 def case(label,reject=False,override=None):
  code,result=invoke(S/'verify_packet.py',packet,report,override or vals);assert (code!=0)==reject,(label,result);controls.append({'case':label,'observed':'rejected' if reject else 'accepted'})
 case('valid independent copied selection');content.chmod(0o644);content.write_bytes(bytes([original[0]^1])+original[1:]);content.chmod(0o444);case('same-size byte mutation',True);content.chmod(0o644);content.write_bytes(original);case('file mode mutation',True);content.chmod(0o444);packet.chmod(0o700);extra=packet/'extra';extra.write_bytes(b'x');packet.chmod(0o500);case('extra file',True);packet.chmod(0o700);extra.unlink();packet.chmod(0o500);case('wrong detached anchor',True,dict(vals,**{'MANIFEST.json':'0'*64}));case('restored copies');packet.chmod(0o700)
run=subprocess.run([sys.executable,'-I','-B',str(S/'independent_math.py')],capture_output=True,text=True);assert run.returncode==0;algebra=json.loads(run.stdout);assert algebra==read(S/'math-checks.json')
assert inventory(R)==before and inventory(A)==author
(P/'proof-observed-root.json').write_text(json.dumps(before,indent=2)+'\n')
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'selected_files':len(selected['files'])-1,'selected_subdirectories':len(selected['directories']),'whole_review_files':len(before['files']),'whole_review_subdirectories':len(before['directories']),'review_sha256':sha((S/'REVIEW.md').read_bytes()),'review_verifier_sha256':sha((S/'verify_packet.py').read_bytes()),'verifier':verified,'canonical_blobs_authenticated':len(records),'read_extents_bound':len(reads),'read_hash_semantics':'Reader logs bind whole-file SHA256 plus exact line/byte ranges; no selected-span hash is claimed.','retrospective_initial_extents_bound':len(initial),'primary_extents_bound':nprimary,'primary_masked_semantic_records_bound':len(semantic),'reviewer_admitted_author_files':sum(x['type']=='file'for x in baseline),'reviewer_admitted_author_directories_including_packet_root':sum(x['type']=='directory'for x in baseline),'reviewer_clean_control_replayed':True,'reviewer_control_log_cases':len(read(R/'copied-control-results.json')['controls']),'independent_copied_controls':controls,'independent_read_only_math_replay':algebra,'author_files':len(author['files']),'author_subdirectories':len(author['directories']),'author_baselines_agree':True,'author_originals_unchanged':True,'review_originals_unchanged':True,'author_verifier':author_verified,'semantic_scope':'Complete independent REVIEW, READING-LIMITS, FINAL, outside REPORT and independent notes read. Identity/range checks do not inherit source/primary/visual reading or determine a mathematical grade. Correctness adoption is separately reasoned; no contribution/count assigned.'}
(P/'proof-replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
