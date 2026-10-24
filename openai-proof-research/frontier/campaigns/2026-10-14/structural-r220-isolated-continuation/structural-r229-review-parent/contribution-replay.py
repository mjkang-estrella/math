#!/usr/bin/env python3
"""Read-only parent replay of the completed contribution review."""
from pathlib import Path
import datetime,hashlib,json,os,stat,subprocess,sys,tempfile
P=Path(__file__).resolve().parent;W=P.parent;C=P.parents[1];PROJECT=C.parents[2]
R=W/'structural-r229-contribution-r1';S=R/'packet';A=W/'fresh-structural-discovery-r229';D=W/'discovery-structural-r229-parent'
sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(p.read_bytes())
anchors={'FINAL.md':'05c18a15a8391c3ab40c13c268569f246da2064bfad0e944550d3aebb4775578','MANIFEST.json':'2544e6bb4d3cdfa253d3cce82aac679388db09f95e4a12696b6782f58e276537','REPORT.md':'38eb190a41060a17b02693c52937dccb6f7502038a686185cb5fc6cffec6a6bf'}
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
for n in anchors:
 x=read(R/'ANCHORS.json')[n];assert x['sha256']==anchors[n] and sha((PROJECT/x['path']).read_bytes())==anchors[n]
m=read(S/'MANIFEST.json');entries=[]
for rel,e in selected['files'].items():
 if rel!='MANIFEST.json':entries.append(dict(path=rel,type='file',mode=format(e['mode'],'04o'),bytes=e['bytes'],sha256=e['sha256']))
for rel,mode in selected['directories'].items():entries.append(dict(path=rel,type='directory',mode=format(mode,'04o')))
assert sorted(entries,key=lambda x:x['path'])==m['entries'] and selected['root_mode']==int(m['root_mode'],8)
baseline_data=read(S/'private/original-baseline.json');baseline=baseline_data['entries'];assert baseline_data['packet_root_mode']=='0500';allowed={str(x.relative_to(PROJECT)) for x in (A/'packet').rglob('*')}|{str((A/'packet').relative_to(PROJECT))}|{str((A/n).relative_to(PROJECT)) for n in ['REPORT.md','ANCHORS.json','artifact-verification.json']}
assert {x['path']for x in baseline}==allowed-{str((A/'packet').relative_to(PROJECT))}
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
 b=(A/'packet'/x['local']).read_bytes();e=by[x['path']];assert len(b)==x['bytes']==e['size'] and sha(b)==x['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob']==e['sha']
reads=[json.loads(x) for x in (S/'private/reviewer-reads.jsonl').read_bytes().splitlines()]
extents=0;masked=0
for x in reads:
 if 'file' not in x:continue
 assert x['file'] in allowed;f=PROJECT/x['file'];b=f.read_bytes();ls=b.splitlines(keepends=True)
 if 'sha256' in x:assert sha(b)==x['sha256']
 if 'lines_inclusive' in x:
  i,j=x['lines_inclusive'];assert [sum(map(len,ls[:i-1])),sum(map(len,ls[:j]))]==x['bytes_half_open'];extents+=1
  if 'masked_lines' in x:assert all(i<=m[0]<=j for m in x['masked_lines']);masked+=1
 if 'line_selection' in x:assert all(1<=i<=len(ls) for i in x['line_selection'])
primary=read(S/'private/primary-reextraction.json')
for x in primary:
 b=(A/'packet/private/primary'/(x['name']+'.txt')).read_bytes();assert len(b)==x['fresh_extraction_bytes'] and sha(b)==x['fresh_sha256']==x['admitted_text_sha256'] and x['identical']
crops=read(S/'private/visual/crops.json')
for x in crops:assert x['source'] in allowed and (PROJECT/x['output']).is_relative_to(S/'private/visual') and (PROJECT/x['output']).is_file()
fixture=R/'copied-controls/packet';report=R/'copied-controls/REPORT.md';vals={'FINAL.md':sha((fixture/'FINAL.md').read_bytes()),'MANIFEST.json':sha((fixture/'MANIFEST.json').read_bytes()),'REPORT.md':sha(report.read_bytes())};code,result=invoke(S/'verify_packet.py',fixture,report,vals);assert code==0
controls=[]
with tempfile.TemporaryDirectory(dir=P,prefix='contribution-copied-controls-') as td:
 r=Path(td);packet=r/'packet';packet.mkdir();content=packet/'MATH.txt';original=b'independent copied control\n';content.write_bytes(original);content.chmod(0o444);(packet/'FINAL.md').write_bytes(b'Copied fixture\n');(packet/'FINAL.md').chmod(0o444);report=r/'REPORT.md';report.write_bytes(b'Copied report\n');report.chmod(0o444)
 inv=inventory(packet);es=[dict(path=n,type='file',mode=format(e['mode'],'04o'),bytes=e['bytes'],sha256=e['sha256']) for n,e in inv['files'].items()];mf=packet/'MANIFEST.json';mf.write_text(json.dumps(dict(format='structural-r229-contribution-r1-selection-v1',root_mode='0500',entries=es)));mf.chmod(0o400);packet.chmod(0o500);vals={'FINAL.md':sha((packet/'FINAL.md').read_bytes()),'MANIFEST.json':sha(mf.read_bytes()),'REPORT.md':sha(report.read_bytes())}
 def case(label,reject=False,override=None):
  code,result=invoke(S/'verify_packet.py',packet,report,override or vals);assert (code!=0)==reject,(label,result);controls.append({'case':label,'observed':'rejected' if reject else 'accepted'})
 case('valid independent copied selection');content.chmod(0o644);content.write_bytes(bytes([original[0]^1])+original[1:]);content.chmod(0o444);case('same-size byte mutation',True);content.chmod(0o644);content.write_bytes(original);case('file mode mutation',True);content.chmod(0o444);packet.chmod(0o700);extra=packet/'extra';extra.write_bytes(b'x');packet.chmod(0o500);case('extra file',True);packet.chmod(0o700);extra.unlink();packet.chmod(0o500);case('wrong detached anchor',True,dict(vals,**{'MANIFEST.json':'0'*64}));case('restored copies');packet.chmod(0o700)
run=subprocess.run([sys.executable,'-I','-B',str(S/'private/coefficient_calculation.py')],capture_output=True,text=True);assert run.returncode==0;algebra=json.loads(run.stdout);assert algebra==read(S/'private/coefficient-output.json')
assert inventory(R)==before and inventory(A)==author
(P/'contribution-observed-root.json').write_text(json.dumps(before,indent=2)+'\n')
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'selected_files':len(selected['files'])-1,'selected_subdirectories':len(selected['directories']),'whole_review_files':len(before['files']),'whole_review_subdirectories':len(before['directories']),'review_sha256':sha((S/'REVIEW.md').read_bytes()),'review_verifier_sha256':sha((S/'verify_packet.py').read_bytes()),'verifier':verified,'canonical_blobs_authenticated':len(records),'reviewer_read_records':len(reads),'read_extents_bound':extents,'read_hash_semantics':'Where present, SHA256 binds whole file plus exact byte/line range. Metadata identity does not inherit semantic coverage.','primary_masked_records_bound':masked,'primary_reextractions_bound':len(primary),'reviewer_visual_crop_identities_bound':len(crops),'reviewer_admitted_author_files':sum(x['type']=='file'for x in baseline),'reviewer_admitted_author_subdirectories':sum(x['type']=='directory'for x in baseline),'reviewer_admitted_packet_root_mode':baseline_data['packet_root_mode'],'reviewer_clean_control_replayed':True,'reviewer_control_log_cases':len(read(R/'artifact-verification.json')['controls']),'independent_copied_controls':controls,'independent_read_only_math_replay':algebra,'author_files':len(author['files']),'author_subdirectories':len(author['directories']),'author_baselines_agree':True,'author_originals_unchanged':True,'review_originals_unchanged':True,'author_verifier':author_verified,'semantic_scope':'Complete independent REVIEW, READING-ACCESS-LIMITS, FINAL, outside REPORT and working DERIVATIONS read. Identity/range checks do not inherit source/primary/visual reading or determine a mathematical grade. Contribution adoption is separately reasoned and conditional on the separately adopted same-scope correctness PASS; artifact checks assign no mathematical verdict or count.'}
(P/'contribution-replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
