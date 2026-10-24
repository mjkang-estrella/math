#!/usr/bin/env python3
"""Read-only parent artifact replay; all mutations run on independent copies."""
from pathlib import Path
import datetime,fnmatch,hashlib,json,os,shutil,stat,subprocess,sys,tempfile
P=Path(__file__).resolve().parent;A=P.parent/'fresh-structural-discovery-r228';C=P.parents[1];PROJECT=C.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(p.read_bytes())
anchors={'FINAL.md':'8e1c5c7a9e10a8d9e2994c2818536126c8e51af00f7eb28401d3c4417a9eebab','MANIFEST.json':'407536200522378c12cf81328c92c324a257d790999135dcb8bad65b80e149d0','REPORT.md':'bdb033a770406b31d3a9a33c90a0916fc4083be6bcc75fb48316e1dd37ba56fb'}
def inventory(root):
 out={'files':{},'directories':{},'root_mode':stat.S_IMODE(root.stat().st_mode)}
 for base,ds,fs in os.walk(root,followlinks=False):
  for n in ds+fs:
   p=Path(base)/n;rel=p.relative_to(root).as_posix();st=p.lstat();assert not stat.S_ISLNK(st.st_mode)
   if stat.S_ISDIR(st.st_mode):out['directories'][rel]=stat.S_IMODE(st.st_mode)
   else:
    assert stat.S_ISREG(st.st_mode);b=p.read_bytes();out['files'][rel]={'bytes':len(b),'sha256':sha(b),'mode':stat.S_IMODE(st.st_mode)}
 return out
before=inventory(A);m=read(A/'MANIFEST.json');assert read(A/'DETACHED.json')['sha256']==anchors
for n,h in anchors.items():assert sha((A/n).read_bytes())==h
assert set(before['files'])-set(m['outside_manifest'])=={x['path'] for x in m['files']}
assert set(before['directories'])|{'.'}==set(m['directories'])
def invoke(root,expected):
 r=subprocess.run([sys.executable,'-I','-B',str(A/'verify_packet.py'),'--root',str(root),'--manifest-sha256',expected['MANIFEST.json'],'--final-sha256',expected['FINAL.md'],'--report-sha256',expected['REPORT.md']],capture_output=True,text=True)
 return r.returncode,json.loads(r.stdout)
code,verified=invoke(A,anchors);assert code==0
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=json.loads(tb)['tree'];assert len(tree)==13223;by={x['path']:x for x in tree}
records=read(A/'private/authenticated.json');assert len(records)==16
for x in records:
 b=(A/x['local']).read_bytes();e=by[x['path']];assert len(b)==x['bytes']==e['size'] and sha(b)==x['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob']==e['sha']
 assert '/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' in x['url']
prefixes={x['path'].split('/')[1] for x in records};assert read(A/'private/tree-selection.json')==[x for x in tree if len(x['path'].split('/'))>1 and x['path'].split('/')[1] in prefixes]
reads=[json.loads(x) for x in (A/'private/semantic-reads.jsonl').read_bytes().splitlines()]
for x in reads:
 b=(A/x['file']).read_bytes();ls=b.splitlines(keepends=True);a,z=x['lines_inclusive'];lo,hi=x['bytes_half_open'];assert sha(b)==x['sha256'] and [sum(map(len,ls[:a-1])),sum(map(len,ls[:z]))]==[lo,hi];assert not x['masked_lines']
coverage=[]
for x in records:
 if Path(x['local']).suffix=='.pdf':continue
 spans=sorted(r['bytes_half_open'] for r in reads if r['file']==x['local']);end=0
 for lo,hi in spans:assert lo<=end;end=max(end,hi)
 assert end==x['bytes'];coverage.append(x['local'])
artifacts=[]
for x in read(A/'private/primary-access.json')+[dict(read(A/'private/Guan-access.json'),name='Guan-published')]:
 if 'error' in x:continue
 p=A/'private/primary'/(x['name']+'.pdf');b=p.read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256'];artifacts.append(p.name)
 if 'text_bytes' in x:assert len(p.with_suffix('.txt').read_bytes())==x['text_bytes']
guards=read(A/'private/guards.json');assert len(guards['wildcards'])==379 and len(guards['substrings'])==162
h=read(A/'private/history-selected.json');rel=h['path'];assert not any(fnmatch.fnmatchcase(rel.casefold(),g.casefold()) for g in guards['wildcards']);assert not any(g.casefold() in rel.casefold() for g in guards['substrings'])
lo,hi=h['bytes_half_open']
with (PROJECT/rel).open('rb') as f:f.seek(lo);history=f.read(hi-lo)
assert sha(history)==h['selected_sha256'] and history==(A/'private/history-r31-angular-section.txt').read_bytes()
assert sha((A/'private/Source352-catalogue.txt').read_bytes())=='6874828238d09341812f4306aa241f48ce9ca62f95f89a211c003952c1943353'
tiny=A/'private/controls/tiny';tinyanchors={n:sha((tiny/n).read_bytes()) for n in anchors};code,result=invoke(tiny,tinyanchors);assert code==0
controls=[]
with tempfile.TemporaryDirectory(dir=P,prefix='copied-controls-') as td:
 r=Path(td);r.chmod(0o700);content=r/'MATH.txt';original=b'local copied integrity control\n';content.write_bytes(original);content.chmod(0o600)
 for n in ['FINAL.md','REPORT.md']:(r/n).write_bytes((A/n).read_bytes());(r/n).chmod(0o600)
 entries=[dict(path=n,bytes=len((r/n).read_bytes()),sha256=sha((r/n).read_bytes()),mode='0600') for n in ['FINAL.md','MATH.txt']]
 manifest=r/'MANIFEST.json';manifest.write_text(json.dumps({'schema':'r228-exact-local-selection-v1','outside_manifest':m['outside_manifest'],'files':entries,'directories':['.']}));manifest.chmod(0o600);expected={n:sha((r/n).read_bytes()) for n in anchors}
 def case(label,reject=False,override=None):
  code,result=invoke(r,override or expected);assert (code!=0)==reject,(label,result);controls.append({'case':label,'observed':'rejected' if reject else 'accepted'})
 case('valid independent copied selection');content.write_bytes(bytes([original[0]^1])+original[1:]);case('same-size byte mutation',True);content.write_bytes(original);content.chmod(0o644);case('file mode mutation',True);content.chmod(0o600);extra=r/'extra';extra.write_bytes(b'x');case('extra file',True);extra.unlink();case('wrong detached anchor',True,dict(expected,**{'MANIFEST.json':'0'*64}));case('restored copies')
with tempfile.TemporaryDirectory(dir=P,prefix='copied-rational-') as td:
 r=Path(td);(r/'private').mkdir();shutil.copyfile(A/'forward_bounds.py',r/'forward_bounds.py');run=subprocess.run([sys.executable,'-I','-B',str(r/'forward_bounds.py')],capture_output=True,text=True);assert run.returncode==0;bounds=read(r/'private/forward-rational-bounds.json');assert bounds==read(A/'private/forward-rational-bounds.json')==json.loads(run.stdout)
assert inventory(A)==before
(P/'observed-root.json').write_text(json.dumps(before,indent=2)+'\n')
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'selected_files':len(m['files']),'selected_directories_including_root':len(m['directories']),'entire_author_files':len(before['files']),'entire_author_subdirectories':len(before['directories']),'verifier':verified,'verifier_sha256':sha((A/'verify_packet.py').read_bytes()),'canonical_blobs_authenticated':len(records),'source_read_extents_bound':sum(x['file'].startswith('private/canonical/') for x in reads),'non_pdf_source_files_fully_covered_by_recorded_ranges':len(coverage),'primary_read_extents_bound':sum(x['file'].startswith('private/primary/') for x in reads),'primary_artifacts_authenticated':artifacts,'recorded_visual_crops':4,'formal_artifacts_authenticated':0,'original_history_ranges_bound':1,'author_control_log_cases':len(read(A/'private/copied-controls.json')['controls']),'author_clean_copied_selection_replayed':True,'independent_copied_controls':controls,'exact_rational_bounds_replayed_on_copy':bounds,'author_originals_unchanged':True,'semantic_scope':'Complete authored notes, FINAL and REPORT read by parent. Source/primary/history ranges and artifact authentication do not inherit child semantic or visual coverage. Rational replay certifies arithmetic only, not the analytic maps, global matching or continuation. No mathematical grade.'}
(P/'replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
