#!/usr/bin/env python3
"""Read-only parent artifact replay; all mutations run on independent copies."""
from pathlib import Path
import datetime,fnmatch,hashlib,json,os,shutil,stat,subprocess,sys,tempfile
P=Path(__file__).resolve().parent;A=P.parent/'fresh-structural-discovery-r229';C=P.parents[1];PROJECT=C.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(p.read_bytes())
anchors={'FINAL.md':'c604f5f58aa74a1416315e1432a6a7478215eff785216db58d90193fe6b6ce42','MANIFEST.json':'d22cac561514198a0c0b44dfec207facdb51c9f8a1954b78ac2065695bdea046','REPORT.md':'72686c17ba999700c9a1bf6659dbe994eff994e979d8463edb3a5e50f501c148'}
S=A/'packet'
def inventory(root):
 out={'files':{},'directories':{},'root_mode':stat.S_IMODE(root.stat().st_mode)}
 for base,ds,fs in os.walk(root,followlinks=False):
  for n in ds+fs:
   p=Path(base)/n;rel=p.relative_to(root).as_posix();st=p.lstat();assert not stat.S_ISLNK(st.st_mode)
   if stat.S_ISDIR(st.st_mode):out['directories'][rel]=stat.S_IMODE(st.st_mode)
   else:
    assert stat.S_ISREG(st.st_mode);b=p.read_bytes();out['files'][rel]={'bytes':len(b),'sha256':sha(b),'mode':stat.S_IMODE(st.st_mode)}
 return out
before=inventory(A);selected=inventory(S);m=read(S/'MANIFEST.json');detached=read(A/'ANCHORS.json')
for key,n in [('FINAL','FINAL.md'),('MANIFEST','MANIFEST.json'),('REPORT','REPORT.md')]:
 assert detached[key]['sha256']==anchors[n] and sha((A/detached[key]['path']).read_bytes())==anchors[n]
assert sha((S/'STATEMENT.md').read_bytes())==read(A/'statement-anchor.json')['sha256']==detached['STATEMENT']['sha256']
entries=[]
for rel,e in selected['files'].items():
 if rel=='MANIFEST.json':continue
 entries.append(dict(path=rel,type='file',mode=format(e['mode'],'04o'),bytes=e['bytes'],sha256=e['sha256']))
for rel,mode in selected['directories'].items():entries.append(dict(path=rel,type='directory',mode=format(mode,'04o')))
assert sorted(entries,key=lambda x:x['path'])==m['entries'];assert selected['root_mode']==int(m['root_mode'],8) and selected['files']['MANIFEST.json']['mode']==0o400
matched=0
for rel,e in selected['files'].items():
 if rel=='MANIFEST.json':continue
 original=A/rel
 for prefix in ['private/metadata/','private/methods/']:
  if rel.startswith(prefix):original=A/rel[len(prefix):]
 assert original.is_file() and sha(original.read_bytes())==e['sha256'];matched+=1
def invoke(packet,report,expected):
 r=subprocess.run([sys.executable,'-I','-B',str(A/'verify_packet.py'),'--packet',str(packet),'--manifest-sha256',expected['MANIFEST.json'],'--final-sha256',expected['FINAL.md'],'--report',str(report),'--report-sha256',expected['REPORT.md']],capture_output=True,text=True)
 return r.returncode,json.loads(r.stdout) if r.returncode==0 else r.stderr.strip()
code,verified=invoke(S,A/'REPORT.md',anchors);assert code==0
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=json.loads(tb)['tree'];assert len(tree)==13223;by={x['path']:x for x in tree}
records=read(A/'authentication.json');assert len(records)==14
for x in records:
 b=(S/x['local']).read_bytes();e=by[x['path']];assert len(b)==x['bytes']==e['size'] and sha(b)==x['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob']==e['sha']
 assert '/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' in x['url']
prefixes={x['path'].split('/')[1] for x in records};assert read(A/'selected-tree.json')==[x for x in tree if len(x['path'].split('/'))>1 and x['path'].split('/')[1] in prefixes]
reads=[json.loads(x) for x in (A/'reads.jsonl').read_bytes().splitlines()]
for x in reads:
 b=(S/x['local']).read_bytes();ls=b.splitlines(keepends=True);a,z=x['lines_inclusive'];lo,hi=x['bytes_halfopen'];assert sha(b[lo:hi])==x['selected_sha256'] and [sum(map(len,ls[:a-1])),sum(map(len,ls[:z]))]==[lo,hi]
# Verify the exact source include line omitted from numbered mathematical displays.
geom=(S/'private/rigidity/build/sections/geometry.tex').read_bytes();line=geom.splitlines(keepends=True)[331];assert len(line)==27 and b'input{figures/thin-slice}' in line
artifacts=[];failed=[]
for x in read(A/'primary-access.json'):
 p=S/'private/primary'/(x['name']+'.pdf');b=p.read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256']
 if 'error' in x:failed.append(x['name']);continue
 text=p.with_suffix('.txt').read_bytes();assert len(text)==x['text_bytes'] and sha(text)==x['text_sha256'];artifacts.append(p.name)
for rec,file in [('formal-access.json','lean-353.md'),('formal-declarations.json','AffineBernstein.lean')]:
 x=read(A/rec);b=(S/'private'/file).read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256'] and '/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' in x['url']
assert b'sorry' in (S/'private/AffineBernstein.lean').read_bytes()
guards=read(A/'guards.json');assert len(guards['wildcards'])==381 and len(guards['substrings'])==162
history=[]
for x in read(A/'history-selected.json'):
 rel=x['path'];assert not any(fnmatch.fnmatchcase(rel.casefold(),g.casefold()) for g in guards['wildcards']);assert not any(g.casefold() in rel.casefold() for g in guards['substrings']);lo,hi=x['bytes']
 with (PROJECT/rel).open('rb') as f:f.seek(lo);b=f.read(hi-lo)
 assert sha(b)==x['sha256'];history.append(b)
assert b''.join(history)==(S/'private/original-sections.txt').read_bytes()
fixture=A/'copied-controls/fixture';report=A/'copied-controls/REPORT.md';expected={'FINAL.md':sha((fixture/'FINAL.md').read_bytes()),'MANIFEST.json':sha((fixture/'MANIFEST.json').read_bytes()),'REPORT.md':sha(report.read_bytes())};code,result=invoke(fixture,report,expected);assert code==0
controls=[]
with tempfile.TemporaryDirectory(dir=P,prefix='copied-controls-') as td:
 r=Path(td);packet=r/'packet';packet.mkdir();content=packet/'MATH.txt';original=b'local copied integrity control\n';content.write_bytes(original);content.chmod(0o600);(packet/'FINAL.md').write_bytes(b'Copied fixture\n');(r/'REPORT.md').write_bytes(b'Outside copied report\n')
 inv=inventory(packet);es=[dict(path=n,type='file',mode=format(e['mode'],'04o'),bytes=e['bytes'],sha256=e['sha256']) for n,e in inv['files'].items()];mf=packet/'MANIFEST.json';mf.write_text(json.dumps(dict(format='r229-exact-selection-v1',root_mode=format(inv['root_mode'],'04o'),entries=es)));mf.chmod(0o400);expected={'FINAL.md':sha((packet/'FINAL.md').read_bytes()),'MANIFEST.json':sha(mf.read_bytes()),'REPORT.md':sha((r/'REPORT.md').read_bytes())}
 def case(label,reject=False,override=None):
  code,result=invoke(packet,r/'REPORT.md',override or expected);assert (code!=0)==reject,(label,result);controls.append({'case':label,'observed':'rejected' if reject else 'accepted'})
 case('valid independent copied selection');content.write_bytes(bytes([original[0]^1])+original[1:]);case('same-size byte mutation',True);content.write_bytes(original);content.chmod(0o644);case('file mode mutation',True);content.chmod(0o600);extra=packet/'extra';extra.write_bytes(b'x');case('extra file',True);extra.unlink();case('wrong detached anchor',True,dict(expected,**{'MANIFEST.json':'0'*64}));case('restored copies')
with tempfile.TemporaryDirectory(dir=P,prefix='copied-algebra-') as td:
 r=Path(td);shutil.copyfile(S/'math_algebra.py',r/'math_algebra.py');run=subprocess.run([sys.executable,'-I','-B',str(r/'math_algebra.py')],capture_output=True,text=True);assert run.returncode==0;algebra=read(r/'math-algebra-output.json');assert algebra==read(S/'math-algebra-output.json')==json.loads(run.stdout)
assert inventory(A)==before
(P/'observed-root.json').write_text(json.dumps(before,indent=2)+'\n')
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'selected_files':len(selected['files'])-1,'selected_subdirectories':len(selected['directories']),'entire_author_files':len(before['files']),'entire_author_subdirectories':len(before['directories']),'selected_files_matching_unselected_originals':matched,'verifier':verified,'verifier_sha256':sha((A/'verify_packet.py').read_bytes()),'canonical_blobs_authenticated':len(records),'source_read_extents_bound':sum(not x['local'].startswith('private/primary/') for x in reads),'primary_read_extents_bound':sum(x['local'].startswith('private/primary/') for x in reads),'primary_pdfs_authenticated':artifacts,'failed_primary_artifacts_authenticated':failed,'recorded_visual_crops':5,'formal_artifacts_authenticated':2,'original_history_ranges_bound':len(history),'author_control_log_cases':len(read(A/'artifact-verification.json')['controls']),'author_clean_copied_selection_replayed':True,'independent_copied_controls':controls,'exact_algebra_replayed_on_copy':algebra,'author_originals_unchanged':True,'semantic_scope':'Parent read the entire frozen statement, author proof, prefreeze, validation, reading limits, FINAL and outside REPORT. Recorded-range authentication does not inherit child source/primary/history semantic or visual coverage. Copied algebra replay checks the listed finite rational identities only. No mathematical grade.'}
(P/'replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
