#!/usr/bin/env python3
"""Read-only archive intake; mathematical and mutation scripts run only on copies."""
from pathlib import Path
import ast,datetime,fnmatch,hashlib,json,os,shutil,stat,subprocess,sys,tempfile
P=Path(__file__).resolve().parent;A=P.parent/'fresh-structural-discovery-r230';C=P.parents[1];PROJECT=C.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(p.read_bytes())
anchors={'FINAL.md':'478c191e5f8ed0feec297ad28f2e12f4310421383972eed95093a1b1e168a83c','MANIFEST.json':'0f71e8e6b50da5d9a12c3de065463d01857ea374369a3e2e25a906244973c523','REPORT.md':'0a998736d9a4d5b5b25b0c8a6d2b63aa867d2ff3c4e9dd7ca9611eaedf066f9a'}
def inventory(root):
 out={'files':{},'directories':{},'root_mode':stat.S_IMODE(root.stat().st_mode)}
 for base,ds,fs in os.walk(root,followlinks=False):
  for n in ds+fs:
   p=Path(base)/n;rel=p.relative_to(root).as_posix();st=p.lstat();assert not stat.S_ISLNK(st.st_mode)
   if stat.S_ISDIR(st.st_mode):out['directories'][rel]=stat.S_IMODE(st.st_mode)
   else:
    assert stat.S_ISREG(st.st_mode);b=p.read_bytes();out['files'][rel]={'bytes':len(b),'sha256':sha(b),'mode':stat.S_IMODE(st.st_mode)}
 return out
before=inventory(A);m=read(A/'MANIFEST.json');anchor_record=read(A/'ANCHORS.json')
for n,h in anchors.items():assert sha((A/n).read_bytes())==h==anchor_record[n]
selected={x['path']for x in m['files']};outside={'MANIFEST.json','REPORT.md','ANCHORS.json','READONLY-VERIFICATION.json'}|{n for n in before['files'] if n.startswith('private/artifact-controls/')}
assert set(before['files'])-outside==selected;assert len(selected)==52

def invoke(root,expected):
 r=subprocess.run([sys.executable,'-I','-B',str(A/'VERIFY.py'),str(root),'--manifest-sha256',expected['MANIFEST.json'],'--final-sha256',expected['FINAL.md'],'--report-sha256',expected['REPORT.md']],capture_output=True,text=True)
 return r.returncode,json.loads(r.stdout) if r.returncode==0 else r.stderr.strip()
code,verified=invoke(A,anchors);assert code==0
b=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(b)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=json.loads(b)['tree'];assert len(tree)==13223;by={x['path']:x for x in tree}
records=read(A/'private/source-bindings.json');assert len(records)==13
for x in records:
 b=(A/x['local']).read_bytes();e=by[x['path']];assert len(b)==x['bytes']==e['size'] and sha(b)==x['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob']==e['sha'];assert '/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' in x['url']
prefix='preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026';assert read(A/'private/tree-selection.json')==[x for x in tree if x['path']==prefix or x['path'].startswith(prefix+'/')]
guards={}
for n in ast.parse((A/'GUARDS.py').read_text()).body:
 if isinstance(n,ast.Assign) and len(n.targets)==1 and isinstance(n.targets[0],ast.Name) and n.targets[0].id in ('WILDCARDS','SUBSTRINGS','DERIVATIVES'):guards[n.targets[0].id]=ast.literal_eval(n.value)
assert len(guards['WILDCARDS'])==383 and len(guards['SUBSTRINGS'])==162
reads=[json.loads(x)for x in (A/'private/reads.jsonl').read_bytes().splitlines()]
for x in reads:
 lo,hi=x['bytes']
 if x['kind']=='original mathematical history':
  rel=x['file'];assert not any(fnmatch.fnmatchcase(rel.casefold(),g.casefold())for g in guards['WILDCARDS']+guards['DERIVATIVES']);assert not any(g.casefold() in rel.casefold() for g in guards['SUBSTRINGS'])
  with (PROJECT/rel).open('rb') as f:f.seek(lo);span=f.read(hi-lo)
  assert span==(A/'private/history-i43-section.txt').read_bytes() and sha(span)==x['sha256']
 else:
  assert x['file'] in selected;b=(A/x['file']).read_bytes();ls=b.splitlines(keepends=True);i,j=x['lines'];assert [sum(map(len,ls[:i-1])),sum(map(len,ls[:j]))]==[lo,hi];assert sha(b[lo:hi])==x['sha256']
coverage=[]
for x in records:
 if not x['local'].endswith('.tex') or x['local'].endswith('/paper.tex'):continue
 end=0
 for lo,hi in sorted(r['bytes']for r in reads if r['file']==x['local']):assert lo<=end;end=max(end,hi)
 assert end==x['bytes'];coverage.append(x['local'])
primary=read(A/'private/primary/access.json')+[dict(read(A/'private/primary'/f'{n}-access.json'),name=n) for n in ['Cristoferi','ChoksiSternberg']];primary_names=[]
for x in primary:
 if 'error' in x:continue
 f=A/'private/primary'/(x['name']+'.pdf');b=f.read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256'];primary_names.append(x['name'])
 if 'text_bytes' in x:assert len(f.with_suffix('.txt').read_bytes())==x['text_bytes']
for n,h in [('private/lean354.md','b7913858f28af7bde03cbbb2e7276e26512aa4e9805cd3ee8ad78c94fef0a784'),('private/CubicTorus.lean','afa546a51aa6cd5b5016b3728a6a09128db21f60fff3e4d8f141c57ffbde0b2c')]:assert sha((A/n).read_bytes())==h
fixture=A/'private/artifact-controls/baseline';vals={n:sha((fixture/n).read_bytes())for n in anchors};code,clean=invoke(fixture,vals);assert code==0
controls=[]
with tempfile.TemporaryDirectory(dir=P,prefix='copied-controls-') as td:
 r=Path(td);names=['FINAL.md','MATH.txt'];selection=sha(('\n'.join(names)+'\n').encode());content=r/'MATH.txt';original=b'local copied integrity control\n';content.write_bytes(original);content.chmod(0o444);(r/'FINAL.md').write_text('Selection SHA256: '+selection+'\n');(r/'FINAL.md').chmod(0o444);(r/'REPORT.md').write_text('Independent copied report\n');mf=r/'MANIFEST.json'
 manifest={'schema':'r230-exact-selection-v1','selection_sha256':selection,'files':[dict(path=n,bytes=len((r/n).read_bytes()),sha256=sha((r/n).read_bytes()),mode='0444')for n in names]};mf.write_text(json.dumps(manifest));vals={n:sha((r/n).read_bytes())for n in anchors}
 def case(label,reject=False,override=None):
  code,result=invoke(r,override or vals);assert (code!=0)==reject,(label,result);controls.append({'case':label,'observed':'rejected' if reject else 'accepted'})
 case('valid independent selected fixture');content.chmod(0o644);content.write_bytes(bytes([original[0]^1])+original[1:]);content.chmod(0o444);case('same-size member mutation',True);content.chmod(0o644);content.write_bytes(original);case('file mode mutation',True);content.chmod(0o444)
 saved=mf.read_bytes();altered=dict(manifest,selection_sha256='0'*64);mf.write_text(json.dumps(altered));case('altered selection commitment',True,dict(vals,**{'MANIFEST.json':sha(mf.read_bytes())}));mf.write_bytes(saved);case('wrong detached anchor',True,dict(vals,**{'MANIFEST.json':'0'*64}));case('restored copies')
with tempfile.TemporaryDirectory(dir=P,prefix='copied-rational-')as td:
 r=Path(td);(r/'private').mkdir();shutil.copyfile(A/'CERTIFY.py',r/'CERTIFY.py');run=subprocess.run([sys.executable,'-I','-B',str(r/'CERTIFY.py')],capture_output=True,text=True,timeout=60);assert run.returncode==0,run.stderr;certificate=read(r/'private/nonlocal-rational-certificate.json');assert certificate==read(A/'private/nonlocal-rational-certificate.json');rational=json.loads(run.stdout)
assert inventory(A)==before;(P/'observed-root.json').write_text(json.dumps(before,indent=2)+'\n')
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'selected_files':len(selected),'entire_author_files':len(before['files']),'entire_author_subdirectories':len(before['directories']),'selection_scope':'Exact manifest membership compared against whole root excluding four detached files and explicitly outside tiny controls. Author verifier checks committed selection, not arbitrary unselected extras or directory modes. Parent independently snapshots all file and directory modes.','verifier':verified,'verifier_sha256':sha((A/'VERIFY.py').read_bytes()),'canonical_blobs_authenticated':len(records),'read_records_bound':len(reads),'source_read_extents_bound':sum(x['file'].startswith('private/upstream/')for x in reads),'complete_included_tex_files_bound':len(coverage),'primary_read_extents_bound':sum(x['file'].startswith('private/primary/')for x in reads),'primary_artifacts_authenticated':primary_names,'formal_artifacts_bound':2,'original_history_ranges_bound':1,'author_control_log_cases':len(read(A/'private/artifact-control-results.json')['results']),'author_clean_copied_selection_replayed':True,'independent_copied_controls':controls,'exact_rational_certificate_reproduced_on_copy':True,'rational_summary':rational,'author_originals_unchanged':True,'semantic_scope':'Complete DERIVATIONS, READ-SCOPE, FINAL, outside REPORT and certificate/verifier code read by parent. Artifact/range binding does not inherit source, primary, history or visual coverage. Rational certificates establish finite arithmetic only. No correctness, contribution, acceptance or count assigned.'}
(P/'replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
