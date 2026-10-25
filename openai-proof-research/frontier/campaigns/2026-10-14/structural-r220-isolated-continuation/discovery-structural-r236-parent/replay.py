#!/usr/bin/env python3
"""Read-only artifact intake for the unchanged S236 author submission."""
from pathlib import Path
import datetime,hashlib,json,os,runpy,shutil,stat,subprocess,sys,tempfile
P=Path(__file__).resolve().parent;A=P.parent/'fresh-structural-discovery-r236';C=P.parents[1];PROJECT=C.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(p.read_bytes())
anchors={'FINAL.md':'3509848e623b225185684e3ef0cb2735dcd101675e5b71fec301274c6a65f0b5','MANIFEST.json':'aa997976c53a467bca89096b08536b54d52cc294aaac598884bd21e0ead37933','REPORT.md':'58f581f44b09413dd252e50d09235b86beb7bc0e684f9135dad85f887e5efce3','SELECTION.json':'18b8de40bbf2939ae57883efcc0d9b5aa6ee29d3195bdc05aa4958b03b7f0e28'}
def inventory(root):
 assert not root.is_symlink();out={'root_mode':stat.S_IMODE(root.stat().st_mode),'files':{},'directories':{}}
 for base,ds,fs in os.walk(root,followlinks=False):
  for n in ds+fs:
   p=Path(base)/n;rel=p.relative_to(root).as_posix();st=p.lstat();assert not stat.S_ISLNK(st.st_mode)
   if stat.S_ISDIR(st.st_mode):out['directories'][rel]=stat.S_IMODE(st.st_mode)
   else:
    assert stat.S_ISREG(st.st_mode);b=p.read_bytes();out['files'][rel]={'bytes':len(b),'sha256':sha(b),'mode':stat.S_IMODE(st.st_mode)}
 return out
before=inventory(A);m=read(A/'MANIFEST.json');assert len(m['entries'])==102
def invoke(expected):
 args=[sys.executable,'-I','-B',str(A/'verify_packet.py'),'--root',str(A),'--selection','SELECTION.json']
 for arg,n in [('final','FINAL.md'),('manifest','MANIFEST.json'),('selection','SELECTION.json'),('report','REPORT.md')]:args+=['--'+arg+'-sha256',expected[n]]
 r=subprocess.run(args,capture_output=True,text=True);return r.returncode,json.loads(r.stdout)if r.returncode==0 else r.stderr.strip()
code,verified=invoke(anchors);assert code==0 and read(A/'ANCHORS.json')['sha256']==anchors
scope=read(A/'private/freeze.json');assert sha((A/'STATEMENT.md').read_bytes())==scope['sha256']==m['scope_sha256']=='ad83c8bcf032a77734228b59ef8e4721215d0c09907e9e504a7df934ab89af1e';assert sha((A/'AUTHOR-PROOF.md').read_bytes())=='c8b6f21d138c4ce517e073dc45bf445c49bb1d21dc1c404f1cedef478cc97cb5'
treebytes=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(treebytes)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=json.loads(treebytes)['tree'];assert len(tree)==13223;by={x['path']:x for x in tree}
records=read(A/'private/authenticated.json');assert len(records)==28
for x in records:
 b=(A/x['local']).read_bytes();e=by[x['path']];assert len(b)==x['bytes']==e['size']and sha(b)==x['sha256']and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob']==e['sha'];assert '/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'in x['url']
prefixes=['preprints/A-counterexample-to-integer-degree-harmonic-dimension-comparison-September-25-2026','preprints/A-Three-Dimensional-Counterexample-to-Integer-Degree-Harmonic-Dimension-Comparison-September-26-2026'];assert read(A/'private/tree-selection.json')==[x for x in tree if any(x['path']==p or x['path'].startswith(p+'/')for p in prefixes)]
reads=[json.loads(x)for x in(A/'private/semantic-reads.jsonl').read_bytes().splitlines()]
for x in reads:
 b=(A/'private'/x['file']).read_bytes();lo,hi=x['bytes'];i,j=x['lines'];ls=b.splitlines(keepends=True);assert[sum(map(len,ls[:i-1])),sum(map(len,ls[:j]))]==[lo,hi]and sha(b[lo:hi])==x['sha256']
full=[]
for x in records:
 if not x['local'].endswith('.tex')or x['local'].endswith('/build/paper.tex'):continue
 b=(A/x['local']).read_bytes();spans=sorted(r['bytes']for r in reads if 'private/'+r['file']==x['local']);end=0
 for lo,hi in spans:assert lo<=end;end=max(end,hi)
 assert end==len(b);full.append(x['local'])
assert len(full)==19
primary=[json.loads(x)for x in(A/'private/primary/reads.jsonl').read_bytes().splitlines()]
for x in primary:
 b=(A/'private/primary'/(x['name']+'.txt')).read_bytes();lo,hi=x['bytes'];i,j=x['lines'];ls=b.splitlines(keepends=True);assert[sum(map(len,ls[:i-1])),sum(map(len,ls[:j]))]==[lo,hi]and sha(b[lo:hi])==x['sha256_unmasked_selection'];assert all(i<=k<=j for k in x['excluded_lines'])
pdfs=[]
for x in read(A/'private/primary/access.json'):
 b=(A/'private/primary'/(x['name']+'.pdf')).read_bytes();assert len(b)==x['bytes']and sha(b)==x['sha256'];assert len((A/'private/primary'/(x['name']+'.txt')).read_bytes())==x['text_bytes'];pdfs.append(x['name'])
g=read(A/'private/guards.json');assert len(g['wildcards'])==395 and len(g['substrings'])==162
history=[json.loads(x)for x in(A/'private/history-reads.jsonl').read_bytes().splitlines()]
for x in history:
 if x['path'].endswith('H-SCOPE.md'):name='original-analytic138-scope.txt'
 elif x['path'].endswith('AUTHOR-PROOF.md'):name=f"original-analytic138-{x['lines'][0]}.txt"
 else:name=Path(x['path']).stem+f"-{x['lines'][0]}.txt"
 b=(A/'private'/name).read_bytes();assert len(b)==x['bytes'][1]-x['bytes'][0]and sha(b)==x['sha256']
assert 'axiom mainStatement : MainClaim'in(A/'private/HarmonicGrowth.lean').read_text()
verify=runpy.run_path(str(A/'verify_packet.py'))['verify'];tiny=A/'private/controls';tinyargs=[sha((tiny/'MANIFEST.json').read_bytes()),sha((tiny/'FINAL.md').read_bytes()),'SELECTION.json',sha((tiny/'SELECTION.json').read_bytes()),sha((tiny/'REPORT.md').read_bytes())];assert verify(tiny,*tinyargs)['selected_files']==3;controls=[]
with tempfile.TemporaryDirectory(dir=P,prefix='copied-controls-')as td:
 root=Path(td)/'tiny';shutil.copytree(tiny,root,copy_function=shutil.copy2);f=root/'STATEMENT.md';original=f.read_bytes()
 def case(label,args=None,reject=False):
  try:verify(root,*(args or tinyargs));failed=False
  except ValueError:failed=True
  assert failed==reject;controls.append({'case':label,'observed':'rejected'if reject else'accepted'})
 case('copied tiny explicit selection');f.chmod(0o644);f.write_bytes(bytes([original[0]^1])+original[1:]);f.chmod(0o444);case('same-size byte mutation',reject=True);f.chmod(0o644);f.write_bytes(original);case('file mode mutation',reject=True);f.chmod(0o444)
 reduced=root/'REDUCED-SELECTION.json';args=list(tinyargs);args[2]=reduced.name;args[3]=sha(reduced.read_bytes());case('reduced selection inheriting manifest',args,True);case('restored tiny explicit selection')
code,_=invoke(dict(anchors,**{'MANIFEST.json':'0'*64}));assert code!=0
assert inventory(A)==before;(P/'observed-root.json').write_text(json.dumps(before,indent=2)+'\n')
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'statement_sha256':scope['sha256'],'author_proof_sha256':sha((A/'AUTHOR-PROOF.md').read_bytes()),'selected_files':len(m['entries']),'selected_bytes':sum(e['bytes']for e in m['entries']),'entire_author_files':len(before['files']),'entire_author_subdirectories':len(before['directories']),'verifier':verified,'verifier_sha256':sha((A/'verify_packet.py').read_bytes()),'selection_scope':'Exact 102-path explicit selection; verifier does not bind directory modes or reject unselected files. Parent separately observes the entire author tree and verifies it remains unchanged.','canonical_blobs_authenticated':len(records),'semantic_read_intervals_bound':len(reads),'non_driver_operative_tex_completely_covered':len(full),'primary_read_intervals_bound':len(primary),'primary_pdfs_with_access_receipts_authenticated':pdfs,'cm98_pdf_bound_by_selected_manifest':True,'copied_original_history_ranges_bound':len(history),'formal_support':'none; mainStatement is a restating axiom','author_tiny_selection_replayed':True,'independent_copied_controls':controls,'wrong_detached_anchor_rejected':True,'author_originals_unchanged':True,'semantic_scope':'Entire unchanged statement, author proof, prefreeze derivations, orientation, comparison, FINAL and REPORT read. Source/primary/history byte and range checks do not inherit semantic or visual reading. No writer or source verification script executed. Mathematical correctness and contribution remain UNDISCHARGED.'}
(P/'replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
