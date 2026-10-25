#!/usr/bin/env python3
"""Read-only S236 contribution intake and tiny independent copied controls."""
from pathlib import Path
import datetime,hashlib,json,os,runpy,shutil,stat,subprocess,sys,tempfile
P=Path(__file__).resolve().parent;W=P.parent;C=P.parents[1];PROJECT=C.parents[2]
R=W/'structural-r236-contribution-r1';A=W/'fresh-structural-discovery-r236';Q=W/'structural-r236-proof-r1'
sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(p.read_bytes())
anchors={'FINAL.md':'3c195e6b74cba33e3aa073a01aa07dec9b2e01c12086b0f44a141d3f814d837e','MANIFEST.json':'b4c1c8513862cac5b6c9ace5afe8e2285b4f06ec3e27f090c4354f1d98a8b647','REPORT.md':'ab1f97defbfbd82347c3accf9bcc19a0529ebdf6cc245dcced7bab8a941dbc68','SELECTION.json':'78648b1b0690f2ec4c8ddd762704f898ddae54bed31321881018784a235e0e63'}
def inventory(root):
 assert not root.is_symlink();out={'root_mode':stat.S_IMODE(root.stat().st_mode),'files':{},'directories':{}}
 for base,ds,fs in os.walk(root,followlinks=False):
  for name in ds+fs:
   p=Path(base)/name;s=p.lstat();rel=p.relative_to(root).as_posix();assert not stat.S_ISLNK(s.st_mode)
   if stat.S_ISDIR(s.st_mode):out['directories'][rel]=stat.S_IMODE(s.st_mode)
   else:
    assert stat.S_ISREG(s.st_mode);b=p.read_bytes();out['files'][rel]={'bytes':len(b),'sha256':sha(b),'mode':stat.S_IMODE(s.st_mode)}
 return out
before=inventory(R);abefore=inventory(A);qbefore=inventory(Q)
assert abefore==read(W/'discovery-structural-r236-parent/observed-root.json') and qbefore==read(P/'proof-observed-root.json')
assert len(before['files'])==40 and len(abefore['files'])==114
assert len(read(R/'SELECTION.json')['files'])==16
assert set(before['files'])-set(read(R/'SELECTION.json')['files'])=={'MANIFEST.json','REPORT.md','ANCHORS.json','SEAL-VERIFICATION.json'}|{k for k in before['files'] if k.startswith('private/controls/')}
assert sha((R/'verify_packet.py').read_bytes())=='7e7c6301de300dc6b2bd01908bf23942bbea3528f0a4ea7c52c1931736f33c26'
def invoke(root,expected):
 args=[sys.executable,'-I','-B',str(R/'verify_packet.py'),'--root',str(root),'--selection','SELECTION.json']
 for key,name in [('manifest','MANIFEST.json'),('final','FINAL.md'),('selection','SELECTION.json'),('report','REPORT.md')]:args+=['--'+key+'-sha256',expected[name]]
 p=subprocess.run(args,capture_output=True,text=True)
 return p.returncode,json.loads(p.stdout) if p.returncode==0 else p.stderr.strip().splitlines()[-1]
code,verified=invoke(R,anchors);assert code==0 and verified['selected_files']==16
for name,digest in read(R/'ANCHORS.json')['sha256'].items():assert sha((R/name).read_bytes())==digest
assert all(read(R/'ANCHORS.json')['sha256'][k]==v for k,v in anchors.items())
verify=runpy.run_path(str(A/'verify_packet.py'))['verify'];aa=read(W/'discovery-structural-r236-parent/replay.json')['anchors']
averified=verify(A,aa['MANIFEST.json'],aa['FINAL.md'],'SELECTION.json',aa['SELECTION.json'],aa['REPORT.md']);assert averified['selected_files']==102
rows={x['path']:x for x in read(R/'private/author-baseline.json')['entries']}
assert len(rows)==106 and set(rows)==set(read(A/'SELECTION.json')['paths'])|{'MANIFEST.json','REPORT.md','ANCHORS.json','SEAL-VERIFICATION.json'}
assert {k:dict(bytes=x['bytes'],sha256=x['sha256'],mode=int(x['mode'],8)) for k,x in rows.items()}=={k:abefore['files'][k] for k in rows}
recheck=read(R/'private/author-recheck.json');assert recheck['all_unchanged'] and recheck['admitted_file_count']==106 and recheck['baseline_sha256']==sha((R/'private/author-baseline.json').read_bytes())
for x in recheck['entries']:assert x['unchanged'] and {k:v for k,v in x.items() if k!='unchanged'}==rows[x['path']]
g=read(R/'guards.json');ag=read(A/'private/guards.json');assert set(g['wildcards'])==set(ag['wildcards']) and set(g['substrings'])==set(ag['substrings']);assert len(g['wildcards'])==395 and len(g['substrings'])==162
assert sha((R/'acceptance.txt').read_bytes())=='f147924a01d36cce7ad5ee13bad6ed9ed9109f3bf4b5c2386fc318aae1330984'
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=json.loads(tb)['tree'];assert len(tree)==13223;by={x['path']:x for x in tree}
auth=read(R/'private/source-authentication.json');assert len(auth)==28
for x in auth:
 assert x['selected'] in rows;b=(A/x['selected']).read_bytes();e=by[x['canonical']]
 assert len(b)==e['size']==x['bytes'] and sha(b)==x['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['sha']==x['blob']
reads=[json.loads(x) for x in (R/'private/reviewer-reads.jsonl').read_bytes().splitlines()];coverage={}
for x in reads:
 assert x['path'] in rows;b=(A/x['path']).read_bytes();ls=b.splitlines(keepends=True);lo,hi=x['start'],x['stop']
 assert sha(b)==x['sha256'] and 1<=lo<=hi<=len(ls) and [sum(map(len,ls[:lo-1])),sum(map(len,ls[:hi]))]==x['bytes']
 assert all(lo<=i<=hi for i in x['omitted'])
 if not x['classification_only']:coverage.setdefault(x['path'],set()).update(set(range(lo,hi+1))-set(x['omitted']))
full=[]
for x in auth:
 n=x['selected']
 if n.endswith('.tex') and not n.endswith('/build/paper.tex'):
  assert coverage[n]==set(range(1,len((A/n).read_bytes().splitlines(keepends=True))+1));full.append(n)
assert len(full)==19
boundaries=read(R/'private/primary-boundary-review.json')
for x in boundaries:
 ls=(A/'private/primary'/(x['name']+'.txt')).read_bytes().splitlines(keepends=True);lo,hi=x['start'],x['stop']
 assert [sum(map(len,ls[:lo-1])),sum(map(len,ls[:hi]))]==x['bytes']
hist=read(R/'private/history-boundaries.json')
for x in hist:
 assert x['path'] in rows;b=(A/x['path']).read_bytes();assert len(b)==x['bytes'] and len(b.splitlines(keepends=True))==x['lines']
controls=[];tiny=R/'private/controls/intact';ta={n:sha((tiny/n).read_bytes()) for n in anchors};assert invoke(tiny,ta)[0]==0
with tempfile.TemporaryDirectory(dir=P,prefix='contribution-copied-controls-') as td:
 root=Path(td)/'tiny';shutil.copytree(tiny,root,copy_function=shutil.copy2);f=root/'control.txt';original=f.read_bytes();mode=stat.S_IMODE(f.stat().st_mode)
 def case(label,expected=ta,reject=False):
  code,_=invoke(root,expected);assert (code!=0)==reject;controls.append({'case':label,'observed':'rejected' if reject else 'accepted'})
 case('intact copied selection');f.chmod(0o600);f.write_bytes(bytes([original[0]^1])+original[1:]);f.chmod(mode);case('same-size byte mutation',reject=True)
 f.chmod(0o600);f.write_bytes(original);case('selected mode mutation',reject=True);f.chmod(mode)
 p=root/'SELECTION.json';sb=p.read_bytes();sm=stat.S_IMODE(p.stat().st_mode);d=json.loads(sb);d['files'].remove('control.txt');p.chmod(0o600);p.write_text(json.dumps(d)+'\n');p.chmod(sm)
 case('reduced selection retaining manifest',dict(ta,**{'SELECTION.json':sha(p.read_bytes())}),True)
 p.chmod(0o600);p.write_bytes(sb);p.chmod(sm);case('restored copied selection');case('wrong detached report anchor',dict(ta,**{'REPORT.md':'0'*64}),True)
assert inventory(R)==before and inventory(A)==abefore and inventory(Q)==qbefore
(P/'contribution-observed-root.json').write_text(json.dumps(before,indent=2)+'\n')
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'review_sha256':sha((R/'REVIEW.md').read_bytes()),'statement_sha256':rows['STATEMENT.md']['sha256'],'author_proof_sha256':rows['AUTHOR-PROOF.md']['sha256'],'selected_review_files':16,'entire_review_files':40,'review_subdirectories':len(before['directories']),'review_verifier':verified,'author_verifier':averified,'admitted_author_files_unchanged':106,'entire_author_files_unchanged':114,'entire_author_subdirectories_unchanged':12,'prior_correctness_review_unchanged':True,'inherited_guard_sets_match':True,'canonical_blobs_authenticated':28,'reviewer_read_records_bound':len(reads),'semantic_read_records_bound':sum(not x['classification_only'] for x in reads),'complete_non_driver_operative_tex_extents':len(full),'primary_boundary_ranges_bound':len(boundaries),'history_boundary_files_bound':len(hist),'reviewer_control_cases':len(read(R/'private/control-results.json')['cases']),'independent_copied_controls':controls,'author_originals_unchanged':True,'review_originals_unchanged':True,'verifier_scope':'Exact explicit selected file identities only; twenty tiny fixture files are unselected extras. Parent separately compares whole observed roots.','semantic_scope':'Full REVIEW, derivation notes, READING-LIMITS, FINAL and outside REPORT read. The positive compatible reduction was assessed against the unchanged frozen theorem and previously read proof. Range/hash checks do not inherit independent semantic or visual coverage. Initial reviewer direct reads are documented manually. Actual metadata, running-header and footnote exposures, late readings and imported unread antecedents remain disclosed. No exhaustive literature/history clearance or proved formal coverage.'}
(P/'contribution-replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
