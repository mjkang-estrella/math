#!/usr/bin/env python3
"""Read-only parent replay, with isolated copied controls and arithmetic checks."""
from pathlib import Path
import datetime,hashlib,json,os,stat,subprocess,sys,tempfile
P=Path(__file__).resolve().parent;A=P.parent/'fresh-structural-discovery-r223';S=A/'packet';C=P.parents[1];PROJECT=C.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(p.read_bytes())
anchors={'packet/FINAL.md':'f5fd5bce5d540044eaab2a5f73b97428acfe75c961efc82d9b735165bc7d8acf','MANIFEST.json':'9e39cf53ebc5db1ee45c9a0a243d7ccea942984f5dc3b8a496bae7ccbef32171','REPORT.md':'fcffb73082b436be20dbba55d5018f44b8599d3eb32f37b3967d3120684865b8'}
def inventory(root):
 files={};dirs={'.':format(stat.S_IMODE(root.stat().st_mode),'04o')}
 for base,ds,fs in os.walk(root,followlinks=False):
  for n in ds+fs:
   p=Path(base)/n;rel=p.relative_to(root).as_posix();st=p.lstat();assert not stat.S_ISLNK(st.st_mode)
   if stat.S_ISDIR(st.st_mode):dirs[rel]=format(stat.S_IMODE(st.st_mode),'04o')
   else:
    assert stat.S_ISREG(st.st_mode);b=p.read_bytes();files[rel]={'path':rel,'bytes':len(b),'sha256':sha(b),'mode':format(stat.S_IMODE(st.st_mode),'04o')}
 return {'files':files,'directories':dirs}
before=inventory(A);selected=inventory(S);m=read(A/'MANIFEST.json')
assert read(A/'ANCHORS.json')['sha256']==anchors
for n,h in anchors.items():assert sha((A/n).read_bytes())==h
assert selected['files']=={x['path']:x for x in m['files']} and selected['directories']==m['directories']
def invoke(root,manifest,report,expected):
 cmd=[sys.executable,'-I','-B',str(S/'verify_packet.py'),'--root',str(root),'--manifest',str(manifest),'--final','FINAL.md','--report',str(report),'--manifest-sha256',expected['manifest'],'--final-sha256',expected['final'],'--report-sha256',expected['report']]
 r=subprocess.run(cmd,capture_output=True,text=True);return {'exit':r.returncode,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()}
expected={'manifest':anchors['MANIFEST.json'],'final':anchors['packet/FINAL.md'],'report':anchors['REPORT.md']};verified=invoke(S,A/'MANIFEST.json',A/'REPORT.md',expected);assert verified['exit']==0
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=json.loads(tb)['tree'];assert len(tree)==13223;by={x['path']:x for x in tree}
records=read(S/'private/blob-authentication.json');assert len(records)==51
for x in records:
 b=(S/'private/upstream'/x['path']).read_bytes();e=by[x['path']];assert len(b)==x['bytes']==e['size'] and sha(b)==x['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob']==e['sha']
 assert '/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' in x['url']
prefixes={x['path'].split('/')[1] for x in records};selection=read(S/'private/tree-selection.json');assert selection==[x for x in tree if len(x['path'].split('/'))>1 and x['path'].split('/')[1] in prefixes]
def extent(b,x):
 ls=b.splitlines(keepends=True);offs=[0]
 for l in ls:offs.append(offs[-1]+len(l))
 assert (offs[x['first_line']-1],offs[x['last_line']])==(x['start'],x['end']) and sha(b[x['start']:x['end']])==x['sha256'];return offs
reads=[json.loads(x) for x in (S/'private/semantic-reads.jsonl').read_text().splitlines()]
for x in reads:extent((S/'private/upstream'/x['path']).read_bytes(),x)
complete=[]
for x in records:
 if not x['path'].endswith(('.tex','.bib')) or x['path'].endswith('/main.tex'):continue
 ints=sorted((a['start'],a['end']) for a in reads if a['path']==x['path']);end=0
 for lo,hi in ints:assert lo<=end;end=max(end,hi)
 assert end==x['bytes'];complete.append(x['path'])
drivers=[json.loads(x) for x in (S/'private/driver-reads.jsonl').read_text().splitlines()]
for x in drivers:
 b=(S/'private/upstream'/x['path']).read_bytes();assert all(0<=lo<hi<=len(b) for lo,hi in x['math_ranges'])
primary=[]
for x in read(S/'private/primary/access.json')+read(S/'private/primary/late-access.json'):
 if not x['ok']:continue
 for suffix,lk,hk in [('.pdf','bytes','sha256'),('.txt','text_bytes','text_sha256')]:
  b=(S/'private/primary'/(x['id']+suffix)).read_bytes();assert len(b)==x[lk] and sha(b)==x[hk]
 primary.append(x['id'])
pr=[json.loads(x) for x in (S/'private/primary/semantic-reads.jsonl').read_text().splitlines()]
for x in pr:
 b=(S/'private/primary'/(x['id']+'.txt')).read_bytes();offs=extent(b,x)
 assert x['read_ranges']==[[offs[i-1],offs[i]] for i in range(x['first_line'],x['last_line']+1) if str(i) not in x['masks']]
for meta,target in [('private/lean347-authentication.json','private/lean347.md'),('private/comparator-authentication.json','private/ArnoldCounterexample.lean')]:
 x=read(S/meta);b=(S/target).read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob']
assert read(S/'private/history-selection.json')['semantic_bodies_read']==0
assert sha((S/'private/source347-catalogue.txt').read_bytes())=='aafa4ffe0062b139d3ae2fc799d9fcbeb0d220ee862f58edbd27d48d5c7c9033'
controls=[];arithmetic=[]
with tempfile.TemporaryDirectory(dir=P,prefix='copied-controls-') as td:
 r=Path(td);root=r/'fixture';root.mkdir();f=root/'FINAL.md';data=(S/'FINAL.md').read_bytes();f.write_bytes(data);f.chmod(0o400);report=r/'REPORT.md';report.write_bytes((A/'REPORT.md').read_bytes());manifest=r/'MANIFEST.json';inv=inventory(root);manifest.write_text(json.dumps({'schema':1,'final':'FINAL.md','files':list(inv['files'].values()),'directories':inv['directories']}));e={'manifest':sha(manifest.read_bytes()),'final':sha(data),'report':sha(report.read_bytes())}
 def case(label,reject=False,override=None):
  out=invoke(root,manifest,report,override or e);assert (out['exit']!=0)==reject,(label,out);controls.append({'case':label,'observed':'rejected' if reject else 'accepted'})
 case('unaltered copied selection');f.chmod(0o600);f.write_bytes(bytes([data[0]^1])+data[1:]);f.chmod(0o400);case('same-size byte alteration',True);f.chmod(0o600);f.write_bytes(data);case('file mode alteration',True);f.chmod(0o400);extra=root/'extra';extra.write_bytes(b'x');case('extra file',True);extra.unlink();case('wrong detached anchor',True,dict(e,manifest='0'*64));case('restored copies')
 work=r/'arithmetic';work.mkdir();(work/'private').mkdir()
 for script,output in [('arithmetic.py','arithmetic-results.json'),('threefold_algebra.py','threefold-algebra.json')]:
  (work/script).write_bytes((S/script).read_bytes());run=subprocess.run([sys.executable,'-I','-B',str(work/script)],capture_output=True,text=True);assert run.returncode==0,(script,run.stderr);assert (work/'private'/output).read_bytes()==(S/'private'/output).read_bytes();arithmetic.append({'script':script,'result':'exact saved output reproduced on parent copies; not proof certification'})
assert inventory(A)==before
(P/'observed-root.json').write_text(json.dumps(before,indent=2)+'\n')
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'selected_files':len(m['files']),'selected_directories':len(m['directories']),'entire_author_files':len(before['files']),'entire_author_directories':len(before['directories']),'verifier':json.loads(verified['stdout']),'verifier_sha256':sha((S/'verify_packet.py').read_bytes()),'canonical_blobs_authenticated':len(records),'source_read_extents_bound':len(reads),'complete_non_driver_tex_bib_byte_coverage':len(complete),'driver_range_records_bound':len(drivers),'primary_read_extents_bound':len(pr),'primary_artifacts_authenticated':primary,'formal_artifacts_authenticated':2,'original_history_bodies_admitted':0,'copied_controls':controls,'copied_arithmetic_checks':arithmetic,'author_originals_unchanged':True,'semantic_scope':'Parent read all four authored prose files, outside REPORT, verifier and arithmetic code. Authentication/coverage-range checks do not inherit child source/primary semantic reading. No mathematical grade.'}
(P/'replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
