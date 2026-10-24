#!/usr/bin/env python3
"""Read-only artifact replay. Writes only the parent directory and tiny copies."""
from pathlib import Path
import datetime,hashlib,json,os,stat,subprocess,sys,tempfile,shutil
P=Path(__file__).resolve().parent; A=P.parent/'fresh-structural-discovery-r222'; S=A/'sealed'; C=P.parents[1]; PROJECT=C.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest()
read=lambda p:json.loads(p.read_bytes())
anchors={'sealed/FINAL.md':'d2525660f8ee7d2ae5697a75e7fd0a0a2afcfdf23725be7e3b152bc0b4dc4e34','sealed/MANIFEST.json':'59b70539a95a53700cc6792ad03ee3e4002af1ae3fb561ac4bfcdfd791b22f05','REPORT.md':'f2f11610c7c84f25c3b5508e612daa43b0d0e5f2531fd772933b8b5610bce79f'}
def inventory(root):
 out={'files':{},'directories':{'':format(stat.S_IMODE(root.stat().st_mode),'04o')}}
 for base,dirs,files in os.walk(root,followlinks=False):
  for n in dirs+files:
   p=Path(base)/n; rel=p.relative_to(root).as_posix(); st=p.lstat(); assert not stat.S_ISLNK(st.st_mode)
   if stat.S_ISDIR(st.st_mode):out['directories'][rel]=format(stat.S_IMODE(st.st_mode),'04o')
   else:
    assert stat.S_ISREG(st.st_mode); b=p.read_bytes(); out['files'][rel]={'bytes':len(b),'sha256':sha(b),'mode':format(stat.S_IMODE(st.st_mode),'04o')}
 return out
before=inventory(A); selected=inventory(S); m=read(S/'MANIFEST.json')
for n,h in anchors.items():assert sha((A/n).read_bytes())==h
for x in read(A/'ANCHORS.json').values():assert sha((A/x['path']).read_bytes())==x['sha256']
assert sha((A/'verify-packet.py').read_bytes())=='c705751ea84c030be10e6af59426b9d9887a537e693ede29ace19c89654023de'
assert selected['directories']==m['directories'] and set(selected['files'])=={x['path'] for x in m['files']}|{'MANIFEST.json'}
for x in m['files']:assert selected['files'][x['path']]=={k:x[k] for k in ('bytes','sha256','mode')}
def invoke(verifier,root,report,ah):
 cmd=[sys.executable,'-I','-B',str(verifier),'--packet',str(root),'--manifest-sha256',ah['manifest'],'--final-sha256',ah['final'],'--report',str(report),'--report-sha256',ah['report']]
 r=subprocess.run(cmd,capture_output=True,text=True); return r.returncode,json.loads(r.stdout)
ah={'manifest':anchors['sealed/MANIFEST.json'],'final':anchors['sealed/FINAL.md'],'report':anchors['REPORT.md']}
code,verified=invoke(A/'verify-packet.py',S,A/'REPORT.md',ah); assert code==0 and verified['ok']
tree_raw=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tree_raw)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=read(PROJECT/'sources/preprints-tree.json')['tree'];assert len(tree)==13223;by={x['path']:x for x in tree}
records=read(S/'private/authenticated-upstream.json');assert len(records)==29
for x in records:
 b=(S/'private/upstream'/x['path']).read_bytes(); e=by[x['path']]
 assert len(b)==x['bytes']==e['size'] and sha(b)==x['sha256']
 assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob']==e['sha']
 assert '/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' in x['url']
selection=read(S/'private/source-tree-selection.json'); prefixes={x['path'].split('/')[1] for x in records}
assert selection==[x for x in tree if len(x['path'].split('/'))>1 and x['path'].split('/')[1] in prefixes]
def bind_extent(b,x):
 lines=b.splitlines(keepends=True);i=x['line_start']-1;j=x['line_end'];lo=sum(map(len,lines[:i]));hi=sum(map(len,lines[:j]))
 assert (lo,hi)==(x['byte_start'],x['byte_end']) and sha(b[lo:hi])==x['sha256'];return b[lo:hi]
reads=[json.loads(x) for x in (S/'private/semantic-reads.jsonl').read_text().splitlines()]
for x in reads:bind_extent((S/x['path']).read_bytes(),x)
coverage=read(S/'private/source-semantic-coverage.json')
for x in coverage:
 b=(S/x['path']).read_bytes();assert len(b)==x['bytes']
 intervals=sorted([[r['byte_start'],r['byte_end']] for r in reads if r['path']==x['path']]);merged=[]
 for lo,hi in intervals:
  if merged and lo<=merged[-1][1]:merged[-1][1]=max(hi,merged[-1][1])
  else:merged.append([lo,hi])
 assert intervals==sorted(x['selected_intervals']);gaps=[];end=0
 for lo,hi in merged:
  if lo>end:gaps.append([end,lo])
  end=max(end,hi)
 if end<len(b):gaps.append([end,len(b)])
 assert gaps==x['gaps']
primary=[]
access=read(S/'private/primary/access.json')+[json.loads(x) for x in (S/'private/primary/access.jsonl').read_text().splitlines()]
for x in access:
 if 'sha256' not in x:continue
 b=(A/'private/primary'/(x['name']+'.pdf')).read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256'];primary.append(x['name'])
pr=read(S/'private/primary/exact-selection.json');assert len(pr)==26
for x in pr:
 b=(A/x['extraction']).read_bytes();assert sha(b)==x['extraction_sha256'];part=bind_extent(b,x)
 assert (S/'private/primary'/x['selection']).read_bytes()==part
hr=read(S/'private/history-selected-ranges.json')
for x in hr:
 p=PROJECT/x['original']
 with p.open('rb') as f:f.seek(x['start']);b=f.read(x['end']-x['start'])
 assert len(b)==x['bytes'] and sha(b)==x['sha256']
 assert (S/'private/history'/Path(x['selected_copy']).name).read_bytes()==b
assert sha((S/'private/direct-inputs/acceptance-4801-6347.txt').read_bytes())=='f147924a01d36cce7ad5ee13bad6ed9ed9109f3bf4b5c2386fc318aae1330984'
assert sha((S/'private/source346-catalogue.txt').read_bytes())=='7969d1fe9ee4ba8f5c439a2d7eab1f410d9ae180997b7d34ce6ddddf12ab4789'
controls=[]
with tempfile.TemporaryDirectory(dir=P,prefix='copied-controls-') as td:
 root=Path(td);v=root/'verify.py';v.write_bytes((A/'verify-packet.py').read_bytes());packet=root/'packet';packet.mkdir();private=packet/'private';private.mkdir();f=packet/'FINAL.md';f.write_bytes((S/'FINAL.md').read_bytes());g=private/'sample.bin';g.write_bytes(b'local copied fixture\n');g.chmod(0o400);report=root/'REPORT.md';report.write_bytes((A/'REPORT.md').read_bytes());report.chmod(0o444)
 inv=inventory(packet);fixture={'schema':'r222-exact-selection-v1','files':[dict(path=n,**r) for n,r in inv['files'].items()],'directories':inv['directories']};manifest=packet/'MANIFEST.json';manifest.write_text(json.dumps(fixture));manifest.chmod(0o444)
 expected={'manifest':sha(manifest.read_bytes()),'final':sha(f.read_bytes()),'report':sha(report.read_bytes())}
 def case(label,reject=False,override=None):
  code,result=invoke(v,packet,report,override or expected);assert (code!=0)==reject,(label,result);controls.append({'case':label,'observed':'rejected' if reject else 'accepted','result':result})
 case('tiny independent copied selection');data=f.read_bytes();f.write_bytes(bytes([data[0]^1])+data[1:]);case('same-size byte mutation',True);f.write_bytes(data);g.chmod(0o600);case('private file mode mutation',True);g.chmod(0o400);extra=packet/'extra';extra.write_bytes(b'x');case('extra file',True);extra.unlink();case('incorrect detached manifest anchor',True,dict(expected,manifest='0'*64));case('restored copies')
assert inventory(A)==before
(P/'observed-root.json').write_text(json.dumps(before,indent=2)+'\n')
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'selected_files':len(m['files']),'selected_directories':len(m['directories']),'entire_author_files':len(before['files']),'entire_author_directories':len(before['directories']),'verifier':verified,'author_verifier_sha256':sha((A/'verify-packet.py').read_bytes()),'canonical_blobs_authenticated':len(records),'source_read_extents_bound':len(reads),'source_coverage_records_bound':len(coverage),'primary_read_extents_bound':len(pr),'primary_artifacts_authenticated':primary,'original_history_extents_bound':len(hr),'copied_controls':controls,'author_originals_unchanged':True,'semantic_scope':'Parent read all four sealed authored prose files and outside REPORT, verifier and applicable metadata. Byte authentication of source/primary/history and recorded read extents does not inherit child semantic coverage. No mathematical grade.'}
(P/'replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
