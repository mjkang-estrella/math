#!/usr/bin/env python3
"""Read-only artifact replay; all mutation controls use temporary parent copies."""
from pathlib import Path
import datetime,hashlib,json,os,stat,subprocess,sys,tempfile
P=Path(__file__).resolve().parent;A=P.parent/'fresh-structural-discovery-r225';C=P.parents[1];PROJECT=C.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(p.read_bytes())
anchors={'FINAL.md':'c40a8758f7d1490eb0d7219c8f46271dd98f99e4abff0ed5932b2238a544fb5e','MANIFEST.json':'5157ccdea785d31b0a2d34220e878d6a6fc0d0544eb83fd5c045f4086dce7cb9','REPORT.md':'4316c60f07e8db66ba09ed8ea37daaa34782747bf0e7bf1ec879309def64f1ab'}
def inventory(root):
 out={'files':{},'directories':{},'root_mode':stat.S_IMODE(root.stat().st_mode)}
 for base,ds,fs in os.walk(root,followlinks=False):
  for n in ds+fs:
   p=Path(base)/n;rel=p.relative_to(root).as_posix();st=p.lstat();assert not stat.S_ISLNK(st.st_mode)
   if stat.S_ISDIR(st.st_mode):out['directories'][rel]={'path':rel,'mode':stat.S_IMODE(st.st_mode)}
   else:
    assert stat.S_ISREG(st.st_mode);b=p.read_bytes();out['files'][rel]={'path':rel,'bytes':len(b),'sha256':sha(b),'mode':stat.S_IMODE(st.st_mode)}
 return out
before=inventory(A);m=read(A/'MANIFEST.json');assert read(A/'ANCHORS.json')['sha256']==anchors
for n,h in anchors.items():assert sha((A/n).read_bytes())==h
outside=set(m['outside_selection']);paths=[x['path'] for x in m['files']];assert paths==sorted(set(paths))
assert set(before['files'])==set(paths)|outside and not set(paths)&outside
for x in m['files']:
 y=dict(x);y.pop('rights');y['mode']=int(y['mode'],8);assert before['files'][x['path']]==y
def invoke(root,expected,copied=False):
 cmd=[sys.executable,'-I','-B',str(root/'verify_packet.py'),'--manifest-sha256',expected['MANIFEST.json'],'--final-sha256',expected['FINAL.md'],'--report-sha256',expected['REPORT.md']]
 if copied:cmd+=['--copied-controls']
 r=subprocess.run(cmd,capture_output=True,text=True);return r.returncode,json.loads(r.stdout) if r.returncode==0 else r.stderr.splitlines()[-1]
code,verified=invoke(A,anchors,True);assert code==0
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=json.loads(tb)['tree'];assert len(tree)==13223;by={x['path']:x for x in tree}
records=read(A/'source-authentication.json');assert len(records)==11
for x in records:
 b=(A/x['local']).read_bytes();e=by[x['path']];assert len(b)==x['bytes']==e['size'] and sha(b)==x['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob']==e['sha']
 assert '/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' in x['url']
prefix='preprints/The-Solomon-Yau-least-volume-theorem-September-23-2026';assert read(A/'source-tree-selection.json')==[x for x in tree if x['path']==prefix or x['path'].startswith(prefix+'/')]
reads=[json.loads(x) for x in (A/'semantic-reads.jsonl').read_bytes().splitlines()]
for x in reads:
 b=(A/x['file']).read_bytes();ls=b.splitlines(keepends=True);ends=[0]
 for l in ls:ends.append(ends[-1]+len(l))
 if 'selected_spans' in x:
  assert sha(b)==x['sha256_file'];edges=set(ends);last=0
  for lo,hi in x['selected_spans']:assert last<=lo<hi<=len(b) and lo in edges and hi in edges;last=hi
 else:
  lo,hi=x['byte_start'],x['byte_end'];assert [ends[x['line_start']-1],ends[x['line_end']]]==[lo,hi] and sha(b[lo:hi])==x['sha256']
section_coverage=[]
for x in records:
 if '/sections/' not in x['local']:continue
 spans=sorted((r['byte_start'],r['byte_end']) for r in reads if r['file']==x['local']);end=0
 for lo,hi in spans:assert lo<=end;end=max(end,hi)
 assert end==x['bytes'];section_coverage.append(x['local'])
primary=[]
for name in ['access.json','access2.json','access3.json','access4.json']:
 j=read(A/'private/primary'/name);primary+=j if isinstance(j,list) else [j]
artifacts=[]
for x in primary:
 if 'sha256' not in x:continue
 local=x.get('local','private/primary/'+(x['file'] if 'file' in x else x.get('id','')+'.pdf'));b=(A/local).read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256']
 if 'text_bytes' in x:assert (A/Path(local).with_suffix('.txt')).stat().st_size==x['text_bytes']
 artifacts.append(local)
assert read(A/'private/history-candidates.json')['sections']==[]
guards=read(A/'guards.json');assert len(guards['wildcards'])==373 and len(guards['substrings'])==162
controls=[]
with tempfile.TemporaryDirectory(dir=P,prefix='copied-controls-') as td:
 r=Path(td);v=r/'verify_packet.py';v.write_bytes((A/'verify_packet.py').read_bytes());v.chmod(0o444)
 f=r/'FINAL.md';data=(A/'FINAL.md').read_bytes();f.write_bytes(data);f.chmod(0o444);report=r/'REPORT.md';report.write_bytes((A/'REPORT.md').read_bytes());report.chmod(0o444)
 rows=[{'path':p.name,'bytes':p.stat().st_size,'sha256':sha(p.read_bytes()),'mode':'0444'} for p in [f,v]]
 manifest=r/'MANIFEST.json';manifest.write_text(json.dumps({'files':rows,'outside_selection':['MANIFEST.json','REPORT.md']}));manifest.chmod(0o444)
 expected={'FINAL.md':sha(data),'MANIFEST.json':sha(manifest.read_bytes()),'REPORT.md':sha(report.read_bytes())}
 def case(label,reject=False,override=None):
  code,result=invoke(r,override or expected);assert (code!=0)==reject,(label,result);controls.append({'case':label,'observed':'rejected' if reject else 'accepted'})
 case('valid independent copied selection');f.chmod(0o644);f.write_bytes(bytes([data[0]^1])+data[1:]);f.chmod(0o444);case('same-size byte mutation',True);f.chmod(0o644);f.write_bytes(data);f.chmod(0o600);case('file mode mutation',True);f.chmod(0o444);extra=r/'extra';extra.write_bytes(b'x');case('extra file',True);extra.unlink();case('wrong detached anchor',True,dict(expected,**{'MANIFEST.json':'0'*64}));case('restored copies')
assert inventory(A)==before
(P/'observed-root.json').write_text(json.dumps(before,indent=2)+'\n')
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'selected_files':len(paths),'outside_selection_files':len(outside),'entire_author_files':len(before['files']),'entire_author_subdirectories':len(before['directories']),'verifier':verified,'verifier_sha256':sha((A/'verify_packet.py').read_bytes()),'canonical_blobs_authenticated':len(records),'source_read_extents_bound':sum(x['file'].startswith('private/source/') for x in reads),'operative_source_sections_fully_covered_by_recorded_ranges':len(section_coverage),'primary_read_extents_bound':sum(x['file'].startswith('private/primary/') for x in reads),'primary_pdfs_authenticated':sum(x.endswith('.pdf') for x in artifacts),'primary_html_artifacts_authenticated':sum(x.endswith('.html') for x in artifacts),'formal_artifacts_authenticated':0,'original_history_extents_bound':0,'copied_controls':controls,'author_originals_unchanged':True,'semantic_scope':'Parent read all five authored prose files and verifier. Authentication and recorded-range checks do not inherit child source/primary/history semantic coverage. No mathematical grade.'}
(P/'replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
