#!/usr/bin/env python3
"""Read-only Structural235 intake; no mathematical grades."""
from pathlib import Path
import datetime,hashlib,json,os,runpy,shutil,stat,subprocess,sys,tempfile
P=Path(__file__).resolve().parent;A=P.parent/'fresh-structural-discovery-r235';C=P.parents[1];PROJECT=C.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(p.read_bytes())
anchors={'FINAL.md':'5373390d822df98b6af8e46da6653a4049a0c66bebd8b3ec33b6b188abd32bb3','MANIFEST.json':'241075fd7cd7aa75f44a2ce40884c57c29264b04765268ada3979df3025b8f06','REPORT.md':'0b17bfd50d3192a82d3c5b75693e2e32173f622fa26a05f9f0badcf963698f66'}
def inventory(root):
 out={'root_mode':stat.S_IMODE(root.stat().st_mode),'files':{},'directories':{}}
 for base,ds,fs in os.walk(root,followlinks=False):
  for n in ds+fs:
   p=Path(base)/n;rel=p.relative_to(root).as_posix();st=p.lstat();assert not stat.S_ISLNK(st.st_mode)
   if stat.S_ISDIR(st.st_mode):out['directories'][rel]=stat.S_IMODE(st.st_mode)
   else:
    assert stat.S_ISREG(st.st_mode);b=p.read_bytes();out['files'][rel]={'bytes':len(b),'sha256':sha(b),'mode':stat.S_IMODE(st.st_mode)}
 return out
before=inventory(A);m=read(A/'MANIFEST.json');assert len(m['files'])==93
def invoke(expected):
 args=[sys.executable,'-I','-B',str(A/'verify_packet.py'),'--root',str(A)]
 for arg,n in [('final','FINAL.md'),('manifest','MANIFEST.json'),('report','REPORT.md')]:args+=['--'+arg+'-sha256',expected[n]]
 r=subprocess.run(args,capture_output=True,text=True);return r.returncode,json.loads(r.stdout)if r.returncode==0 else r.stderr.strip()
code,verified=invoke(anchors);assert code==0
treebytes=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(treebytes)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=json.loads(treebytes)['tree'];assert len(tree)==13223;by={x['path']:x for x in tree}
records=read(A/'private/authenticated.json');assert len(records)==28
for x in records:
 b=(A/'private/canonical'/x['path']).read_bytes();e=by[x['path']];assert len(b)==x['bytes']==e['size']and sha(b)==x['sha256']and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob']==e['sha'];assert '/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'in x['url']
prefixes=['preprints/A-negatively-pinched-Kahler-threefold-without-bounded-holomorphic-coordinates-September-25-2026','preprints/One-sided-negative-sectional-curvature-and-the-holomorphic-Liouville-property-September-25-2026'];assert read(A/'private/tree-selection.json')==[x for x in tree if any(x['path']==p or x['path'].startswith(p+'/')for p in prefixes)]
reads=[json.loads(x)for x in(A/'private/read-extents.jsonl').read_bytes().splitlines()]
for x in reads:
 b=(A/'private/canonical'/x['path']).read_bytes();lo,hi=x['bytes_halfopen'];i,j=x['lines_inclusive'];ls=b.splitlines(keepends=True);assert[sum(map(len,ls[:i-1])),sum(map(len,ls[:j]))]==[lo,hi]and sha(b[lo:hi])==x['sha256']
coverage=read(A/'private/source-coverage.json');assert len(coverage)==24
for x in coverage:
 b=(A/'private/canonical'/x['path']).read_bytes();spans=sorted(r['bytes_halfopen']for r in reads if r['path']==x['path']);end=0;gaps=[]
 for lo,hi in spans:
  if lo>end:gaps.append([end,lo])
  end=max(end,hi)
 if end<len(b):gaps.append([end,len(b)])
 assert gaps==x['uncovered_bytes'];assert not gaps or x['driver']
primary=[json.loads(x)for x in(A/'private/primary-read-extents.jsonl').read_bytes().splitlines()];displayed=masked=0
for x in primary:
 b=(A/'private/primary'/(x['name']+'.txt')).read_bytes();lo,hi=x['bytes'];i,j=x['lines'];ls=b.splitlines(keepends=True);assert[sum(map(len,ls[:i-1])),sum(map(len,ls[:j]))]==[lo,hi]and sha(b[lo:hi])==x['sha256'];offset=lo;expected=[]
 for line in ls[i-1:j]:expected.append((offset,offset+len(line)));offset+=len(line)
 assert[(r['start'],r['end'])for r in x['spans']]==expected;displayed+=sum(r['displayed']for r in x['spans']);masked+=sum(not r['displayed']for r in x['spans'])
pdfs=[]
for x in read(A/'private/primary-access.json')+read(A/'private/primary-access-02.json'):
 if x.get('error'):continue
 b=(A/'private/primary'/(x['name']+'.pdf')).read_bytes();assert len(b)==x['bytes']and sha(b)==x['sha256'];assert len((A/'private/primary'/(x['name']+'.txt')).read_bytes())==x.get('extraction_bytes',x.get('text_bytes'));pdfs.append(x['name'])
g=read(A/'guards.json');assert len(g['full_path_casefold_wildcards'])==393 and len(g['full_path_casefold_substrings'])==162
for n in [1,2]:assert read(A/f'private/history-navigation-0{n}.json')['guards_sha256']==sha((A/'guards.json').read_bytes())
history=read(A/'private/history-reading-01.json')
for n,x in enumerate(history,1):
 b=(A/f'private/history-selected-01-{n}.txt').read_bytes();assert len(b)==x['bytes'][1]-x['bytes'][0]and sha(b)==x['sha256']
for x in read(A/'private/lean-access.json'):
 b=(A/'private'/x['local']).read_bytes();assert len(b)==x['bytes']and sha(b)==x['sha256']
assert(A/'private/PinchedKahler.lean').read_text().count(':= by\n  sorry')==3
verify=runpy.run_path(str(A/'verify_packet.py'))['verify'];tiny=A/'controls/tiny';tinyanchors=read(tiny/'ANCHORS.json');assert verify(tiny,tinyanchors)['files']==2;controls=[]
with tempfile.TemporaryDirectory(dir=P,prefix='copied-controls-')as td:
 root=Path(td)/'specimen';shutil.copytree(tiny,root,copy_function=shutil.copy2);f=root/'payload.txt';original=f.read_bytes()
 def case(label,reject=False):
  try:verify(root,tinyanchors);failed=False
  except ValueError:failed=True
  assert failed==reject;controls.append({'case':label,'observed':'rejected'if reject else'accepted'})
 case('copied tiny packet');f.chmod(0o644);f.write_bytes(bytes([original[0]^1])+original[1:]);f.chmod(0o444);case('same-size byte mutation',True);f.chmod(0o644);f.write_bytes(original);case('file mode mutation',True);f.chmod(0o444);extra=root/'extra';extra.write_bytes(b'x');case('extra file',True);extra.unlink();extra.mkdir();case('extra directory',True);extra.rmdir();root.chmod(0o755);case('root mode mutation',True);root.chmod(0o700);case('restored tiny packet')
code,_=invoke(dict(anchors,**{'MANIFEST.json':'0'*64}));assert code!=0
assert inventory(A)==before;(P/'observed-root.json').write_text(json.dumps(before,indent=2)+'\n')
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'selected_files':len(m['files']),'selected_directories_including_root':len(m['directories']),'entire_author_files':len(before['files']),'entire_author_subdirectories':len(before['directories']),'verifier':verified,'verifier_sha256':sha((A/'verify_packet.py').read_bytes()),'canonical_blobs_authenticated':len(records),'source_read_intervals_bound':len(reads),'non_driver_tex_bib_completely_covered':sum(not x['driver']for x in coverage),'driver_coverage_bound':2,'primary_read_intervals_bound':len(primary),'primary_displayed_line_ranges_bound':displayed,'primary_masked_line_ranges_bound':masked,'primary_pdfs_authenticated':pdfs,'independent_history_pass_records_bound':2,'copied_original_history_ranges_bound':len(history),'formal_support':'none; three declarations end in sorry','author_tiny_packet_replayed':True,'independent_copied_controls':controls,'wrong_detached_anchor_rejected':True,'author_originals_unchanged':True,'semantic_scope':'Full authored derivation, comparison, reading limits, FINAL and REPORT read. Authentication of source/primary/history ranges and visual files does not inherit semantic or visual reading. Writing passage readers and seal script were not executed. No mathematical grades or count.'}
(P/'replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
