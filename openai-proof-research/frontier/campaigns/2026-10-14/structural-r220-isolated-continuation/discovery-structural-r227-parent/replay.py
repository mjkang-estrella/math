#!/usr/bin/env python3
"""Read-only parent replay; mutation checks use small independent copies."""
from pathlib import Path
import datetime,fnmatch,hashlib,json,os,stat,subprocess,sys,tempfile
P=Path(__file__).resolve().parent;A=P.parent/'fresh-structural-discovery-r227';S=A/'packet';C=P.parents[1];PROJECT=C.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(p.read_bytes())
anchors={'FINAL.md':'6c8b021d0317c47c34a3e7b324448f316a2eb471b320095ba68028d8d6766385','MANIFEST.json':'83e33f404d00a5bc4e130b076efe89015f44ba9ba045117b20f8dfa0d78c1a7e','REPORT.md':'e88bb26e0764653dcfb4fce57316cc2a8e6c7e5b7dffbc7178c3a1172b5beaab'}
def inventory(root):
 out={'files':{},'directories':{},'root_mode':stat.S_IMODE(root.stat().st_mode)}
 for base,ds,fs in os.walk(root,followlinks=False):
  for n in ds+fs:
   p=Path(base)/n;rel=p.relative_to(root).as_posix();st=p.lstat();assert not stat.S_ISLNK(st.st_mode)
   if stat.S_ISDIR(st.st_mode):out['directories'][rel]={'path':rel,'type':'directory','mode':stat.S_IMODE(st.st_mode)}
   else:
    assert stat.S_ISREG(st.st_mode);b=p.read_bytes();out['files'][rel]={'path':rel,'type':'file','bytes':len(b),'sha256':sha(b),'mode':stat.S_IMODE(st.st_mode)}
 return out
before=inventory(A);selected=inventory(S);m=read(A/'MANIFEST.json');assert read(A/'ANCHORS.json')==anchors
for n,h in anchors.items():assert sha((A/n).read_bytes())==h
assert sorted([*selected['files'].values(),*selected['directories'].values()],key=lambda x:x['path'])==m['entries'] and selected['root_mode']==m['packet_mode']
duplicates=0
for rel,x in selected['files'].items():
 if (A/rel).is_file():assert sha((A/rel).read_bytes())==x['sha256'];duplicates+=1
def invoke(root,expected):
 r=subprocess.run([sys.executable,'-I','-B',str(S/'verify_packet.py'),'--root',str(root),'--manifest-sha256',expected['MANIFEST.json'],'--final-sha256',expected['FINAL.md'],'--report-sha256',expected['REPORT.md']],capture_output=True,text=True)
 return r.returncode,json.loads(r.stdout)
code,verified=invoke(A,anchors);assert code==0
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=json.loads(tb)['tree'];assert len(tree)==13223;by={x['path']:x for x in tree}
records=read(S/'authentication.json');assert len(records)==38
for x in records:
 b=(S/'private'/x['path']).read_bytes();e=by[x['path']];assert len(b)==x['bytes']==e['size'] and sha(b)==x['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob_sha1']==e['sha']
 assert '/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' in x['url']
prefixes={x['path'].split('/')[1] for x in records};assert read(S/'tree-selection.json')==[x for x in tree if len(x['path'].split('/'))>1 and x['path'].split('/')[1] in prefixes]
def check_extent(b,x):
 ls=b.splitlines(keepends=True);a,z=x['lines'];lo,hi=x['bytes'];assert [sum(map(len,ls[:a-1])),sum(map(len,ls[:z]))]==[lo,hi] and sha(b[lo:hi])==x['sha256']
reads=[json.loads(x) for x in (S/'reads.jsonl').read_bytes().splitlines()]
for x in reads:check_extent((S/'private'/x['path']).read_bytes(),x)
coverage=[]
for x in records:
 p=Path(x['path'])
 if p.suffix not in {'.tex','.bib'} or p.name=='paper.tex':continue
 spans=sorted(r['bytes'] for r in reads if r['path']==x['path']);end=0
 for lo,hi in spans:assert lo<=end;end=max(end,hi)
 assert end==x['bytes'];coverage.append(x['path'])
edges=read(S/'include-graph.json');known={x['path'] for x in records}
for x in edges:
 b=(S/'private'/x['from']).read_bytes();off=x['source_byte'];assert x['target'].encode() in b[off:off+len(x['target'])+40] and all(y in known for y in x['authenticated_matches']) and x['authenticated_matches']
primary=S/'private/primary';artifacts=[]
for x in read(primary/'access.json'):
 p=primary/(x['id']+'.src');b=p.read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256'];artifacts.append(p.name)
for x in read(primary/'pdf-access.json'):
 p=primary/(x['name']+'.pdf');b=p.read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256'];artifacts.append(p.name)
extra=read(primary/'additional-access-and-visual-reads.json')
for name in ['2007.09937v1.src','DO-v1.tex']:
 b=(primary/name).read_bytes();assert len(b)==extra[name]['bytes'] and sha(b)==extra[name]['sha256'];artifacts.append(name)
x=read(primary/'Wang-access.json');b=(primary/'0704.3018v2.src').read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256'];artifacts.append('0704.3018v2.src')
pr=[json.loads(x) for x in (S/'primary-reads.jsonl').read_bytes().splitlines()]
for x in pr:check_extent((primary/x['path']).read_bytes(),x)
guards=read(S/'guards.json');assert len(guards['wildcards'])==377 and len(guards['substrings'])==162
rel='frontier/iterations/i80-geometric-flows-computation-discovery.md';assert not any(fnmatch.fnmatchcase(rel.casefold(),g.casefold()) for g in guards['wildcards']);assert not any(g.casefold() in rel.casefold() for g in guards['substrings'])
with (PROJECT/rel).open('rb') as f:f.seek(7726);history=f.read(10286-7726)
assert history==(S/'private/i80-r-section.txt').read_bytes()
assert sha((S/'acceptance.txt').read_bytes())=='f147924a01d36cce7ad5ee13bad6ed9ed9109f3bf4b5c2386fc318aae1330984';assert sha((S/'source351.txt').read_bytes())=='5a5cc7949d1c41b1e022ecda353d992c3443eacc11c74bfa49556d6f6316ee63'
author_controls=[]
for label,reject in [('base',False),('bad-hash',True),('bad-mode',True),('extra-file',True)]:
 r=A/'controls'/label;expected={n:sha((r/n).read_bytes()) for n in anchors};code,result=invoke(r,expected);assert (code!=0)==reject;author_controls.append({'case':label,'observed':'rejected' if reject else 'accepted'})
controls=[]
with tempfile.TemporaryDirectory(dir=P,prefix='copied-controls-') as td:
 r=Path(td);packet=r/'packet';packet.mkdir();content=packet/'MATH.txt';original=b'local copied integrity control\n';content.write_bytes(original);content.chmod(0o600)
 for n in ['FINAL.md','REPORT.md']:(r/n).write_bytes((A/n).read_bytes())
 inv=inventory(packet);manifest=r/'MANIFEST.json';manifest.write_text(json.dumps({'format':'r227-exact-selected-packet-v1','packet':'packet','packet_mode':inv['root_mode'],'entries':list(inv['files'].values())}));expected={n:sha((r/n).read_bytes()) for n in anchors}
 def case(label,reject=False,override=None):
  code,result=invoke(r,override or expected);assert (code!=0)==reject,(label,result);controls.append({'case':label,'observed':'rejected' if reject else 'accepted'})
 case('valid independent copied selection');content.write_bytes(bytes([original[0]^1])+original[1:]);case('same-size byte mutation',True);content.write_bytes(original);content.chmod(0o644);case('file mode mutation',True);content.chmod(0o600);extra_file=packet/'extra';extra_file.write_bytes(b'x');case('extra file',True);extra_file.unlink();case('wrong detached anchor',True,dict(expected,**{'MANIFEST.json':'0'*64}));case('restored copies')
assert inventory(A)==before
(P/'observed-root.json').write_text(json.dumps(before,indent=2)+'\n')
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'selected_files':len(selected['files']),'selected_subdirectories':len(selected['directories']),'entire_author_files':len(before['files']),'entire_author_subdirectories':len(before['directories']),'selected_files_matching_unselected_originals':duplicates,'verifier':verified,'verifier_sha256':sha((S/'verify_packet.py').read_bytes()),'canonical_blobs_authenticated':len(records),'source_read_extents_bound':len(reads),'non_driver_tex_bib_files_fully_covered_by_recorded_ranges':len(coverage),'literal_include_edges_bound':len(edges),'primary_read_extents_bound':len(pr),'primary_artifacts_authenticated':artifacts,'recorded_visual_crops':len(extra['visual_reads']),'formal_artifacts_authenticated':0,'original_history_ranges_bound':1,'author_copied_controls_replayed':author_controls,'independent_copied_controls':controls,'author_originals_unchanged':True,'semantic_scope':'Parent read DERIVATIONS and READING-NOTES completely, bound equal packet copies, and read FINAL, outside REPORT and verifier. Authentication and recorded-range checks do not inherit child source/primary/history semantic coverage. No mathematical grade.'}
(P/'replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
