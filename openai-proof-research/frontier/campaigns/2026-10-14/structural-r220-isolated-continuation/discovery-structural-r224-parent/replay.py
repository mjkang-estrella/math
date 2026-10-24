#!/usr/bin/env python3
"""Read-only parent artifact replay; mutation controls use tiny parent copies."""
from pathlib import Path
import datetime,hashlib,json,os,stat,subprocess,sys,tempfile
P=Path(__file__).resolve().parent;A=P.parent/'fresh-structural-discovery-r224';S=A/'packet';C=P.parents[1];PROJECT=C.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(p.read_bytes())
anchors={'FINAL.md':'b570ab4edd694c659f3d248cb171c57886188c3d5fed8525b9aa219152a65249','MANIFEST.json':'41c0284bae1499e8653f952357a9720694a025131ccfbc07f0b6ad630010ade6','REPORT.md':'014f614f8f8134fb7b009ca9590feaf72cbaae165f81d09ab12adf6dd319ad84'}
def inventory(root):
 out={'files':{},'directories':{},'root_mode':stat.S_IMODE(root.stat().st_mode)}
 for base,ds,fs in os.walk(root,followlinks=False):
  for n in ds+fs:
   p=Path(base)/n;rel=p.relative_to(root).as_posix();st=p.lstat();assert not stat.S_ISLNK(st.st_mode)
   if stat.S_ISDIR(st.st_mode):out['directories'][rel]={'path':rel,'mode':stat.S_IMODE(st.st_mode)}
   else:
    assert stat.S_ISREG(st.st_mode);b=p.read_bytes();out['files'][rel]={'path':rel,'bytes':len(b),'sha256':sha(b),'mode':stat.S_IMODE(st.st_mode)}
 return out
before=inventory(A);selected=inventory(S);m=read(A/'MANIFEST.json');assert read(A/'ANCHORS.json')==anchors
for name,h in anchors.items():assert sha(((S if name=='FINAL.md' else A)/name).read_bytes())==h
assert selected['files']=={x['path']:x for x in m['files']} and selected['directories']=={x['path']:x for x in m['directories']} and selected['root_mode']==m['root_mode']
def invoke(root,expected):
 cmd=[sys.executable,'-I','-B',str(S/'verify_packet.py'),'--root',str(root),'--manifest-sha256',expected['MANIFEST.json'],'--final-sha256',expected['FINAL.md'],'--report-sha256',expected['REPORT.md']]
 r=subprocess.run(cmd,capture_output=True,text=True);return r.returncode,json.loads(r.stdout if r.returncode==0 else r.stderr)
code,verified=invoke(A,anchors);assert code==0
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=json.loads(tb)['tree'];assert len(tree)==13223;by={x['path']:x for x in tree}
records=read(S/'private/authenticated-52.json');assert len(records)==52
for x in records:
 b=(S/'private/canonical'/x['path']).read_bytes();e=by[x['path']];assert len(b)==x['bytes']==e['size'] and sha(b)==x['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob_sha1']==e['sha']
 assert '/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' in x['url']
prefixes={x['path'].split('/')[1] for x in records};assert read(S/'private/selected-tree.json')==[x for x in tree if len(x['path'].split('/'))>1 and x['path'].split('/')[1] in prefixes]
def check_extent(b,lines,interval,h):
 ls=b.splitlines(keepends=True);lo,hi=lines;a=sum(map(len,ls[:lo-1]));z=sum(map(len,ls[:hi-1]));assert [a,z]==interval and sha(b[a:z])==h
reads=[json.loads(x) for x in (S/'private/semantic-reads.jsonl').read_text().splitlines()]
mapped=0
for x in reads:
 b=(S/'private/canonical'/x['path']).read_bytes();check_extent(b,x['lines'],x['bytes'],x['sha256'])
 if 'source_path' in x:
  sb=(S/'private/canonical'/x['source_path']).read_bytes();lo,hi=x['source_bytes'];a,z=x['bytes'];assert b[a:z]==sb[lo:hi]
  direct=sorted(y['bytes'] for y in reads if y['path']==x['source_path'] and y['mode']=='semantic-display');end=lo
  for l,r in direct:
   if l<=end:end=max(end,r)
  assert end>=hi;mapped+=1
maps=read(S/'private/parallel-text-map.json')
for x in maps:
 l=(S/'private/canonical'/x['zero']).read_bytes().splitlines(keepends=True);r=(S/'private/canonical'/x['positive']).read_bytes().splitlines(keepends=True)
 for tag,a,b,c,d in x['opcodes']:
  if tag=='equal':assert l[a:b]==r[c:d]
primary=read(S/'private/primary/retrieval.json')
for key in ['chan-chen-lee-v3','gursky-viaclovsky','slice-survey','cheeger-ziller','topping-compactness']:
 x=read(S/f'private/primary/{key}-receipt.json');x['key']=key;primary.append(x)
for x in primary:
 b=(S/'private/primary'/(x['key']+'.pdf')).read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256']
 if 'text_bytes' in x:assert (S/'private/primary'/(x['key']+'.txt')).stat().st_size==x['text_bytes']
pr=[json.loads(x) for x in (S/'private/primary-read-extents.jsonl').read_text().splitlines()]
for x in pr:
 b=(S/x['file']).read_bytes();check_extent(b,x['outer_lines'],x['outer_bytes'],x['outer_sha256']);lo,hi=x['outer_bytes'];assert all(lo<=a<z<=hi for a,z in x['selected_byte_extents'])
hr=[json.loads(x) for x in (S/'private/original-read-extents.jsonl').read_text().splitlines()]
copies={(x['sha256'],x['bytes']) for n,x in selected['files'].items() if n.startswith('private/original-selected/')}
for x in hr:
 lo,hi=x['bytes']
 with (PROJECT/x['path']).open('rb') as f:f.seek(lo);b=f.read(hi-lo)
 assert sha(b)==x['sha256'] and (sha(b),len(b)) in copies
for meta,target in [('private/lean-navigation-receipt.json','lean/docs/348.md'),('private/comparator-auth.json','lean/ComparatorChallenges/EinsteinFour.lean')]:
 x=read(S/meta);b=(S/'private/canonical'/target).read_bytes();assert sha(b)==x['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob_sha1']
assert sha((S/'private/acceptance-selection.txt').read_bytes())=='f147924a01d36cce7ad5ee13bad6ed9ed9109f3bf4b5c2386fc318aae1330984'
assert sha((S/'private/Source348.txt').read_bytes())=='2e39e5ad60631949c0150a6241ce66c8ff738ed754387d612a2572471a374e23'
controls=[]
with tempfile.TemporaryDirectory(dir=P,prefix='copied-controls-') as td:
 r=Path(td);packet=r/'packet';packet.mkdir();f=packet/'FINAL.md';data=(S/'FINAL.md').read_bytes();f.write_bytes(data);f.chmod(0o644);report=r/'REPORT.md';report.write_bytes((A/'REPORT.md').read_bytes());report.chmod(0o644);inv=inventory(packet);manifest=r/'MANIFEST.json';manifest.write_text(json.dumps({'schema':'r224.exact-packet.v1','packet_root':'packet','files':list(inv['files'].values()),'directories':list(inv['directories'].values()),'root_mode':inv['root_mode']}));manifest.chmod(0o644);expected={'FINAL.md':sha(data),'MANIFEST.json':sha(manifest.read_bytes()),'REPORT.md':sha(report.read_bytes())}
 def case(label,reject=False,override=None):
  code,result=invoke(r,override or expected);assert (code!=0)==reject,(label,result);controls.append({'case':label,'observed':'rejected' if reject else 'accepted'})
 case('valid independent copied selection');f.write_bytes(bytes([data[0]^1])+data[1:]);case('same-size byte mutation',True);f.write_bytes(data);f.chmod(0o600);case('file mode mutation',True);f.chmod(0o644);extra=packet/'extra';extra.write_bytes(b'x');case('extra file',True);extra.unlink();case('wrong detached anchor',True,dict(expected,**{'MANIFEST.json':'0'*64}));case('restored copies')
assert inventory(A)==before
(P/'observed-root.json').write_text(json.dumps(before,indent=2)+'\n')
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'selected_files':len(m['files']),'selected_subdirectories':len(m['directories']),'entire_author_files':len(before['files']),'entire_author_subdirectories':len(before['directories']),'verifier':verified,'verifier_sha256':sha((S/'verify_packet.py').read_bytes()),'canonical_blobs_authenticated':len(records),'source_read_extents_bound':len(reads),'shared_read_extents_bound_to_direct_reads':mapped,'parallel_text_maps_checked':len(maps),'primary_read_extents_bound':len(pr),'primary_artifacts_authenticated':[x['key'] for x in primary],'formal_artifacts_authenticated':2,'original_history_extents_bound':len(hr),'copied_controls':controls,'author_originals_unchanged':True,'semantic_scope':'Parent read all five authored packet prose files and outside REPORT, METHODS and verifier. Authentication and recorded-range checks do not inherit child source/primary/history semantic coverage. No mathematical grade.'}
(P/'replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
