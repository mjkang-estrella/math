#!/usr/bin/env python3
"""Independent read-only S242 artifact replay; no mathematical certification."""
from pathlib import Path
import datetime,fnmatch,hashlib,json,os,re,stat,subprocess,sys,tempfile
P=Path(__file__).resolve().parent;A=P.parent/'fresh-structural-discovery-r242';Q=A/'packet';C=P.parents[1];PROJECT=C.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(p.read_bytes())
anchors={'packet/FINAL.md':'c35d4dd2c58a5a840ec12d3ef4d5865556c5b029aa62d5172dcdc96d5025f277','MANIFEST.json':'ae069c56db71d8fc5617fbb35255c9b7412058176138b63881ac79fc51f720ae','REPORT.md':'367394374ee12868bd439329ae4ed3372e9981e614397eca29f8e1cc1ab17717'}
def inventory(root):
 out={'root_mode':stat.S_IMODE(root.stat().st_mode),'files':{},'directories':{}}
 for base,ds,fs in os.walk(root,followlinks=False):
  for name in ds+fs:
   p=Path(base)/name;s=p.lstat();rel=p.relative_to(root).as_posix();assert not stat.S_ISLNK(s.st_mode)
   if stat.S_ISDIR(s.st_mode):out['directories'][rel]=stat.S_IMODE(s.st_mode)
   else:
    assert stat.S_ISREG(s.st_mode);b=p.read_bytes();out['files'][rel]={'bytes':len(b),'sha256':sha(b),'mode':stat.S_IMODE(s.st_mode)}
 return out
before=inventory(A)
def invoke(root,expected):
 args=[sys.executable,'-I','-B',str(A/'verify_packet.py'),'--root',str(root)]
 for flag,name in [('final','packet/FINAL.md'),('manifest','MANIFEST.json'),('report','REPORT.md')]:args+=['--'+flag+'-sha256',expected[name]]
 r=subprocess.run(args,capture_output=True,text=True);return r.returncode,json.loads(r.stdout)
code,verified=invoke(A,anchors);assert code==0 and verified['files']==82
assert sha((A/'verify_packet.py').read_bytes())=='5dc21b44b5c0e238533ba2fd26e72468e884a41e5dec421a49d3248e15284255'
for n,h in anchors.items():assert sha((A/n).read_bytes())==h and h in (A/'ANCHORS.txt').read_text()
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(tb)['tree'];assert len(tree)==13223;by={x['path']:x for x in tree};records=read(Q/'private/canonical-auth.json');assert len(records)==42
prefix=records[0]['path'].rsplit('/',1)[0];selected=[x for x in tree if x['path']==prefix or x['path'].startswith(prefix+'/')]
assert selected==read(Q/'private/tree-selection.json') and len(selected)==53
for x in records:
 b=(Q/x['local']).read_bytes();e=by[x['path']]
 assert len(b)==x['bytes']==e['size'] and sha(b)==x['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob']==e['sha']
 assert '/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' in x['url']
g=read(Q/'private/guards.json');brief=(PROJECT/read(P/'brief-record.json')['brief']).read_text()
assert set(g['wildcards'])==set(re.findall(r'\*[A-Za-z0-9][A-Za-z0-9*_-]*\*',brief))and len(g['wildcards'])==407 and len(g['substrings'])==162
def permitted(rel):
 rel=rel.casefold();return not any(fnmatch.fnmatchcase(rel,x.casefold())for x in g['wildcards']+g['derivative_wildcards'])and not any(x.casefold()in rel for x in g['substrings'])
rows=[json.loads(x)for x in(Q/'private/reads.jsonl').read_bytes().splitlines()];coverage={};history=0;primary=0
for x in rows:
 if 'page'in x:continue
 name=x['file'];local=Q/'private'/name
 if name.startswith('frontier/'):
  assert permitted(name);local=Q/'private/history-r99-section-source.txt';assert local.read_bytes()==(PROJECT/name).read_bytes();history+=1
 elif 'original_path'in x:
  assert permitted(x['original_path']);assert local.read_bytes()==(PROJECT/x['original_path']).read_bytes();history+=1
 b=local.read_bytes();lo,hi=x['start'],x['end'];assert 0<=lo<hi<=len(b)
 if 'lines'in x:
  ls=b.split(b'\n');a,z=x['lines'];assert lo==sum(len(v)+1 for v in ls[:a-1]) and hi==min(len(b),sum(len(v)+1 for v in ls[:z]));primary+=1
 if name.startswith('canonical/'):coverage.setdefault(name,[]).append((lo,hi))
for name,ranges in coverage.items():
 end=0
 for a,z in sorted(ranges):assert a<=end;end=max(end,z)
 assert end==len((Q/'private'/name).read_bytes())
assert len(coverage)==13 and history==3
for tag in ['js','frs','ee']:
 b=(Q/'private'/(tag+'.txt')).read_bytes();ls=b.split(b'\n')
 for x in read(Q/'private'/(tag+'-masks.json')):
  start=sum(len(v)+1 for v in ls[:x['line']-1]);assert x['start']==start and x['end']==start+len(ls[x['line']-1])
access=read(Q/'private/primary-access.json');assert len(access)==3
for x in access:
 b=(Q/'private'/(x['id']+'.pdf')).read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256']
assert len(read(Q/'private/history-navigation.json')['hits'])==10 and len(read(Q/'private/history-narrow-navigation.json')['hits'])==6
lean=read(Q/'private/lean-comparator-access.json');lb=(Q/'private/BernoulliNonflatInSeven.lean').read_bytes();assert sha(lb)==lean['sha256'] and len(lb)==lean['bytes'] and b'sorry'in lb
assert sha((Q/'private/entry367.txt').read_bytes())=='2d54508aa0f52bf46cd177ef163d4f2825d5fe48f957ea10f0f4146238c81409'
assert sha((Q/'private/acceptance.txt').read_bytes())=='f147924a01d36cce7ad5ee13bad6ed9ed9109f3bf4b5c2386fc318aae1330984'
r=subprocess.run([sys.executable,'-I','-B',str(Q/'algebra.py')],capture_output=True,text=True);assert r.returncode==0 and json.loads(r.stdout)==read(Q/'private/own-algebra-output.json')
assert sha((A/'controls/outcomes.json').read_bytes())=='59f710de2c0dd350b9af3720fce778c1b6aa4073dd5a0ca17a5dad97007b1174'
controls=[]
with tempfile.TemporaryDirectory(dir=P,prefix='tiny-controls-')as td:
 root=Path(td);packet=root/'packet';packet.mkdir(mode=0o700);payload=b'independent tiny control\n';f=packet/'FINAL.md';f.write_bytes(payload);f.chmod(0o444)
 manifest={'schema':'r242-exact-packet-v1','packet':'packet','final':'FINAL.md','files':[{'path':'FINAL.md','size':len(payload),'sha256':sha(payload),'mode':'0444'}],'directories':{'.':'0700'}}
 mp=root/'MANIFEST.json';mp.write_text(json.dumps(manifest));mp.chmod(0o444)
 rp=root/'REPORT.md';rp.write_text('independent outside report\n');rp.chmod(0o444);expected={n:sha((root/n).read_bytes())for n in anchors}
 def case(label,reject=False):
  rc,out=invoke(root,expected);assert (rc!=0)==reject;controls.append({'case':label,'observed':'rejected'if reject else'accepted'})
 case('intact synthetic fixture');f.chmod(0o644);f.write_bytes(bytes([payload[0]^1])+payload[1:]);f.chmod(0o444);case('same-size byte mutation',True)
 f.chmod(0o644);f.write_bytes(payload);case('file mode mutation',True);f.chmod(0o444)
 packet.chmod(0o755);case('directory mode mutation',True);packet.chmod(0o700)
 extra=packet/'extra';extra.write_text('extra');case('extra file',True);extra.unlink();f.unlink();case('missing file',True)
 f.write_bytes(payload);f.chmod(0o444);case('restored fixture')
 rc,_=invoke(root,dict(expected,**{'REPORT.md':'0'*64}));assert rc!=0;controls.append({'case':'wrong detached anchor','observed':'rejected'})
 mp.chmod(0o644);case('manifest mode mutation',True);mp.chmod(0o444)
assert inventory(A)==before
(P/'observed-root.json').write_text(json.dumps(before,indent=2)+'\n')
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'selected_files':verified['files'],'selected_directories':verified['directories'],'entire_author_files':len(before['files']),'entire_author_subdirectories':len(before['directories']),'verifier':verified,'canonical_blobs_authenticated':42,'canonical_exact_tree_entries':53,'text_read_intervals_bound':len(rows)-1,'complete_source_text_files_covered':len(coverage),'primary_text_intervals_bound':primary,'primary_pdf_identities_bound':3,'guarded_history_passes':2,'history_original_copies_bound':history,'history_limit':'Only three admitted r99 mathematical sections; later comparisons and visible provenance remain disclosed. No exhaustive clearance.','author_control_cases':4,'independent_tiny_controls':controls,'small_authored_algebra_reproduced':True,'author_originals_unchanged':True,'formal_support':'none; exact pinned comparator contains sorry','semantic_scope':'Parent read complete derivation, sources-and-limits, FINAL and outside REPORT. No source/primary/history semantic or visual coverage inherited. All documented masking corrections, recoveries, late comparisons and limited primary scope remain. Retained calculations are unreviewed; no nominee or mathematical grades/count.','runtime':'gpt-6-astra/xhigh/ultrafast confirmed by terminal receipt'}
(P/'replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
