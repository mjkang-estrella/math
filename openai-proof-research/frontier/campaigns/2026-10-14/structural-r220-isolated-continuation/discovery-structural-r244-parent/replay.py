#!/usr/bin/env python3
"""Read-only S244 artifact replay. No mathematical verdict is assigned."""
from pathlib import Path
import datetime,fnmatch,hashlib,json,os,re,stat,subprocess,sys,tempfile
P=Path(__file__).resolve().parent;A=P.parent/'fresh-structural-discovery-r244';Q=A/'packet';C=P.parents[1];PROJECT=C.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(p.read_bytes())
anchors={'packet/FINAL.md':'d3564a62268d1c2ad6d0c792b2b2c4dbff1d1d8156f8611adcfe5572f7456906','MANIFEST.json':'53bfe5b7313a96a07dc32d11265136a5b9e772ddac2d47857d9e4ece1f848fba','REPORT.md':'f86fff38cee237a291dc4a70d514cd6f3d01aa820d302ca5261548ff69055209'}
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
assert sha((Q/'original/verify_packet.py').read_bytes())=='f63e83fdd72c04816ef57e51b455fa0d3a414d5fe293d7dbf8ac68a607dba139'
def invoke(root,expected):
 args=[sys.executable,'-I','-B',str(Q/'original/verify_packet.py'),'--packet',str(root/'packet'),'--manifest',str(root/'MANIFEST.json'),'--report',str(root/'REPORT.md')]
 for flag,name in [('final','packet/FINAL.md'),('manifest','MANIFEST.json'),('report','REPORT.md')]:args+=['--'+flag+'-sha256',expected[name]]
 r=subprocess.run(args,capture_output=True,text=True);return r.returncode,json.loads(r.stdout)
code,verified=invoke(A,anchors);assert code==0 and verified['ok']
m=read(A/'MANIFEST.json');assert len(m['files'])==47 and len(m['directories'])==9
assert {v['path']:v['sha256'] for k,v in read(A/'ANCHORS.json').items() if isinstance(v,dict)}==anchors
for n,h in anchors.items():assert sha((A/n).read_bytes())==h
root_copies={'NAVIGATION-NOTE.md','START.md','controls-results.json','guards.json','navigate-fold.py','navigate.py'}
for p in Q.rglob('*'):
 if p.is_file():
  rel=p.relative_to(Q)
  original=A/rel
  if rel.parts[0]=='original':original=A/rel.name
  elif rel.parts[0]=='private' and rel.name in root_copies and len(rel.parts)==2:original=A/rel.name
  assert p.read_bytes()==original.read_bytes(),str(rel)
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(tb)['tree'];assert len(tree)==13223;by={x['path']:x for x in tree};records=read(A/'private/source-auth.json');assert len(records)==11
prefixes={'/'.join(x['path'].split('/')[:2]) for x in records};selected=[x for x in tree if '/'.join(x['path'].split('/')[:2])in prefixes]
assert selected==read(A/'private/tree-selection.json') and len(selected)==16
for x in records:
 b=(A/x['local']).read_bytes();e=by[x['path']]
 assert len(b)==x['size']==e['size'] and sha(b)==x['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob_sha1']==e['sha']
 assert '/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' in x['url']
g=read(A/'guards.json');brief=(PROJECT/read(P/'brief-record.json')['brief']).read_text();wild=g['full_path_casefold_wildcards'];subs=g['full_path_casefold_substrings']
assert set(wild)==set(re.findall(r'\*[A-Za-z0-9][A-Za-z0-9*_-]*\*',brief)) and len(wild)==411 and len(subs)==162
def permitted(rel):
 rel=rel.casefold();return not any(fnmatch.fnmatchcase(rel,x.casefold()) for x in wild+g['additional_component_patterns']) and not any(x.casefold()in rel for x in subs)
rows=[json.loads(x) for x in(A/'private/reads.jsonl').read_bytes().splitlines()];coverage={};history=0;primary=0;intervals=0
for x in rows:
 name=x['path'];ranges=x.get('ranges',[x.get('bytes')]);assert all(z is not None for z in ranges)
 if name.startswith('frontier/'):
  assert permitted(name);lo,hi=x['bytes']
  with(PROJECT/name).open('rb')as f:f.seek(lo);b=f.read(hi-lo)
  assert len(b)==hi-lo and b==(A/x['local_selection']).read_bytes();history+=1;intervals+=1;continue
 b=(A/name).read_bytes()
 for lo,hi in ranges:assert 0<=lo<hi<=len(b);intervals+=1
 if '/sections/'in name:coverage.setdefault(name,[]).extend(ranges)
 if '/primary/'in name:primary+=len(ranges)
for name,ranges in coverage.items():
 end=0
 for lo,hi in sorted(ranges):assert lo<=end;end=max(end,hi)
 assert end==len((A/name).read_bytes())
assert len(coverage)==6 and history==6 and len(rows)==23
pdf=(A/'private/primary/banuelos-pang.pdf').read_bytes();assert len(pdf)==271908 and sha(pdf)=='1aa36a2e961ef4183f813b5840c2bac4d3defa4c77cd218a86922d7db53baeee'
lean=read(A/'private/lean-comparator-access.json');b=(A/'private/HotSpots.lean').read_bytes();assert len(b)==lean['bytes'] and sha(b)==lean['sha256']
assert sha((A/'private/catalogue369.bin').read_bytes())=='4bf334ba3b4e11fc0c41aacdf6849b450173d8c8fe48aa6de630cea6920c7ee8'
with tempfile.TemporaryDirectory(dir=P,prefix='algebra-replay-')as td:
 root=Path(td);target=root/A.relative_to(PROJECT);target.mkdir(parents=True)
 r=subprocess.run([sys.executable,'-I','-B',str(A/'local_algebra.py')],cwd=root,capture_output=True,text=True);assert r.returncode==0,r.stderr
 assert (target/'local-algebra.txt').read_bytes()==(A/'local-algebra.txt').read_bytes()
controls=[]
with tempfile.TemporaryDirectory(dir=P,prefix='tiny-controls-')as td:
 root=Path(td);packet=root/'packet';packet.mkdir(mode=0o700);payload=b'independent tiny control\n';f=packet/'FINAL.md';f.write_bytes(payload);f.chmod(0o444)
 manifest={'version':1,'files':[{'path':'FINAL.md','bytes':len(payload),'sha256':sha(payload),'mode':'0444'}],'directories':{'.':'0700'}}
 mp=root/'MANIFEST.json';mp.write_text(json.dumps(manifest));rp=root/'REPORT.md';rp.write_text('independent outside report\n');expected={n:sha((root/n).read_bytes())for n in anchors}
 def case(label,reject=False):
  rc,out=invoke(root,expected);assert(rc!=0)==reject;controls.append({'case':label,'observed':'rejected'if reject else'accepted'})
 case('intact synthetic fixture');f.chmod(0o644);f.write_bytes(bytes([payload[0]^1])+payload[1:]);f.chmod(0o444);case('same-size byte mutation',True)
 f.chmod(0o644);f.write_bytes(payload);case('file mode mutation',True);f.chmod(0o444)
 packet.chmod(0o755);case('directory mode mutation',True);packet.chmod(0o700)
 extra=packet/'extra';extra.write_text('extra');case('extra file',True);extra.unlink();f.unlink();case('missing file',True)
 f.write_bytes(payload);f.chmod(0o444);case('restored fixture')
 rc,_=invoke(root,dict(expected,**{'REPORT.md':'0'*64}));assert rc!=0;controls.append({'case':'wrong detached anchor','observed':'rejected'})
assert inventory(A)==before
(P/'observed-root.json').write_text(json.dumps(before,indent=2)+'\n')
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'selected_files':len(m['files']),'selected_directories':len(m['directories']),'selected_bytes':sum(x['bytes']for x in m['files']),'entire_author_files':len(before['files']),'entire_author_subdirectories':len(before['directories']),'verifier':verified,'original_selected_copies_match':True,'canonical_blobs_authenticated':11,'canonical_exact_tree_entries':16,'read_ledger_rows':len(rows),'text_read_intervals_bound':intervals,'complete_source_section_files_covered':6,'primary_text_intervals_bound':primary,'primary_pdf_identities_bound':1,'history_original_intervals_bound':6,'history_limit':'Only six exact i214 mathematical intervals compared; no whole-file history hash or exhaustive clearance claimed. Raw metadata navigation false admission and actual editorial overreads remain disclosed.','independent_tiny_controls':controls,'local_algebra_replayed_in_disposable_scratch':True,'author_originals_unchanged':True,'formal_support':'none; comparator endpoint contains sorry','semantic_scope':'Complete authored boundary derivation, initial derivation, source-operation comparisons, limits, final and report read. No source/primary/history semantic or visual coverage inherited. No nominee; no mathematical grades/count.','runtime':'S244 completed on ultrafast. Parent and future owned tasks now default standard speed, per latest user instruction.'}
(P/'replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
