#!/usr/bin/env python3
"""Read-only artifact replay for S237; no mathematical grade."""
from pathlib import Path
import datetime,hashlib,json,os,re,runpy,stat,subprocess,sys,tempfile
P=Path(__file__).resolve().parent;A=P.parent/'fresh-structural-discovery-r237';C=P.parents[1];PROJECT=C.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(p.read_bytes())
anchors={'FINAL.md':'978e401cc727eb150b5f50965f9c77e30af553db6b3540089f34701fff901337','MANIFEST.json':'2a514afed9d31ae88b30afa7df77ac903e26fdd10eff4b496cbebdc1e4d019d0','REPORT.md':'5900f3e6531c3b9a3a084486469e3a4f6e5250ded155fe5bef80f436e7d03b2d'}
def inventory(root):
 assert not root.is_symlink();out={'root_mode':stat.S_IMODE(root.stat().st_mode),'files':{},'directories':{}}
 for base,ds,fs in os.walk(root,followlinks=False):
  for name in ds+fs:
   p=Path(base)/name;s=p.lstat();rel=p.relative_to(root).as_posix();assert not stat.S_ISLNK(s.st_mode)
   if stat.S_ISDIR(s.st_mode):out['directories'][rel]=stat.S_IMODE(s.st_mode)
   else:
    assert stat.S_ISREG(s.st_mode);b=p.read_bytes();out['files'][rel]={'bytes':len(b),'sha256':sha(b),'mode':stat.S_IMODE(s.st_mode)}
 return out
before=inventory(A);assert len(before['files'])==77 and len(before['directories'])==10
def invoke(expected):
 args=[sys.executable,'-I','-B',str(A/'verify_packet.py'),'--root',str(A)]
 for arg,name in [('final','FINAL.md'),('manifest','MANIFEST.json'),('report','REPORT.md')]:args+=['--'+arg+'-sha256',expected[name]]
 r=subprocess.run(args,capture_output=True,text=True);return r.returncode,json.loads(r.stdout) if not r.returncode else r.stderr.strip().splitlines()[-1]
code,verified=invoke(anchors);assert code==0 and verified['files']==69
for name,digest in anchors.items():assert (A/(name.split('.')[0]+'.sha256')).read_text().split()[0]==digest
m=read(A/'MANIFEST.json');assert len(m['files'])==69 and len(m['outside_selection'])==8
treebytes=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(treebytes)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=json.loads(treebytes)['tree'];assert len(tree)==13223;by={x['path']:x for x in tree}
prefix='preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026';records=read(A/'private/canonical-authentication.json');assert len(records)==17
assert read(A/'private/canonical-exact-tree-selection.json')==[x for x in tree if x['path']==prefix or x['path'].startswith(prefix+'/')]
for x in records:
 b=(A/x['local']).read_bytes();e=by[x['path']];assert len(b)==x['bytes']==e['size'] and sha(b)==x['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob']==e['sha']
 assert '/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' in x['url']
base=A/'private/canonical'/prefix/'build';reads=[json.loads(x)for x in(A/'private/semantic-reads.jsonl').read_bytes().splitlines()];coverage={}
for x in reads:
 b=(base/x['path']).read_bytes();ls=b.splitlines(keepends=True);lo,hi=x['lines'];a,z=x['bytes']
 assert [sum(map(len,ls[:lo-1])),sum(map(len,ls[:hi]))]==[a,z] and sha(b[a:z])==x['sha256'];coverage.setdefault(x['path'],set()).update(range(lo,hi+1))
missing_blank=0
for name,cov in coverage.items():
 ls=(base/name).read_bytes().splitlines(keepends=True)
 for i in set(range(1,len(ls)+1))-cov:assert not ls[i-1].strip();missing_blank+=1
assert len(coverage)==14 and missing_blank==1
primary=[json.loads(x)for x in(A/'private/primary/reads.jsonl').read_bytes().splitlines()]
for x in primary:
 b=(A/'private/primary'/(x['name']+'.txt')).read_bytes();ls=b.splitlines(keepends=True);lo,hi=x['lines'];a,z=x['bytes']
 assert [sum(map(len,ls[:lo-1])),sum(map(len,ls[:hi]))]==[a,z] and sha(b[a:z])==x['sha256']
versions=read(A/'private/primary/versions-and-hashes.json');assert len(versions)==8
for x in versions:
 for suffix,key in [('.pdf','pdf'),('.txt','text')]:
  b=(A/'private/primary'/(x['name']+suffix)).read_bytes();assert len(b)==x[key+'_bytes'] and sha(b)==x[key+'_sha256']
for x in read(A/'private/formal-authentication.json'):
 b=(A/'private'/Path(x['upstream_path']).name).read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob']
assert b'sorry' in (A/'private/VlasovMaxwell.lean').read_bytes()
g=read(A/'private/guards.json');brief=(PROJECT/read(P/'brief-record.json')['brief']).read_text();literal=set(re.findall(r'\*[A-Za-z0-9][A-Za-z0-9*_-]*\*',brief));assert len(literal)==397 and set(g['wildcards'])==literal and len(g['substrings'])==162
hist=[read(A/'private/history-pass1.json'),read(A/'private/history-pass2.json')];assert [x['pass']for x in hist]==[1,2] and len(hist[0]['hits'])==1 and hist[0]['hits'][0]['admin_rejected'] and not hist[1]['hits']
assert sha((A/'private/acceptance-slice.txt').read_bytes())=='f147924a01d36cce7ad5ee13bad6ed9ed9109f3bf4b5c2386fc318aae1330984'
assert sha((A/'private/catalogue362.txt').read_bytes())=='351cd5386b597b543eb35ec41a279adfa67d50aaba63ef95aa9bcef8326038f7'
api=runpy.run_path(str(A/'verify_packet.py'));controls=[]
with tempfile.TemporaryDirectory(dir=P,prefix='copied-controls-')as td:
 root=Path(td);f=root/'sample.txt';payload=b'independent parent artifact control\n';f.write_bytes(payload);f.chmod(0o444);entries=[{'path':'sample.txt','bytes':len(payload),'sha256':sha(payload),'mode':'0444'}]
 def case(label,es=entries,reject=False):
  try:api['verify_entries'](root,es);failed=False
  except ValueError:failed=True
  assert failed==reject;controls.append({'case':label,'observed':'rejected'if reject else'accepted'})
 case('intact copied selection');f.chmod(0o644);f.write_bytes(bytes([payload[0]^1])+payload[1:]);f.chmod(0o444);case('same-size byte mutation',reject=True)
 f.chmod(0o644);f.write_bytes(payload);case('mode mutation',reject=True);f.chmod(0o444);extra=root/'extra.txt';extra.write_bytes(b'extra');case('unselected extra file',reject=True);extra.unlink();case('omitted selected entry',[],True);case('restored copied selection')
code,_=invoke(dict(anchors,**{'REPORT.md':'0'*64}));assert code!=0
assert inventory(A)==before;(P/'observed-root.json').write_text(json.dumps(before,indent=2)+'\n')
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'selected_files':69,'outside_selection_files':8,'entire_author_files':77,'entire_author_subdirectories':10,'verifier':verified,'verifier_sha256':sha((A/'verify_packet.py').read_bytes()),'canonical_blobs_authenticated':17,'canonical_exact_tree_entries':21,'source_read_intervals_bound':len(reads),'logged_operative_tex_and_bibliography_files':14,'unlogged_blank_line_count':1,'source_read_coverage_note':'The only uncovered line within logged complete source files is a blank retarded-section line. Driver and README are reported direct reads, not semantic-log coverage.','primary_read_intervals_bound':len(primary),'primary_pdf_text_pairs_bound':8,'distinct_guarded_history_passes':2,'admitted_history_mathematical_bodies':0,'formal_endpoint_local_identities_bound':2,'formal_support':'none; comparator declaration ends in sorry','author_control_cases':len(read(A/'private/integrity-controls.json')['tests']),'independent_copied_controls':controls,'wrong_detached_anchor_rejected':True,'author_originals_unchanged':True,'selection_scope':'Exact selected files plus eight named outside files; verifier rejects other files and checks selected/anchor modes, but does not bind directory modes. Parent independently observes the whole root.','semantic_scope':'Parent read complete DERIVATIONS D1-D9, LIMITS, FINAL and outside REPORT. Source/primary/visual identity and range checks do not inherit semantic or visual reading. Retained deductions are not independently mathematically certified. Coupled uniqueness/stability remain unproved. No nominee, mathematical grades, count, history clearance or formal support.'}
(P/'replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
