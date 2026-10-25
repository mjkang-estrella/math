#!/usr/bin/env python3
"""Independent read-only S241 artifact replay; no mathematical certification."""
from pathlib import Path
import datetime,hashlib,json,os,re,stat,subprocess,sys,tempfile
P=Path(__file__).resolve().parent;A=P.parent/'fresh-structural-discovery-r241';C=P.parents[1];PROJECT=C.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(p.read_bytes())
anchors={'packet/FINAL.md':'dd00f8bcbcabe577153e498b5fad4b4be9140fb2144007f2d6a3992c4f4b0dac','MANIFEST.json':'b986b909fa7a054ce0eb6e9928f4ccad424fb71b2ced495b3eaf135cf0ce63f3','REPORT.md':'2854326fdec9a02fa9887e5ac65ae12a9b8c2f8ec17feb5a2d1ded628afde3ab'}
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
 args=[sys.executable,'-I','-B',str(A/'packet/verify_packet.py'),'--packet',str(root/'packet'),'--manifest',str(root/'MANIFEST.json'),'--report',str(root/'REPORT.md')]
 for flag,name in [('final','packet/FINAL.md'),('manifest','MANIFEST.json'),('report','REPORT.md')]:args+=['--'+flag+'-sha256',expected[name]]
 r=subprocess.run(args,capture_output=True,text=True);return r.returncode,json.loads(r.stdout)
code,verified=invoke(A,anchors);assert code==0 and verified['files']==37
assert sha((A/'packet/verify_packet.py').read_bytes())=='9c4abd3fa3387ea1b30f2321d3cc6b4d0a500af557c5754d3bc1e577bdc0b28b'
assert {x['path']:x['sha256'] for x in read(A/'ANCHORS.json').values()}==anchors
for n,h in anchors.items():assert sha((A/n).read_bytes())==h
for p in (A/'packet').rglob('*'):
 if p.is_file() and p.name not in ('verify_packet.py','copied-control-results.json'):
  rel=p.relative_to(A/'packet');original=A/rel
  if str(rel)=='private/primary-access.json':original=A/'private/primary/access.json'
  assert p.read_bytes()==original.read_bytes()
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(tb)['tree'];assert len(tree)==13223;by={x['path']:x for x in tree};records=read(A/'private/source-authentication.json');assert len(records)==11
prefix=records[0]['path'].rsplit('/',1)[0];selected=[x for x in tree if x['path']==prefix or x['path'].startswith(prefix+'/')]
assert selected==read(A/'private/tree-selection.json') and len(selected)==15
for x in records:
 b=(A/x['local']).read_bytes();e=by[x['path']]
 assert len(b)==x['size']==e['size'] and sha(b)==x['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob']==e['sha']
 assert '/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' in x['url']
extents=read(A/'private/read-extents.json');coverage={}
for x in extents:
 b=(A/x['file']).read_bytes();ls=b.splitlines(keepends=True);lo,hi=x['lines'];assert [sum(map(len,ls[:lo-1])),sum(map(len,ls[:hi]))]==x['bytes']
 if x['file'].startswith('private/source366/'):coverage.setdefault(x['file'],set()).update(range(lo,hi+1))
assert len(coverage)==10
for name,cov in coverage.items():assert cov==set(range(1,len((A/name).read_bytes().splitlines(keepends=True))+1))
access=read(A/'private/primary/access.json');success=[x for x in access if 'error'not in x];assert len(success)==5
for x in success:
 b=(A/'private/primary'/(x['name']+'.pdf')).read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256']
g=read(A/'private/guards.json');brief=(PROJECT/read(P/'brief-record.json')['brief']).read_text()
assert set(g['wildcards'])==set(re.findall(r'\*[A-Za-z0-9][A-Za-z0-9*_-]*\*',brief))and len(g['wildcards'])==405 and len(g['substrings'])==162
h1=read(A/'private/history-navigation.json');h2=read(A/'private/history-navigation-specific.json')
assert len(h1['results'])==2 and all(not h['body_admitted'] for r in h1['results'] for h in r['hits']) and not h2['results']
assert read(A/'private/lean-access.json')['status']==404
assert sha((A/'private/catalogue366.txt').read_bytes())=='280d3e876d3c17e151c7872b0a74f13ee255e0b763e771e3ddb988c84aa4950c'
assert sha((A/'private/acceptance-bytes.txt').read_bytes())=='f147924a01d36cce7ad5ee13bad6ed9ed9109f3bf4b5c2386fc318aae1330984'
controls=[]
with tempfile.TemporaryDirectory(dir=P,prefix='tiny-controls-')as td:
 root=Path(td);packet=root/'packet';packet.mkdir(mode=0o700);payload=b'independent tiny control\n';f=packet/'FINAL.md';f.write_bytes(payload);f.chmod(0o444)
 manifest={'version':1,'packet_files':[{'path':'FINAL.md','bytes':len(payload),'sha256':sha(payload),'mode':'0444'}],'packet_directories':[{'path':'.','mode':'0700'}]}
 mp=root/'MANIFEST.json';mp.write_text(json.dumps(manifest));mp.chmod(0o444)
 rp=root/'REPORT.md';rp.write_text('FINAL SHA256: '+sha(payload)+'\nMANIFEST SHA256: '+sha(mp.read_bytes())+'\n');rp.chmod(0o444)
 expected={n:sha((root/n).read_bytes())for n in anchors}
 def case(label,reject=False):
  rc,out=invoke(root,expected);assert (rc!=0)==reject;controls.append({'case':label,'observed':'rejected'if reject else'accepted'})
 case('intact synthetic fixture')
 f.chmod(0o644);f.write_bytes(bytes([payload[0]^1])+payload[1:]);f.chmod(0o444);case('same-size byte mutation',True)
 f.chmod(0o644);f.write_bytes(payload);case('file mode mutation',True);f.chmod(0o444)
 packet.chmod(0o755);case('directory mode mutation',True);packet.chmod(0o700)
 extra=packet/'extra';extra.write_text('extra');case('extra file',True);extra.unlink();f.unlink();case('missing file',True)
 f.write_bytes(payload);f.chmod(0o444);case('restored fixture')
 rc,_=invoke(root,dict(expected,**{'REPORT.md':'0'*64}));assert rc!=0;controls.append({'case':'wrong detached anchor','observed':'rejected'})
 mp.chmod(0o644);case('manifest mode mutation',True);mp.chmod(0o444)
assert inventory(A)==before
(P/'observed-root.json').write_text(json.dumps(before,indent=2)+'\n')
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'selected_files':verified['files'],'selected_directories':verified['directories'],'entire_author_files':len(before['files']),'entire_author_subdirectories':len(before['directories']),'verifier':verified,'original_selected_copies_match':True,'canonical_blobs_authenticated':11,'canonical_exact_tree_entries':15,'read_intervals_bound':len(extents),'complete_source_text_files_covered':10,'primary_pdf_identities_bound':5,'guarded_history_passes':2,'admitted_history_mathematical_bodies':0,'history_limit':'Two candidate paths rejected after heading classification; narrower pass no hits. No exhaustive clearance.','independent_tiny_controls':controls,'author_originals_unchanged':True,'formal_support':'none; requested pinned navigation endpoint returned 404','semantic_scope':'Parent read complete DERIVATIONS, READ_LIMITS, FINAL and outside REPORT. No source/primary/history semantic or visual coverage inherited. The exact late reads, recovered displays, failed primary access and actual exposures remain disclosed. Initial batched parent metadata display was clipped; schemas recovered in focused reads, and all metadata entries verified programmatically. Retained calculations are unreviewed; no nominee or mathematical grades/count.','runtime':'gpt-6-astra/xhigh/ultrafast confirmed by terminal receipt'}
(P/'replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
