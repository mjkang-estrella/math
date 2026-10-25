#!/usr/bin/env python3
"""Independent read-only artifact replay; no mathematical grade for S239."""
from pathlib import Path
import datetime,fnmatch,hashlib,json,os,re,stat,subprocess,sys,tempfile,shutil
P=Path(__file__).resolve().parent;A=P.parent/'fresh-structural-discovery-r239';C=P.parents[1];PROJECT=C.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest()
read=lambda p:json.loads(p.read_bytes())
anchors={'packet/FINAL.md':'736368e1c0eb1fa5f811b627f10e4452202c948a77b51e90bab34eeac54992a3','MANIFEST.json':'6fe4f5d7d0b019e1ac105c07420fbd64bca337545141db24d81de4eb1940bb30','REPORT.md':'81207797cd8aea3150166037fb568958eec70a9e20b8073e57c1a44ce3c7110f'}
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
def invoke(root,expected=anchors):
 args=[sys.executable,'-I','-B',str(A/'packet/verify_packet.py'),'--root',str(root)]
 for flag,name in [('final','packet/FINAL.md'),('manifest','MANIFEST.json'),('report','REPORT.md')]:args+=['--'+flag+'-sha256',expected[name]]
 r=subprocess.run(args,capture_output=True,text=True);return r.returncode,r.stdout.strip() or r.stderr.strip()
code,verified=invoke(A);assert code==0;verified=json.loads(verified);assert verified['selected_files']==5
for name,digest in anchors.items():
 assert sha((A/name).read_bytes())==digest
 assert (A/(Path(name).stem+'.sha256')).read_text().split()[0]==digest
treebytes=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(treebytes)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(treebytes)['tree'];assert len(tree)==13223;by={x['path']:x for x in tree}
records=read(A/'private/canonical-authentication.json');assert len(records)==25
prefixes={x['path'].split('/')[1]for x in records};selection=[x for x in tree if len(x['path'].split('/'))>1 and x['path'].split('/')[1]in prefixes]
assert read(A/'private/selected-tree.json')==selection and len(selection)==33
for x in records:
 b=(A/'private/canonical'/x['path']).read_bytes();e=by[x['path']]
 assert len(b)==x['bytes']==e['size'] and sha(b)==x['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob']==e['sha']
 assert '/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' in x['url']
bounds={x['alias']:x for x in read(A/'private/primary-boundaries.json')}
reads=[json.loads(x)for x in(A/'private/read-events.jsonl').read_bytes().splitlines()];coverage={}
for x in reads:
 b=(A/'private/canonical'/bounds[x['alias']]['path']).read_bytes();ls=b.splitlines(keepends=True);lo=x['line_start'];hi=x['line_end_inclusive'];a=x['byte_start'];z=x['byte_end_exclusive']
 assert [sum(map(len,ls[:lo-1])),sum(map(len,ls[:hi]))]==[a,z]
 selected=b[a:z]
 for u,v,label in x['masked']:assert a<=u<v<=z;selected=selected.replace(b[u:v],b'[MASKED editorial/driver metadata]\n',1)
 assert sha(selected)==x['display_sha256'];coverage.setdefault(x['alias'],set()).update(range(lo,hi+1))
for alias,cov in coverage.items():assert cov==set(range(1,len((A/'private/canonical'/bounds[alias]['path']).read_bytes().splitlines(keepends=True))+1))
assert len(coverage)==23
primary=[json.loads(x)for x in(A/'private/antecedent-reads.jsonl').read_bytes().splitlines()]
for x in primary:
 path=x.get('path') or 'private/antecedents/'+({'dhm-v3':'dhm'}.get(x['alias'],x['alias']))+'.txt'
 b=(A/path).read_bytes();ls=b.splitlines(keepends=True);lo,hi=x['lines'];a,z=x['bytes']
 assert [sum(map(len,ls[:lo-1])),sum(map(len,ls[:hi]))]==[a,z]
for x in read(A/'private/antecedents/access.json'):
 b=(A/'private/antecedents'/(x['name']+'.pdf')).read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256']
 assert (A/'private/antecedents'/(x['name']+'.txt')).stat().st_size==x['text_bytes']
g=read(A/'private/guards.json');brief=(PROJECT/read(P/'brief-record.json')['brief']).read_text()
assert set(g['wildcards'])==set(re.findall(r'\*[A-Za-z0-9][A-Za-z0-9*_-]*\*',brief)) and len(g['wildcards'])==401 and len(g['substrings'])==162
def rejected(name):
 p=name.casefold()
 return p==g['own_root'] or p.startswith(g['own_root']+'/') or any(s in p for s in g['substrings'])or any(fnmatch.fnmatchcase(p,w)for w in g['wildcards']+g['additional_derivative_patterns'])
history=[json.loads(x)for x in(A/'private/original-read-events.jsonl').read_bytes().splitlines()]
for x in history:
 assert not rejected(x['path']);p=PROJECT/x['path']
 for q in p.relative_to(PROJECT).parents:
  if str(q)!='.':assert not rejected(q.as_posix())
 with p.open('rb')as f:f.seek(x['start']);b=f.read(x['end']-x['start'])
 assert sha(b)==x['sha256']
assert sha((A/'private/acceptance.bin').read_bytes())=='f147924a01d36cce7ad5ee13bad6ed9ed9109f3bf4b5c2386fc318aae1330984'
assert sha((A/'private/source364-entry.bin').read_bytes())=='6a44e04a27cc05ece169970382faa88e5cec3c45f12093ecaa15f09ad0a7d115'
assert read(A/'private/lean-access.json')['status']==404
# A tiny, independent five-file fixture exercises the actual read-only verifier.
controls=[]
with tempfile.TemporaryDirectory(dir=P,prefix='copied-controls-')as td:
 root=Path(td);(root/'packet').mkdir();rows=[]
 for name in ['FINAL.md','a.txt','b.txt','c.txt','d.txt']:
  f=root/'packet'/name;b=('tiny '+name+'\n').encode();f.write_bytes(b);f.chmod(0o444);rows.append({'path':'packet/'+name,'bytes':len(b),'sha256':sha(b),'mode':'0444'})
 (root/'MANIFEST.json').write_text(json.dumps({'schema':'source364-r239-packet-v1','files':rows}));(root/'REPORT.md').write_text('tiny outside report\n')
 expected={n:sha((root/n).read_bytes())for n in anchors}
 def case(label,reject=False):
  rc,_=invoke(root,expected);assert (rc!=0)==reject;controls.append({'case':label,'observed':'rejected'if reject else'accepted'})
 case('intact tiny fixture')
 f=root/'packet/a.txt';b=f.read_bytes();f.chmod(0o644);f.write_bytes(bytes([b[0]^1])+b[1:]);f.chmod(0o444);case('same-size byte change',True)
 f.chmod(0o644);f.write_bytes(b);case('mode change',True);f.chmod(0o444)
 extra=root/'packet/extra.txt';extra.write_text('extra');case('unselected extra',True);extra.unlink()
 f.unlink();case('missing selected file',True);f.write_bytes(b);f.chmod(0o444);case('restored fixture')
 rc,_=invoke(root,dict(expected,**{'REPORT.md':'0'*64}));assert rc!=0;controls.append({'case':'wrong report anchor','observed':'rejected'})
assert inventory(A)==before
(P/'observed-root.json').write_text(json.dumps(before,indent=2)+'\n')
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'selected_files':5,'entire_author_files':len(before['files']),'entire_author_subdirectories':len(before['directories']),'verifier':verified,'verifier_sha256':sha((A/'packet/verify_packet.py').read_bytes()),'canonical_blobs_authenticated':25,'canonical_exact_tree_entries':33,'source_display_intervals_bound':len(reads),'complete_text_files_covered':23,'primary_read_intervals_coordinates_bound':len(primary),'primary_pdf_hashes_from_access_records_bound':3,'primary_limit':'All five PDF/text pairs inventoried; three PDF identities have access-record hashes. Primary range records have coordinates, not display digests. No inherited semantic or visual coverage.','guarded_history_intervals_bound':len(history),'distinct_original_history_files':len({x['path']for x in history}),'history_limit':'Only exact guarded byte ranges hashed; parent has not semantically read original history. Child reports strongest finite-test process overlap, coarse search omissions and false derivative navigation admissions.','author_control_cases':len(read(A/'private/artifact-controls.json')['cases']),'independent_tiny_controls':controls,'author_originals_unchanged':True,'selection_scope':'Exact packet selection only; anchors bind manifest and outside report bytes. Whole root bytes/modes independently observed unchanged; existing author pycache retained.','semantic_scope':'Complete two authored derivation files, FINAL, outside REPORT and READING-LIMITS read. Initial combined tool output truncated part of section9, recovered by focused lines175-260 display. No mathematical certification, nominee, grade, count, exhaustive history clearance or formal support.','formal_support':'none; pinned navigation returned404'}
(P/'replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
