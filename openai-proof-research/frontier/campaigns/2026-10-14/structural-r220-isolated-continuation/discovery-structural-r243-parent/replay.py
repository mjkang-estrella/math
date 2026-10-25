#!/usr/bin/env python3
"""Read-only S243 artifact replay; retained deductions receive no mathematical grade."""
from pathlib import Path
import datetime,fnmatch,hashlib,json,os,re,stat,subprocess,sys,tempfile
P=Path(__file__).resolve().parent;A=P.parent/'fresh-structural-discovery-r243';Q=A/'packet';C=P.parents[1];PROJECT=C.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(p.read_bytes())
anchors={'packet/FINAL.md':'dd64aa61d0e289ecb449341f674328bf214d06f1b7064e6dcb150866cd539bb1','MANIFEST.json':'2f9a46897245886d85b42ca5919cd6061e107b248411dcb7305837ed2dc5b043','REPORT.md':'f92bef5245877bb573891a4b623a2af72e6f1b1e3d0345b12925c6befbeff68f'}
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
 args=[sys.executable,'-I','-B',str(Q/'VERIFY.py'),'--packet',str(root/'packet'),'--manifest',str(root/'MANIFEST.json'),'--report',str(root/'REPORT.md')]
 for flag,name in [('final','packet/FINAL.md'),('manifest','MANIFEST.json'),('report','REPORT.md')]:args+=['--'+flag+'-sha256',expected[name]]
 r=subprocess.run(args,capture_output=True,text=True);return r.returncode,json.loads(r.stdout)
code,verified=invoke(A,anchors);assert code==0 and verified['files']==74
assert sha((Q/'VERIFY.py').read_bytes())=='105e96074941cadc040395323299d6f167b421d6a26d094836c79a160ede183d'
assert {x['path']:x['sha256']for x in read(A/'ANCHORS.json').values()}==anchors
for n,h in anchors.items():assert sha((A/n).read_bytes())==h
mapping={'DERIVATIONS.md':'derivations.md','SOURCE-OPERATIONS.md':'source-operations.md','VERIFY.py':'verify_packet.py'}
for p in Q.rglob('*'):
 if p.is_file():
  rel=p.relative_to(Q).as_posix();original=A/mapping.get(rel,rel);assert p.read_bytes()==original.read_bytes()
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(tb)['tree'];assert len(tree)==13223;by={x['path']:x for x in tree};records=read(A/'private/authenticated.json');assert len(records)==20
prefixes={'/'.join(x['path'].split('/')[:2])for x in records};selected=[x for x in tree if '/'.join(x['path'].split('/')[:2])in prefixes]
assert selected==read(A/'private/tree-selection.json')and len(selected)==26
for x in records:
 b=(A/x['local']).read_bytes();e=by[x['path']]
 assert len(b)==x['bytes']==e['size'] and sha(b)==x['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob']==e['sha']
 assert '/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'in x['url']
g=read(A/'private/guards.json');brief=(PROJECT/read(P/'brief-record.json')['brief']).read_text()
assert set(g['wildcards'])==set(re.findall(r'\*[A-Za-z0-9][A-Za-z0-9*_-]*\*',brief))and len(g['wildcards'])==409 and len(g['substrings'])==162
def permitted(rel):
 rel=rel.casefold();return not any(fnmatch.fnmatchcase(rel,x.casefold())for x in g['wildcards']+g['additional_derivative_wildcards'])and not any(x.casefold()in rel for x in g['substrings'])
rows=[json.loads(x)for x in(A/'private/reads.jsonl').read_bytes().splitlines()];coverage={};history=0;primary=0
for x in rows:
 name=x['path']
 if name.startswith('frontier/'):
  assert permitted(name);lo,hi=x['byte_start'],x['byte_end']
  with(PROJECT/name).open('rb')as f:f.seek(lo);b=f.read(hi-lo)
  copy=A/'private'/('original-i07-'+str(x['line_start'])+'-'+str(x['line_end'])+'.txt');assert b==copy.read_bytes();history+=1;continue
 b=(A/name).read_bytes();ls=b.splitlines(keepends=True)
 if 'start'in x:lo,hi=x['start'],x['end'];a,z=x['line_start'],x['line_end_exclusive']
 else:lo,hi=x['byte_start'],x['byte_end'];a,z=x['line_start'],x['line_end'];primary+=1
 assert [lo,hi]==[sum(map(len,ls[:a-1])),sum(map(len,ls[:z-1]))]
 assert all(a<=i<z for i in x.get('masked_lines',[]))
 if '/sections/'in name:coverage.setdefault(name,[]).append((lo,hi))
for name,ranges in coverage.items():
 end=0
 for a,z in sorted(ranges):assert a<=end;end=max(end,z)
 assert end==len((A/name).read_bytes())
assert len(coverage)==12 and history==2 and primary==12
sc=read(A/'private/source-coverage.json');assert len(sc)==12 and all(not x['requested_read_gaps']for x in sc)
access=read(A/'private/primary/access.json');extra=read(A/'private/primary/grochulska-access.json');access.append(dict(extra,name='grochulska'))
for x in access:
 b=(A/'private/primary'/(x['name']+'.pdf')).read_bytes();assert len(b)==x['bytes']and sha(b)==x['sha256']
assert len(read(A/'private/render/selected.json'))==11
assert read(A/'private/lean368-access.json')['http_status']==404
assert sha((A/'private/catalogue368.txt').read_bytes())=='57cb96669bb5f4c819eadcc5cb5ec1896c73852b99c7772ae67ae5fbff4f9b36'
controls=[]
with tempfile.TemporaryDirectory(dir=P,prefix='tiny-controls-')as td:
 root=Path(td);packet=root/'packet';packet.mkdir(mode=0o700);payload=b'independent tiny control\n';f=packet/'FINAL.md';f.write_bytes(payload);f.chmod(0o444)
 manifest={'format':'r243-exact-selection-v1','files':[{'path':'FINAL.md','bytes':len(payload),'sha256':sha(payload),'mode':'0444'}],'directories':{'.':'0700'}}
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
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'selected_files':verified['files'],'selected_directories':len(read(A/'MANIFEST.json')['directories']),'selected_bytes':verified['bytes'],'entire_author_files':len(before['files']),'entire_author_subdirectories':len(before['directories']),'verifier':verified,'original_selected_copies_match':True,'canonical_blobs_authenticated':20,'canonical_exact_tree_entries':26,'text_read_intervals_bound':len(rows),'complete_source_section_files_covered':12,'primary_text_intervals_bound':primary,'primary_pdf_identities_bound':4,'guarded_history_passes':1,'history_original_intervals_bound':2,'history_limit':'Only two exact i07 mathematical intervals compared; no exhaustive clearance.','author_control_cases':len(read(A/'private/artifact-controls.json')),'independent_tiny_controls':controls,'author_originals_unchanged':True,'formal_support':'none; exact pinned document endpoint returned404','semantic_scope':'Parent read complete DERIVATIONS, SOURCE-OPERATIONS, READING-LIMITS, FINAL and outside REPORT. No source/primary/history semantic or visual coverage inherited. Documented source recovery, late comparison, old-primary exponent issue, accidental exposures and limited literature scope remain. Retained calculations are unreviewed; no nominee or mathematical grades/count.','runtime':'gpt-6-astra/xhigh/ultrafast confirmed by terminal receipt'}
(P/'replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
