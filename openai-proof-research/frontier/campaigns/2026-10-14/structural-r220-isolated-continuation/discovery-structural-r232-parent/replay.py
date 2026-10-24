#!/usr/bin/env python3
"""Read-only parent replay of r232; mutation controls use independent tiny copies."""
from pathlib import Path
import datetime,hashlib,json,os,stat,subprocess,sys,tempfile
P=Path(__file__).resolve().parent;A=P.parent/'fresh-structural-discovery-r232';S=A/'selected';C=P.parents[1];PROJECT=C.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(p.read_bytes())
anchors={'FINAL.md':'a5982cae6f21221136b4bfe93a7dda4cf77de43cc7867d905a5f8b4b33e87cac','MANIFEST.json':'690aa2c27df417b1495f97ca4b51cbc6b2dac781145221d08e06efdcce744400','REPORT.md':'1c223784f7f7e524f890ede2f724f4a9a168cf66d1be5803f2d9236bc9c13a36'}
def inventory(root):
 out={'files':{},'directories':{},'root_mode':stat.S_IMODE(root.stat().st_mode)}
 for base,ds,fs in os.walk(root,followlinks=False):
  for n in ds+fs:
   p=Path(base)/n;rel=p.relative_to(root).as_posix();st=p.lstat();assert not stat.S_ISLNK(st.st_mode)
   if stat.S_ISDIR(st.st_mode):out['directories'][rel]=stat.S_IMODE(st.st_mode)
   else:
    assert stat.S_ISREG(st.st_mode);b=p.read_bytes();out['files'][rel]={'bytes':len(b),'sha256':sha(b),'mode':stat.S_IMODE(st.st_mode)}
 return out
before=inventory(A);selected=inventory(S);m=read(S/'MANIFEST.json');detached=read(A/'DETACHED-ANCHORS.json')
for key,n in [('FINAL','FINAL.md'),('MANIFEST','MANIFEST.json'),('REPORT','REPORT.md')]:
 assert detached[key]['sha256']==anchors[n] and sha((A/detached[key]['path']).read_bytes())==anchors[n]
assert sha((S/'author/FROZEN-STATEMENT.md').read_bytes())==detached['statement_sha256']=='9e57e9fcd07c3653bc8568c05f4e1ba57cf4ae56bd58f7b38a087b08ee7e1e68'
assert sha((S/'author/AUTHOR-PROOF.md').read_bytes())==detached['author_proof_sha256']=='477e211c486f14fd1118f0ceb2f1e550cb65303dc2eea1b65c357fb8437b78a7'
expected={e['path']:e for e in m['files']};assert set(selected['files'])==set(expected)|{'FINAL.md','MANIFEST.json'}
for n,e in expected.items():
 assert selected['files'][n]==dict(bytes=e['bytes'],sha256=e['sha256'],mode=int(e['mode'],8))
assert {'.':selected['root_mode'],**selected['directories']}=={n:int(v,8) for n,v in m['directories'].items()}
assert all(selected['files'][n]['mode']==0o400 for n in ['FINAL.md','MANIFEST.json'])
matched=0
for rel,e in expected.items():
 original=A/rel
 for prefix in ['author/','code/','private/evidence/']:
  if rel.startswith(prefix):original=A/rel[len(prefix):]
 assert original.is_file() and sha(original.read_bytes())==e['sha256'],rel
 matched+=1
def invoke(root,report,expected_anchors):
 r=subprocess.run([sys.executable,'-I','-B',str(S/'code/verify_packet.py'),'--root',str(root),'--final-sha256',expected_anchors['FINAL.md'],'--manifest-sha256',expected_anchors['MANIFEST.json'],'--report',str(report),'--report-sha256',expected_anchors['REPORT.md']],capture_output=True,text=True)
 return r.returncode,json.loads(r.stdout)
code,verified=invoke(S,A/'REPORT.md',anchors);assert code==0
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=json.loads(tb)['tree'];assert len(tree)==13223;by={x['path']:x for x in tree}
records=read(A/'authentication-private.json');assert len(records)==22
for x in records:
 b=(S/x['local']).read_bytes();e=by[x['path']]
 assert len(b)==x['bytes']==e['size'] and sha(b)==x['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob']==e['sha']
 assert '/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' in x['url']
prefixes={x['path'].split('/')[1] for x in records};assert read(A/'canonical-tree-private.json')==[x for x in tree if len(x['path'].split('/'))>1 and x['path'].split('/')[1] in prefixes]
reads=[json.loads(x) for x in (A/'semantic-reads-private.jsonl').read_bytes().splitlines()]
for x in reads:
 b=(S/x['file']).read_bytes();assert 0<=x['start']<x['end']<=len(b) and sha(b[x['start']:x['end']])==x['sha256']
coverage=read(A/'coverage-private.json')['coverage']
for x in coverage:
 b=(S/x['file']).read_bytes();assert len(b)==x['bytes'];mask=bytearray(len(b))
 for r in reads:
  if r['file']==x['file']:mask[r['start']:r['end']]=b'\1'*(r['end']-r['start'])
 gaps=[];i=0
 while i<len(b):
  if mask[i]:i+=1;continue
  j=i+1
  while j<len(b) and not mask[j]:j+=1
  gaps.append([i,j]);i=j
 assert gaps==x['gaps'],x['file']
sections=[x for x in coverage if '/sections/' in x['file']];assert len(sections)==11 and all(not x['gaps'] for x in sections)
primaries=read(A/'primary-access-private.json')+[read(A/(n+'-access-private.json')) for n in ['Eschenburg','PetersenSprouse','GRS']]
for x in primaries:
 b=(S/'private/primary'/(x['id']+'.pdf')).read_bytes();assert len(b)==x.get('bytes',x.get('pdfbytes')) and sha(b)==x['sha256']
 b=(S/'private/primary'/(x['id']+'.txt')).read_bytes();assert len(b)==x.get('text_bytes',x.get('textbytes'))
primary_reads=[json.loads(x) for x in (A/'primary-reads-private.jsonl').read_bytes().splitlines()]
for x in primary_reads:
 b=(S/'private/primary'/(x['id']+'.txt')).read_bytes();assert 0<=x['start']<x['end']<=len(b) and sha(b[x['start']:x['end']])==x['sha256']
for key,name in [('navigation','lean356.md'),('comparator','WeakHessian.lean')]:
 x=read(A/'lean-access-private.json')[key];b=(S/'private'/name).read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256']
assert b'sorry' in (S/'private/WeakHessian.lean').read_bytes()
g=read(A/'guards.json');assert len(g['wildcards'])==387 and len(g['substrings'])==162
assert read(A/'history-navigation-private.json')['hits']==[] and read(A/'history-navigation-private.json')['semantic_sections_read']==[]
assert read(A/'history-refined-private.json')['candidate_heading_metadata']==[] and read(A/'history-refined-private.json')['body_reads']==[]
controls=[]
with tempfile.TemporaryDirectory(dir=P,prefix='copied-controls-') as td:
 root=Path(td)/'selected';root.mkdir();f=root/'sample.txt';content=b'independent tiny copied control\n';f.write_bytes(content);f.chmod(0o400);(root/'FINAL.md').write_bytes(b'Copied final\n');(root/'FINAL.md').chmod(0o400);report=Path(td)/'REPORT.md';report.write_bytes(b'Copied report\n')
 mf=root/'MANIFEST.json';mf.write_text(json.dumps({'files':[{'path':'sample.txt','bytes':len(content),'sha256':sha(content),'mode':'0400'}],'directories':{'.':'0700'}}));mf.chmod(0o400);root.chmod(0o700)
 exp={n:sha((report if n=='REPORT.md' else root/n).read_bytes()) for n in anchors}
 def case(label,reject=False,override=None):
  code,result=invoke(root,report,override or exp);assert bool(code)==reject,(label,result);controls.append({'case':label,'observed':'rejected' if reject else 'accepted'})
 case('valid independent copied selection')
 f.chmod(0o600);f.write_bytes(bytes([content[0]^1])+content[1:]);f.chmod(0o400);case('same-size byte mutation',True)
 f.chmod(0o600);f.write_bytes(content);f.chmod(0o400)
 f.chmod(0o600);case('file mode mutation',True);f.chmod(0o400)
 extra=root/'extra';extra.write_bytes(b'x');case('extra file',True);extra.unlink()
 case('wrong detached anchor',True,dict(exp,**{'MANIFEST.json':'0'*64}))
 root.chmod(0o500);case('directory mode mutation',True);root.chmod(0o700)
 case('restored copies')
assert inventory(A)==before
(P/'observed-root.json').write_text(json.dumps(before,indent=2)+'\n')
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'selected_manifest_entries':len(expected),'selected_total_files':len(selected['files']),'selected_subdirectories':len(selected['directories']),'entire_author_files':len(before['files']),'entire_author_subdirectories':len(before['directories']),'selected_files_matching_unselected_originals':matched,'verifier':verified,'verifier_sha256':sha((S/'code/verify_packet.py').read_bytes()),'canonical_blobs_authenticated':len(records),'source_read_extents_bound':len(reads),'complete_operative_section_extents':len(sections),'primary_read_extents_bound':len(primary_reads),'primary_pdfs_authenticated':len(primaries),'recorded_visual_pages':3,'formal_artifacts_authenticated':2,'original_history_body_reads':0,'author_control_log_cases':len(read(A/'tiny-control-results.json')['results']),'independent_copied_controls':controls,'author_originals_unchanged':True,'semantic_scope':'Parent read entire frozen statement, author proof, compatibility, prefreeze, reading scope, live reading notes, FINAL and outside REPORT. Hash/range authentication does not inherit child semantic or visual source/primary coverage. No mathematical grade. Prior administrative template and metadata dumps clipped; required schemas recovered with bounded selections; no authored mathematical proof reading truncated.'}
(P/'replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))

