#!/usr/bin/env python3
"""Read-only r233 intake; artifact mutations occur only on tiny temporary copies."""
from pathlib import Path
import datetime,gzip,hashlib,io,json,os,runpy,stat,tarfile,tempfile
P=Path(__file__).resolve().parent; A=P.parent/'fresh-structural-discovery-r233'; C=P.parents[1]; PROJECT=C.parents[2]
read=lambda p:json.loads(p.read_bytes()); sha=lambda b:hashlib.sha256(b).hexdigest()
anchors={'FINAL.md':'d9066fbda7a50bd6009b9a4a1f1e454d9ac337969a510dfd018fe59cf6629681','MANIFEST.json':'d886d0826df4caeb3b2b5df9e465493a8bf3e14214c6482e9d26677e3b80a5ca','REPORT.md':'60fc253bc631e544f2033eec56550d9c59150508d83d72fabd70c56aa8093954'}
def inventory(root):
 out={'files':{},'directories':{},'root_mode':stat.S_IMODE(root.stat().st_mode)}
 for base,ds,fs in os.walk(root,followlinks=False):
  for n in ds+fs:
   p=Path(base)/n; rel=p.relative_to(root).as_posix(); s=p.lstat(); assert not stat.S_ISLNK(s.st_mode)
   if stat.S_ISDIR(s.st_mode):out['directories'][rel]=stat.S_IMODE(s.st_mode)
   else:
    assert stat.S_ISREG(s.st_mode); b=p.read_bytes();out['files'][rel]={'bytes':len(b),'sha256':sha(b),'mode':stat.S_IMODE(s.st_mode)}
 return out
before=inventory(A); m=read(A/'MANIFEST.json'); selection=read(A/'selection.json'); assert read(A/'ANCHORS.json')==anchors
assert set(before['files'])==set(selection['paths'])|{'FINAL.md','MANIFEST.json','REPORT.md','ANCHORS.json','SEAL-CHECK.json'}
assert sha((A/'selection.json').read_bytes())==m['selection_sha256']=='7817da11478a65d893bef0b7e9b1571ac42cd77b84e794ab1932a3781866e926'
assert sha((A/'FROZEN-STATEMENT.md').read_bytes())==read(A/'freeze-anchor.json')['sha256']=='3d9a20ab3e17778919f3ae159b1e297d682c63b4a8c98474fb9c99d7e7fe65da'
assert sha((A/'author-proof.md').read_bytes())=='302d436f1beb448f9c06031d6a078892a433099d5b845b84d4b76b351659d286'
api=runpy.run_path(str(A/'verify_packet.py')); verified=api['verify_packet'](A,anchors);assert verified==read(A/'SEAL-CHECK.json')
treebytes=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(treebytes)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(treebytes)['tree'];assert len(tree)==13223;by={x['path']:x for x in tree};records=read(A/'source-authentication.json');assert len(records)==8
for x in records:
 b=(A/x['local']).read_bytes();e=by[x['path']]
 assert len(b)==x['bytes']==e['size'] and sha(b)==x['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob']==e['sha']
 assert '/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' in x['url']
prefix=records[0]['path'].rsplit('/',1)[0];assert read(A/'selected-tree.json')==[x for x in tree if x['path']==prefix or x['path'].startswith(prefix+'/')]
assert (A/'entry357.txt').read_bytes()==(PROJECT/'sources/CONTENTS.md').read_bytes()[600795:601956]
assert sha((A/'acceptance.txt').read_bytes())=='f147924a01d36cce7ad5ee13bad6ed9ed9109f3bf4b5c2386fc318aae1330984'
primaries=read(A/'primary-access.json');assert len(primaries)==8
for x in primaries:
 base=A/'private-primary'/x['id'];b=(base/'source.tar').read_bytes();tex=(base/'article.tex').read_bytes()
 assert len(b)==x['bytes'] and sha(b)==x['sha256'] and len(tex)==x['tex_bytes'] and sha(tex)==x['tex_sha256']
 if 'members' in x:
  with tarfile.open(fileobj=io.BytesIO(b),mode='r:*') as tf:
   assert [{'name':t.name,'bytes':t.size,'file':t.isfile()} for t in tf.getmembers()]==x['members']
   assert sum(tf.extractfile(t).read()==tex for t in tf.getmembers() if t.isfile() and t.name.endswith('.tex'))==1
 else:assert gzip.decompress(b)==tex
reads=[json.loads(x) for x in (A/'semantic-reads.jsonl').read_bytes().splitlines()];coverage={}
for x in reads:
 b=(A/x['file']).read_bytes();lines=b.splitlines(keepends=True);lo,hi=x['lines'];start,end=x['bytes']
 assert x['parser']=='bytes.splitlines(keepends=True)' and 1<=lo<=hi<=len(lines)
 assert [sum(map(len,lines[:lo-1])),sum(map(len,lines[:hi]))]==[start,end] and sha(b)==x['sha256']
 coverage.setdefault(x['file'],set()).update(range(lo,hi+1))
for n,expected_lines in [('paper.tex',57),('introduction.tex',258),('coordinates.tex',1166),('pinching.tex',1149),('renormalization.tex',839)]:
 assert coverage['private-source/build/source/'+n]==set(range(1,expected_lines+1)),n
boundary_count=0
for file,base,prefix in [('primary-boundaries.json',A/'private-source/build/source',''),('external-boundaries.json',A/'private-primary','')]:
 for n,rows in read(A/file).items():
  b=(base/(n if file=='primary-boundaries.json' else n+'/article.tex')).read_bytes();lines=b.splitlines(keepends=True)
  for x in rows:
   i=x['line'];assert [sum(map(len,lines[:i-1])),sum(map(len,lines[:i]))]==[x['start'],x['end']];boundary_count+=1
guards=read(A/'guards.json');assert len(guards['wildcards'])==389 and len(guards['substrings'])==162
brief=(C/'expanded-target-2026-10-17/fresh-structural-r220-isolated-r233-brief.txt').read_bytes();assert sha(brief)=='03f053c49efac00634a5233d52ec08f5d33a2b001e870bc8e69374d712d89c4d'
assert all(s.encode() in brief for s in guards['wildcards']+guards['substrings'])
nav=read(A/'guarded-navigation.json');assert len(nav['hits'])==2 and all('Rejected' in x['subsequent_classification'] for x in nav['hits'])
assert read(A/'focused-navigation.json')['hits']==[]
controls=[]
with tempfile.TemporaryDirectory(dir=P,prefix='copied-controls-') as td:
 root=Path(td);content=b'independent tiny control\n';f=root/'sample.txt';f.write_bytes(content);f.chmod(0o444)
 entries=[{'path':'sample.txt','bytes':len(content),'sha256':sha(content),'mode':'0444'}]
 def case(label,expected_error=False,paths=None):
  try:api['verify_payload'](root,entries,paths or ['sample.txt'])
  except ValueError:assert expected_error;controls.append({'case':label,'observed':'rejected'})
  else:assert not expected_error;controls.append({'case':label,'observed':'accepted'})
 case('valid independent copy')
 f.chmod(0o644);f.write_bytes(bytes([content[0]^1])+content[1:]);f.chmod(0o444);case('same-size byte mutation',True)
 f.chmod(0o644);f.write_bytes(content);case('file-mode mutation',True);f.chmod(0o444)
 case('exact-selection mutation',True,['sample.txt','extra.txt']);case('restored copy')
assert inventory(A)==before
(P/'observed-root.json').write_text(json.dumps(before,indent=2)+'\n')
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'selected_manifest_entries':len(m['entries']),'entire_author_files':len(before['files']),'entire_author_subdirectories':len(before['directories']),'verifier':verified,'verifier_sha256':sha((A/'verify_packet.py').read_bytes()),'canonical_blobs_authenticated':len(records),'primary_source_containers_and_tex_authenticated':len(primaries),'source_read_extents_bound':sum(x['file'].startswith('private-source/') for x in reads),'primary_read_extents_bound':sum(x['file'].startswith('private-primary/') for x in reads),'complete_operative_tex_extents':5,'source_and_primary_boundary_offsets_verified':boundary_count,'original_history_body_reads':0,'inherited_wildcards':389,'inherited_substrings':162,'author_control_log_cases':len(read(A/'artifact-controls.json')['controls']),'independent_copied_controls':controls,'author_originals_unchanged':True,'semantic_scope':'Parent read the entire frozen statement, author proof, derivations, primary comparison, reading limits, FINAL and REPORT. Hash/range/container authentication does not transfer child semantic source/primary reading. Full correctness and contribution remain undischarged pending independent review. No formal coverage or history clearance claimed.'}
(P/'replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
