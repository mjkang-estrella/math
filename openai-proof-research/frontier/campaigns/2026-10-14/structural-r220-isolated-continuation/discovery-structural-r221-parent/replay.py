#!/usr/bin/env python3
"""Read-only parent artifact replay; writes only this parent directory."""
from pathlib import Path
import datetime,hashlib,json,os,runpy,stat,subprocess,sys,tempfile
P=Path(__file__).resolve().parent;A=P.parent/'fresh-structural-discovery-r221';C=P.parents[1];PROJECT=C.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest()
anchors={'FINAL.md':'b8cfff280afe0f750aa9c9fef058c348bf76160087961b0c8d86672075bde922','MANIFEST.json':'f89e59ce1f4d52870394f82942bd8f1c9881795e2d6cf3b3d78a45834e1bfee9','REPORT.md':'4dc16fd7f9aead2b3c2665da2a6eef149c6c372cec3fd41397d432c6958c33db'}
def inventory(root):
 out={'files':{},'directories':{'':stat.S_IMODE(root.stat().st_mode)}}
 for base,dirs,files in os.walk(root,followlinks=False):
  for n in dirs+files:
   f=Path(base)/n;rel=f.relative_to(root).as_posix();s=f.lstat();assert not stat.S_ISLNK(s.st_mode)
   if stat.S_ISDIR(s.st_mode):out['directories'][rel]=stat.S_IMODE(s.st_mode)
   else:
    assert stat.S_ISREG(s.st_mode);b=f.read_bytes();out['files'][rel]={'bytes':len(b),'sha256':sha(b),'mode':stat.S_IMODE(s.st_mode)}
 return out
before=inventory(A)
for n,h in anchors.items():assert sha((A/n).read_bytes())==h
assert json.loads((A/'ANCHORS.json').read_bytes())==anchors
m=json.loads((A/'MANIFEST.json').read_bytes());outside={'MANIFEST.json','REPORT.md','ANCHORS.json'}
assert set(before['files'])=={x['path'] for x in m['files']}|outside
assert before['directories']=={x['path']:x['mode'] for x in m['directories']}
for x in m['files']:assert before['files'][x['path']]=={k:x[k] for k in ('bytes','sha256','mode')}
cmd=[sys.executable,'-I','-B',str(A/'verify_packet.py'),'--root',str(A),'--final-sha',anchors['FINAL.md'],'--manifest-sha',anchors['MANIFEST.json'],'--report-sha',anchors['REPORT.md']]
r=subprocess.run(cmd,capture_output=True,text=True);assert r.returncode==0,(r.stdout,r.stderr);verifier=json.loads(r.stdout)
tree_bytes=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tree_bytes)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(tree_bytes);assert len(tree['tree'])==13223;by={x['path']:x for x in tree['tree']}
acquisitions=json.loads((A/'private/acquisitions.json').read_bytes());records=[x for x in acquisitions if 'local_path' in x];assert len(records)==17 and len(acquisitions)==18
assert acquisitions[-1]['repository_path']=='lean/docs/345.md' and '404' in acquisitions[-1]['access']
for x in records:
 b=(A/x['local_path']).read_bytes();e=by[x['repository_path']];git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 assert len(b)==x['bytes']==e['size'] and git==x['git_blob']==e['sha'] and sha(b)==x['sha256']
 assert '/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' in x['url']
selected=json.loads((A/'private/tree-selected.json').read_bytes());assert selected==[x for x in tree['tree'] if x['path'].startswith('preprints/Infinitely-many-closed-geodesic-images-on-every-Riemannian-sphere-September-24-2026')]
reads=[json.loads(x) for x in (A/'private/reads.jsonl').read_text().splitlines()]
for x in reads:
 b=(A/x['file']).read_bytes();lines=b.splitlines(keepends=True);lo,hi=x['bytes'];i,j=x['lines']
 assert [sum(map(len,lines[:i-1])),sum(map(len,lines[:j]))]==[lo,hi] and sha(b[lo:hi])==x['sha256']
primary=[]
for name in ('private/primary/acquisitions.json','private/primary/additional-acquisitions.json'):
 for x in json.loads((A/name).read_bytes()):
  if 'sha256' not in x:continue
  target=A/('private/primary/GM-landing.html' if x['name']=='GM' else 'private/primary/'+x['name']+'.pdf');b=target.read_bytes();assert sha(b)==x['sha256'] and len(b)==x['bytes'];primary.append(x['name'])
x=json.loads((A/'private/primary/Shel-acquisition.json').read_bytes());b=(A/'private/primary/Shel.pdf').read_bytes();assert sha(b)==x['sha256'] and len(b)==x['bytes'];primary.append('Shel')
f=json.loads((A/'private/freeze-anchor.json').read_bytes());assert f['bytes']==before['files']['FROZEN.md']['bytes'] and f['sha256']==before['files']['FROZEN.md']['sha256']==m['frozen_statement_sha256']
assert sha((A/'private/acceptance-exact.txt').read_bytes())=='f147924a01d36cce7ad5ee13bad6ed9ed9109f3bf4b5c2386fc318aae1330984'
assert sha((A/'private/source345-catalogue-exact.txt').read_bytes())=='a7cb7179e7121fec514856ea996ae654a629f82dff16a30b691eb038b9dfe17c'
namespace=runpy.run_path(str(A/'verify_packet.py'),run_name='parent_read_only_import');check=namespace['check_entries'];controls=[]
with tempfile.TemporaryDirectory(dir=P,prefix='copied-controls-') as td:
 root=Path(td);sample=root/'sample.txt';data=(A/'FINAL.md').read_bytes();sample.write_bytes(data);sample.chmod(0o644)
 fixture={'files':[{'path':'sample.txt','bytes':len(data),'sha256':sha(data),'mode':0o644}],'directories':[{'path':'','mode':stat.S_IMODE(root.stat().st_mode)}]}
 def case(label,reject=False):
  try:check(root,fixture);ok=True
  except ValueError:ok=False
  assert ok!=reject,label;controls.append({'case':label,'observed':'rejected' if reject else 'accepted'})
 case('unaltered tiny copied payload');sample.write_bytes(bytes([data[0]^1])+data[1:]);case('same-size byte mutation',True);sample.write_bytes(data);sample.chmod(0o600);case('file mode mutation',True);sample.chmod(0o644);(root/'extra').write_text('x');case('extra file',True);(root/'extra').unlink();case('restored copied payload')
assert inventory(A)==before
(P/'observed-root.json').write_text(json.dumps(before,indent=2)+'\n')
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'anchors':anchors,'independent_selection_check':True,'selected_files':len(m['files']),'directories':len(m['directories']),'entire_author_files':len(before['files']),'entire_author_directories':len(before['directories']),'author_verifier_sha256':before['files']['verify_packet.py']['sha256'],'verifier':verifier,'canonical_blobs_authenticated':len(records),'read_extents_bound':len(reads),'primary_artifacts_authenticated':primary,'freeze_anchor_matches':True,'copied_controls':controls,'author_originals_unchanged':True,'semantic_scope':'Parent read all newly authored statement/proof/derivation/comparison/final/report/reading-limit prose and verifier/helper code. Canonical/primary/read-extent authentication does not inherit child semantic reading. No mathematical grade.'}
(P/'replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
