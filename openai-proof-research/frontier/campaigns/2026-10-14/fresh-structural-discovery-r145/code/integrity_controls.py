"""Small copied fixtures with independent reduced membership; no original manifest reuse."""
from pathlib import Path
import os,json,hashlib,shutil,subprocess,datetime
R=Path(__file__).resolve().parents[1];P=R.parents[3]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def inv(root):
 files={};dirs=[]
 for parent,ds,fs in os.walk(root):
  dirs.extend(str((Path(parent)/d).relative_to(root)) for d in ds)
  for f in fs:
   p=Path(parent)/f;files[str(p.relative_to(root))]={'size':p.stat().st_size,'sha256':sha(p)}
 return files,sorted(dirs)
base=R/'private/integrity-controls';base.mkdir(exist_ok=False);fixture=base/'reduced-own-copy';(fixture/'notes').mkdir(parents=True)
source=R/'notes/02-integrated-reduction-and-gap.md';shutil.copyfile(source,fixture/'notes/reduction.md')
(fixture/'FINAL.md').write_text('Reduced copied integrity fixture, not an original-root authentication.\n')
(fixture/'REPORT.md').write_text('Only reduction.md is selected. Its membership is independent.\n')
files,dirs=inv(fixture);files={p:v for p,v in files.items() if p not in {'FINAL.md','REPORT.md'}}
(fixture/'MANIFEST.json').write_text(json.dumps({'format':'r145-exact-membership-v1','scope':'independent reduced fixture only','files':files,'directories':dirs},indent=2)+'\n')
anchors={n:sha(fixture/n) for n in ['FINAL.md','MANIFEST.json','REPORT.md']};verifier=R/'code/verify_packet.py'
source_before=sha(source);results=[]
def run(label,want_success,change_anchor=False):
 before=inv(fixture);args=['python',str(verifier),str(fixture)]
 for n,option in [('FINAL.md','final'),('MANIFEST.json','manifest'),('REPORT.md','report')]:
  val=anchors[n]
  if change_anchor and n=='MANIFEST.json':val=('0' if val[0]!='0' else '1')+val[1:]
  args+=['--'+option+'-sha256',val]
 cp=subprocess.run(args,capture_output=True,text=True,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1','TMPDIR':str(R/'scratch')})
 assert (cp.returncode==0)==want_success and inv(fixture)==before
 results.append({'case':label,'expected_accept':want_success,'returncode':cp.returncode,'stdout':cp.stdout.strip(),'stderr':cp.stderr.strip(),'fixture_unchanged_by_verifier':True})
run('clean reduced copy',True)
p=fixture/'notes/reduction.md';data=p.read_bytes();p.write_bytes(data+b'changed\n');run('changed copied payload',False);p.write_bytes(data)
p.unlink();run('missing copied payload',False);p.write_bytes(data)
(fixture/'.extra').write_text('extra');run('extra hidden file',False);(fixture/'.extra').unlink()
(fixture/'.empty').mkdir();run('extra empty directory',False);(fixture/'.empty').rmdir()
run('wrong detached manifest anchor',False,True);run('restored reduced copy',True)
assert sha(source)==source_before
context=json.loads((R/'private/context/receipts.json').read_text());observations=[]
for item in context['records']:
 current=sha(P/item['canonical_local_path']);observations.append({'path':item['canonical_local_path'],'current_sha256':current,'snapshot_sha256':item['sha256'],'matches_late_snapshot':current==item['sha256']})
tree=json.loads((P/'sources/preprints-tree.json').read_text());lookup={e['path']:e for e in tree['tree']};auth=[]
for item in json.loads((R/'private/pinned/receipts.json').read_text()):
 data=(R/item['local']).read_bytes();blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest();e=lookup[item['canonical_path']]
 assert len(data)==e['size']==item['size'] and blob==e['sha']==item['git_blob'] and hashlib.sha256(data).hexdigest()==item['sha256']
 auth.append({'path':item['canonical_path'],'tree_size_gitblob_sha256_match':True})
(base/'receipt.json').write_text(json.dumps({'time':datetime.datetime.now(datetime.timezone.utc).isoformat(),'meaning':'integrity only; no mathematical or whole-original-root verdict','source_note_unchanged':True,'fixture_external_anchors':anchors,'cases':results,'selected_current_originals':observations,'pinned_bindings':auth},indent=2)+'\n')
print(json.dumps({'cases':len(results),'expected_rejections':sum(not x['expected_accept'] for x in results),'selected_original_matches':sum(x['matches_late_snapshot'] for x in observations),'selected_originals':len(observations),'pinned_files_authenticated':len(auth)},sort_keys=True))
