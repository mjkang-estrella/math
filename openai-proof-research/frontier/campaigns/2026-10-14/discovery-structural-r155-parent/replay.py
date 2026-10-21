#!/usr/bin/env python3
"""Structural155 artifact archive and bounded existing finite diagnostics."""
import datetime,hashlib,importlib.util,io,json,shutil,subprocess,sys,tarfile,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-structural-discovery-r155'
spec=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'b864fae946db7b82e55e06c269dc57d2252a8e0602bc158b153707138e9db085','MANIFEST.json':'fb3e38b7420a099ebccb90ebf7e014edf793a2a958a55af8bdc66ee23409ae09','REPORT.md':'acbbecfda72fb852efdd09d35e9aba1268635ced6196e7c62de9457ef6c5fc37'}
PROTECTED={'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json':'6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9','frontier/iterations/i31-nonconical-no-mcm.md':'d606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=P)
 head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip();assert head=='c8fbb09e0904ff99d33a2f15aa0555dcff84c67e' and len(read(B/'tasks.json')['tasks'])==525
 dump('integration-baseline.json',{'observed_utc':now,'head':head,'initial_index_empty':True,'task_count':525,'task_index':522,'protected_unrelated_sha256':PROTECTED})
 before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current completed root,excluding root-directory mode;not historical whole-project or OS isolation.'})
 st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and st['workState']=='result_available' and not st['hasPendingChildRuns'] and not st['hasPendingQuestion']
 assert all(v in st['summary'] and sha(ROOT/n)==v for n,v in ANCHORS.items())
 m=read(ROOT/'MANIFEST.json');assert m['version']==1 and len(m['files'])==60 and len(m['directories'])==9
 rows={e['path']:e for e in m['files']};assert len(rows)==60 and {n for n,e in before.items() if e['kind']=='file'}==set(rows)|set(ANCHORS)
 assert {n for n,e in before.items() if e['kind']=='directory'}==set(m['directories'])-{'.'}
 for n,e in rows.items():assert (ROOT/n).stat().st_size==e['size'] and sha(ROOT/n)==e['sha256']
 tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
 tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']}
 source=read(ROOT/'private/source-identities.json');assert len(source)==10
 prefix='preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/'
 assert {e['canonical_path'] for e in source}=={p for p,e in entries.items() if e['type']=='blob' and p.startswith(prefix) and p.endswith(('.md','.tex','.bib'))}
 for e in source:
  q=ROOT/e['member'];data=q.read_bytes();node=entries[e['canonical_path']]
  assert len(data)==e['size']==node['size'] and sha(q)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob_sha1']==node['sha']
  assert e['pinned_url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['canonical_path']
 primary=read(ROOT/'private/primary-identities.json');assert len(primary)==4;members=0
 for e in primary:
  version=e['url'].rsplit('/',1)[1];q=ROOT/'private/primary'/(version+'.response');data=q.read_bytes();assert len(data)==e['size'] and sha(q)==e['sha256']
  with tarfile.open(fileobj=io.BytesIO(data),mode='r:*') as tf:
   for a in e['selected_members']:
    p=ROOT/a['member'];node=tf.getmember(a['original_member']);assert node.isfile() and tf.extractfile(node).read()==p.read_bytes() and p.stat().st_size==a['size'] and sha(p)==a['sha256'];members+=1
 assert members==6
 originals=read(ROOT/'private/incoming-original-identities.json');assert len(originals)==10;stable=[];mutable=[]
 for e in originals:
  p=P/e['original_path']
  if e['original_path']=='frontier/NEW-TEN-2026-10-14.md':mutable.append(e|{'current_sha256':sha(p),'current_matches_historical_observation':sha(p)==e['sha256']});continue
  assert p.stat().st_size==e['size'] and sha(p)==e['sha256'];stable.append({'path':e['original_path'],'bytes':e['size'],'sha256':e['sha256']})
 assert len(stable)==9 and len(mutable)==1
 selected=read(ROOT/'private/selected-membership.json');assert len(selected)==10;whole=0;excerpts=[]
 for e in selected:
  q=ROOT/e['member'];assert q.stat().st_size==e['size'] and sha(q)==e['sha256'];p=P/e['original_path']
  if e['selection']=='whole original bytes':assert p.read_bytes()==q.read_bytes();whole+=1
  elif e['original_path'].startswith('frontier/iterations/'):
   assert ('\n'.join(p.read_text().splitlines()[:120])+'\n').encode()==q.read_bytes();excerpts.append(e)
  else:assert e['original_path']=='frontier/NEW-TEN-2026-10-14.md' and q.read_bytes() in p.read_bytes();excerpts.append(e)
 assert whole==8 and len(excerpts)==2
 recheck=read(ROOT/'private/originals-final-recheck.json');assert recheck['named_originals']==10 and recheck['all_match_incoming_identities']
 ctl=read(ROOT/'seal/control-results.json');fixture=ROOT/'seal/copied-control';assert len(ctl['results'])==8 and all((e['exit']==0)==e['expected_accept'] and e['copy_unchanged_by_verifier'] for e in ctl['results'])
 assert all(sha(fixture/n)==v for n,v in ctl['fixture_anchors'].items()) and len(read(fixture/'MANIFEST.json')['files'])==2
 assert (fixture/'verify_readonly.py').read_bytes()==(ROOT/'original/verify_readonly.py').read_bytes()
 cases=[];finite={}
 with tempfile.TemporaryDirectory(prefix='structural155-copy-',dir=O) as tmp:
  copy=Path(tmp)/'packet';shutil.copytree(ROOT,copy);args=[str(copy),'--final',ANCHORS['FINAL.md'],'--manifest',ANCHORS['MANIFEST.json'],'--report',ANCHORS['REPORT.md']]
  def check(label,want,custom=None):
   state=snap(copy);r=subprocess.run([sys.executable,'-I','-B',str(copy/'original/verify_readonly.py'),*(custom or args)],capture_output=True,text=True,timeout=30)
   assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state
   cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
  check('baseline_full_packet',True);q=copy/'notes/01-prefreeze-calculations.md';data=q.read_bytes();q.write_bytes(data+b'\nCONTROL\n');check('changed_payload',False)
  q.unlink();check('missing_payload',False);q.write_bytes(data);q=copy/'private/.extra';q.write_text('extra');check('hidden_extra',False);q.unlink()
  q=copy/'private/.empty';q.mkdir();check('extra_empty_directory',False);q.rmdir();wrong=args.copy();wrong[4]='0'*64;check('wrong_manifest_anchor',False,wrong)
  q=copy/'REPORT.md';data=q.read_bytes();q.write_bytes(data+b'\nCONTROL\n');check('changed_REPORT',False);q.write_bytes(data);check('restored',True)
  for name,receipt in [('diagnostic.py','private/diagnostic.json'),('edge_grading.py','private/edge-grading-closed-components.json')]:
   state=snap(copy);r=subprocess.run([sys.executable,'-I','-B',str(copy/'original'/name)],capture_output=True,text=True,timeout=60,cwd=P);assert r.returncode==0,r.stderr
   result=json.loads(r.stdout);assert result==read(ROOT/receipt) and snap(copy)==state;finite[name]={'matches_sealed_receipt':True,'result':result}
  assert snap(copy)==before
 assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in PROTECTED.items())
 dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':6,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Artifact checks only;manifest authenticates file/directory membership and bytes,not modes.Parent snapshots additionally observe modes/links,excluding root-directory mode.'})
 dump('finite-replay.json',{'programs':finite,'limits':'Existing bounded diagnostics,not full mathematics or novelty.213cases/7154words/1325components,total demand<=5;closed two six-word components and induced-path edge equalities.Earlier collision-search receipt is retained byte-bound,not a fresh exhaustive collision search.'})
 dump('input-authentication.json',{'source_blobs':10,'primary_incoming_archives':4,'independently_reconstructed_members':6,'stable_whole_original_byte_identities':9,'selected_whole_copies':8,'selected_excerpts':2,'historical_mutable_journal':mutable,'selected_control_payloads':2,'limits':'Local bytes/path/member identity only,no fresh protected semantic reading,remote retrieval,PDF/figure visual or transitive coverage.'})
 dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'payload_files':60,'whole_root_files':63,'subdirectories':8,'manifest_directories_including_dot':9,'source_blobs':10,'primary_received_objects':4,'primary_members':6,'stable_named_originals':stable,'selected_original_excerpts':excerpts,'artifact_cases':8,'negative_cases':6,'finite_cases':213,'finite_words':7154,'finite_components':1325,'whole_actual_root_unchanged':True,'limits':'Artifact and bounded algebra observations only;no mathematical grade.Parent snapshots exclude root-directory mode.'})
 print(json.dumps({'files':63,'payload':60,'subdirectories':8,'source_blobs':10,'primary_objects':4,'primary_members':6,'stable_original_identities':9,'whole_copies':8,'excerpts':2,'artifact_cases':8,'finite_cases':213}))
if __name__=='__main__':main()
