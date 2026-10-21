#!/usr/bin/env python3
"""Structural156 artifact archive and output-relocated finite diagnostics."""
import datetime,gzip,hashlib,importlib.util,json,re,shutil,subprocess,sys,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-structural-discovery-r156'
spec=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'f025f54cea27cb2b201c250d2dac7792c03e7c39b1e492cb5721fa7a276fe15a','MANIFEST.json':'e5973d7720286d132306342f9122e5fd7386d9c8ae3948768230bd488e1d9996','REPORT.md':'1180bc061f162a81d60418d2a7aebefa06510a8957d126de8622c994c6997b8e'}
PROTECTED={'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json':'6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9','frontier/iterations/i31-nonconical-no-mcm.md':'d606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=P)
 head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip();assert head=='c9fa241c381b5fa43043900d076b4517d320a9f4' and len(read(B/'tasks.json')['tasks'])==528
 dump('integration-baseline.json',{'observed_utc':now,'head':head,'initial_index_empty':True,'task_count':528,'task_index':525,'protected_unrelated_sha256':PROTECTED})
 before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current completed root,excluding root-directory mode;not historical whole-project or OS isolation.'})
 st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and st['workState']=='result_available' and not st['hasPendingChildRuns'] and not st['hasPendingQuestion']
 assert all(v in st['summary'] and sha(ROOT/n)==v for n,v in ANCHORS.items())
 m=read(ROOT/'MANIFEST.json');assert m['schema']==1 and len(m['files'])==77 and len(m['directories'])==9
 assert {n for n,e in before.items() if e['kind']=='file'}==set(m['files'])|set(ANCHORS) and {n for n,e in before.items() if e['kind']=='directory'}==set(m['directories'])-{'.'}
 for n,e in m['files'].items():assert (ROOT/n).stat().st_size==e['size'] and sha(ROOT/n)==e['sha256']
 tp=P/'sources/preprints-tree.json';tm=read(ROOT/'private/tree-identity.json');assert sha(tp)==tm['sha256']=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
 tree=read(tp);assert len(tree['tree'])==tm['entries']==13223 and not tree['truncated'] and not tm['truncated'];entries={e['path']:e for e in tree['tree']}
 source=read(ROOT/'private/source-identities.json');assert len(source)==15
 prefix='preprints/Rational-homology-and-Quillens-conjecture-September-24-2026/'
 assert {e['canonical_path'] for e in source}=={p for p,e in entries.items() if e['type']=='blob' and p.startswith(prefix) and p.endswith(('.md','.tex','.bib'))}
 for e in source:
  q=ROOT/e['selected_path'];data=q.read_bytes();node=entries[e['canonical_path']]
  assert len(data)==e['size']==node['size'] and sha(q)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob_sha1']==node['sha']
  assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['canonical_path']
 assert len(read(ROOT/'private/source-recheck.json'))==15 and all(e['matched'] for e in read(ROOT/'private/source-recheck.json'))
 initial=read(ROOT/'private/primary-incoming-identities.json');assert len(initial)==4 and len([e for e in initial if e['status']=='failure'])==2
 acquired=[e for e in initial if e['status']=='acquired']+[read(ROOT/'private/primary-third-incoming.json')]
 singles=[read(ROOT/'private/primary-second-incoming.json'),read(ROOT/'private/primary-fourth-incoming.json')]
 assert len(acquired)==3 and len(singles)==2
 for e in acquired+singles:
  q=ROOT/e['path'];assert q.stat().st_size==e['size'] and sha(q)==e['sha256']
 for e,name in zip(singles,['private/primary/gelvin-moller-v2.tex','private/primary/piterman-v2.tex']):
  q=ROOT/name;assert q.stat().st_size==e['selected_size'] and sha(q)==e['selected_sha256'] and gzip.decompress((ROOT/e['path']).read_bytes())==q.read_bytes()
 renders=[n for n in m['files'] if n.startswith('private/primary/') and n.endswith('.png')];texts=[n for n in m['files'] if n.startswith('private/primary/') and n.endswith('.txt')];assert len(renders)==6 and len(texts)==3
 originals=read(ROOT/'private/incoming-original-identities.json');assert len(originals)==8;stable=[]
 for e in originals:
  p=P/e['original_path'];assert p.stat().st_size==e['size'] and sha(p)==e['sha256'];stable.append({'path':e['original_path'],'bytes':e['size'],'sha256':e['sha256']})
 selected=read(ROOT/'private/selected-membership.json');assert len(selected)==10;excerpts=[];whole=0
 for e in selected:
  q=ROOT/e['selected_path'];p=P/e['original_path'];assert q.stat().st_size==e['size'] and sha(q)==e['sha256']
  if e['selection']=='whole original':assert p.read_bytes()==q.read_bytes();whole+=1
  else:assert q.read_bytes() in p.read_bytes();excerpts.append(e)
 assert whole==8 and len(excerpts)==2
 ctl=read(ROOT/'private/copied-controls/results.json');fixture=ROOT/'private/copied-controls/fixture';fa=read(ROOT/'private/copied-controls/fixture-anchors.json')
 assert len(ctl)==8 and all((e['exit_code']==0)==e['expected_accept'] and e['unchanged_by_verifier'] for e in ctl) and all(sha(fixture/n)==v for n,v in fa.items())
 assert len(read(fixture/'MANIFEST.json')['files'])==3
 for a,b in [('notes/01-prefreeze-calculations.md','note.md'),('original/subgroup_diagnostic.py','diagnostic.py'),('original/verify.py','verify.py')]:assert (ROOT/a).read_bytes()==(fixture/b).read_bytes()
 cases=[];finite={}
 with tempfile.TemporaryDirectory(prefix='structural156-copy-',dir=O) as tmp:
  copy=Path(tmp)/'packet';shutil.copytree(ROOT,copy);args=[str(copy),*ANCHORS.values()]
  def check(label,want,custom=None):
   state=snap(copy);r=subprocess.run([sys.executable,'-I','-B',str(copy/'original/verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30)
   assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state
   cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
  check('baseline_full_packet',True);q=copy/'notes/01-prefreeze-calculations.md';data=q.read_bytes();q.write_bytes(data+b'\nCONTROL\n');check('changed_payload',False)
  q.unlink();check('missing_payload',False);q.write_bytes(data);q=copy/'private/.extra';q.write_text('extra');check('hidden_extra',False);q.unlink()
  q=copy/'private/.empty';q.mkdir();check('empty_extra_directory',False);q.rmdir();wrong=args.copy();wrong[2]='0'*64;check('wrong_manifest_anchor',False,wrong)
  q=copy/'REPORT.md';data=q.read_bytes();q.write_bytes(data+b'\nCONTROL\n');check('changed_REPORT',False);q.write_bytes(data);check('restored',True);assert snap(copy)==before
  sandbox=Path(tmp)/'diagnostics';sandbox.mkdir()
  for name,receipt in [('subgroup_diagnostic.py','private/gl32-diagnostic.json'),('subgroup_residues.py','private/gl32-residues-diagnostic.json')]:
   original=(ROOT/'original'/name).read_text();out=sandbox/(name+'.json')
   patched,count=re.subn(r'^OUT=Path\([^\n]+\)$','OUT=Path('+repr(str(out))+')',original,flags=re.M);assert count==1
   program=sandbox/name;program.write_text(patched)
   r=subprocess.run([sys.executable,'-I','-B',str(program)],capture_output=True,text=True,timeout=60,cwd=P);assert r.returncode==0,r.stderr
   result=json.loads(r.stdout);assert result==read(out)==read(ROOT/receipt)
   finite[name]={'only_OUT_destination_relocated':True,'original_sha256':sha(ROOT/'original'/name),'relocated_program_sha256':sha(program),'matches_sealed_receipt':True,'result':result}
  assert snap(copy)==before
 assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in PROTECTED.items())
 dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':6,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Artifact checks only;manifest binds exact files/directories and bytes,not modes.Parent snapshots additionally observe modes/links except root-directory mode.'})
 dump('finite-replay.json',{'programs':finite,'limits':'Only fixed OUT destinations relocated in disposable program copies,removed afterward.168matrices/77nonidentity2-subgroups/all455nonemptychainlinks for GL3(F2),not all groups/primes or a substantial obstruction.'})
 dump('input-authentication.json',{'source_blobs':15,'primary_received_objects':5,'primary_pdfs':3,'primary_single_gzip_sources':2,'independently_reconstructed_selected_sources':2,'bound_text_derivatives':texts,'bound_renders':renders,'failed_acquisitions':2,'stable_whole_original_copies':8,'selected_excerpts':2,'selected_fixture_members':3,'limits':'Local byte/path/member observations only.No fresh protected semantic reading,PDF/figure visual or transitive coverage.Quillen original remains unread;Bouc text is not claimed semantically useful.'})
 dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'payload_files':77,'whole_root_files':80,'subdirectories':8,'manifest_directories_including_dot':9,'source_blobs':15,'primary_received_objects':5,'primary_pdfs':3,'primary_selected_sources':2,'stable_named_originals':stable,'selected_original_excerpts':excerpts,'artifact_cases':8,'negative_cases':6,'finite_group_order':168,'finite_subgroups':77,'finite_chain_links':455,'local_residue_images':14,'each_local_rank':2,'joint_rank':8,'whole_actual_root_unchanged':True,'limits':'Artifact and exact finite-group observations only,no independent mathematical grade.Parent snapshots exclude root-directory mode.'})
 print(json.dumps({'files':80,'payload':77,'subdirectories':8,'source_blobs':15,'primary_objects':5,'stable_whole_copies':8,'excerpts':2,'artifact_cases':8,'finite_chain_links':455,'local_ranks':'14x2','joint_rank':8}))
if __name__=='__main__':main()
