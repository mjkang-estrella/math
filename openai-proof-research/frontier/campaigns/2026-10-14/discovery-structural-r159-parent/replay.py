#!/usr/bin/env python3
"""Structural159 artifact authentication and redirected bounded routing checks."""
import datetime,hashlib,importlib.util,json,re,shutil,subprocess,sys,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-structural-discovery-r159'
spec=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'5e4a76b5870e2e13f6ab9821a6bd7d21aca0d4467d8b38097891e0d8160e3f30','MANIFEST.json':'02809af18932ef62478fd5de369fef86728b600525c8d445c80bbe06f168c6ed','REPORT.md':'9862fdcb58b5e4bfd5b5b9a52310ba6e5fb28fdac95037e87d0c241d6f7ce423'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 now=datetime.datetime.now(datetime.timezone.utc).isoformat();base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'] and len(read(B/'tasks.json')['tasks'])==537
 before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current sealed root excludes root-directory mode.'})
 st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and st['workState']=='result_available' and not st['hasPendingChildRuns'] and not st['hasPendingQuestion'];assert all(v in st['summary'] and sha(ROOT/n)==v for n,v in ANCHORS.items())
 m=read(ROOT/'MANIFEST.json');assert len(m['files'])==47 and len(m['directories'])==10;assert {n for n,e in before.items() if e['kind']=='file'}==set(m['files'])|set(ANCHORS) and {n for n,e in before.items() if e['kind']=='directory'}==set(m['directories'])
 for n,e in m['files'].items():assert (ROOT/n).stat().st_size==e['bytes'] and sha(ROOT/n)==e['sha256']
 source=read(ROOT/'receipts/pinned-source-selection.json');tp=P/'sources/preprints-tree.json';assert source['canonical_objects']==[] and sha(tp)==source['tree_sha256']=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated']
 primary=read(ROOT/'receipts/primary-acquisition01.json')+read(ROOT/'receipts/primary-acquisition02.json');assert len(primary)==4
 for e in primary:
  q=ROOT/'private/primary'/(e['name']+'.pdf');assert q.stat().st_size==e['bytes'] and sha(q)==e['sha256'] and sha(q.with_suffix('.txt'))==e['text_sha256']
 renders=sorted((ROOT/'private/primary').glob('*.png'));assert len(renders)==3 and all(p.read_bytes().startswith(b'\x89PNG\r\n\x1a\n') for p in renders)
 originals=read(ROOT/'receipts/incoming-original-identities.json');assert len(originals)==10;stable=[];copies=[]
 for e in originals:
  p=P/e['original_path']
  if e['copy_scope'].startswith('excerpt'):
   q=ROOT/e['copy_path'];assert q.stat().st_size==e['bytes'] and sha(q)==e['sha256'] and q.read_bytes() in p.read_bytes()
  else:
   assert p.stat().st_size==e['bytes'] and sha(p)==e['sha256'];stable.append({'path':e['original_path'],'bytes':e['bytes'],'sha256':e['sha256'],'selection':e['copy_scope']})
   if 'copy_path' in e:assert p.read_bytes()==(ROOT/e['copy_path']).read_bytes();copies.append(e['copy_path'])
 assert len(stable)==9 and len(copies)==7;membership=read(ROOT/'receipts/selected-history-copy-membership.json');assert set(membership['members'])==set(copies)|{'private/history/acceptance-lines19-28.txt'}
 ctl=read(ROOT/'receipts/copied-controls.json');fixture=ROOT/'controls/selected-fixture';assert len(ctl['controls'])==9 and all((e['exit_code']==0)==e['expected_accept'] and e['after_equal'] for e in ctl['controls']);assert all(sha(fixture/n)==v for n,v in ctl['fixture_anchors'].items()) and len(read(fixture/'MANIFEST.json')['files'])==3
 for e in ctl['selected_membership']:assert (ROOT/e['source']).read_bytes()==(fixture/e['selected_copy']).read_bytes()
 cases=[];finite={}
 with tempfile.TemporaryDirectory(prefix='structural159-copy-',dir=O) as tmp:
  copy=Path(tmp)/'packet';shutil.copytree(ROOT,copy);args=[str(copy),'--final',ANCHORS['FINAL.md'],'--manifest',ANCHORS['MANIFEST.json'],'--report',ANCHORS['REPORT.md']]
  def check(label,want,custom=None):
   state=snap(copy);r=subprocess.run([sys.executable,'-I','-B',str(copy/'code/verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30);assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state;cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
  check('baseline_full_packet',True);q=copy/'notes/01-prefreeze-routing-calculations.md';data=q.read_bytes();q.write_bytes(data+b'\nCONTROL\n');check('changed_payload',False);q.unlink();check('missing_payload',False);q.write_bytes(data);q=copy/'private/.extra';q.write_text('extra');check('hidden_extra',False);q.unlink();q=copy/'private/.empty';q.mkdir();check('empty_extra_directory',False);q.rmdir();wrong=args.copy();wrong[4]='0'*64;check('wrong_manifest_anchor',False,wrong)
  for name in ['REPORT.md','FINAL.md']:
   q=copy/name;data=q.read_bytes();q.write_bytes(data+b'\nCONTROL\n');check('changed_'+name,False);q.write_bytes(data)
  check('restored',True);assert snap(copy)==before
  sandbox=Path(tmp)/'finite';sandbox.mkdir();(sandbox/'receipts').mkdir()
  for name,receipt in [('core_routes.py','core-routes.json'),('biclique_routes.py','biclique-routes.json')]:
   original=(ROOT/'code'/name).read_text();patched,count=re.subn(r"^ROOT=Path\('[^']+'\)$",'ROOT=Path('+repr(str(sandbox))+')',original,count=1,flags=re.M);assert count==1;program=sandbox/name;program.write_text(patched);r=subprocess.run([sys.executable,'-I','-B',str(program)],capture_output=True,text=True,timeout=60,cwd=P);assert r.returncode==0,r.stderr;result=read(sandbox/'receipts'/receipt);assert result==read(ROOT/'receipts'/receipt);finite[name]={'only_fixed_output_root_relocated':True,'original_sha256':sha(ROOT/'code'/name),'relocated_program_sha256':sha(program),'matches_sealed_receipt':True,'result':result}
 assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':7,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Artifact checks only;manifest binds exact files/directories/bytes,not modes;parent snapshots exclude root-directory mode.'})
 dump('finite-replay.json',{'programs':finite,'limits':'Bounded support only;no general rejected-case proof,independent review,novelty or mathematical gate.Only fixed output roots relocated in disposable copies.'})
 dump('input-authentication.json',{'selected_pinned_source_objects':0,'pinned_source_development_met':False,'primary_pdf_text_pairs':4,'bound_render_members':3,'stable_whole_original_copies':7,'stable_identity_only_originals':2,'selected_acceptance_excerpt':1,'selected_fixture_members':3,'limits':'Local byte/path/member observations only.No canonical manuscript proof/Gitblob authentication or fresh protected semantic/PDF/visual/transitive reading.'})
 dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'payload_files':47,'whole_root_files':50,'subdirectories':10,'source_blobs':0,'primary_pdf_text_pairs':4,'render_members':3,'stable_named_originals':stable,'stable_whole_original_copies':7,'stable_identity_only_originals':2,'selected_acceptance_excerpt':1,'artifact_cases':9,'negative_cases':7,'finite_parameter_tuples':22848,'finite_constructed_routings':10129,'tiny_generic_searches':148,'whole_actual_root_unchanged':True,'limits':'Artifact and finite observations only.No pinned-source development,mathematical/contribution grade or nominee.'})
 print(json.dumps({'payload':47,'files':50,'subdirs':10,'source_blobs':0,'pdf_text_pairs':4,'renders':3,'whole_copies':7,'identity_only':2,'artifact_cases':9,'finite_parameter_tuples':22848,'constructed_routings':10129,'tiny_searches':148}))
if __name__=='__main__':main()
