#!/usr/bin/env python3
"""Structural158 archive authentication and disposable finite replay."""
import datetime,hashlib,importlib.util,json,re,shutil,subprocess,sys,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-structural-discovery-r158'
spec=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'f924666e665acf42181fd933188435181d28e3140bea26656008a841456a83e8','MANIFEST.json':'5581864c82fd67fdf8c0030fb0b1a4b3b9bc1d675e17763404f83f68d1170f71','REPORT.md':'3ef52df997bd5264d022a509f8e51368cacd12ff8cc27ca855da046a6b339597'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 now=datetime.datetime.now(datetime.timezone.utc).isoformat();base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'] and len(read(B/'tasks.json')['tasks'])==534
 before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current sealed root excludes root-directory mode.'})
 st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and st['workState']=='result_available' and not st['hasPendingChildRuns'] and not st['hasPendingQuestion'];assert all(v in st['summary'] and sha(ROOT/n)==v for n,v in ANCHORS.items())
 m=read(ROOT/'MANIFEST.json');assert len(m['files'])==86 and len(m['directories'])==20;assert {n for n,e in before.items() if e['kind']=='file'}==set(m['files'])|set(ANCHORS) and {n for n,e in before.items() if e['kind']=='directory'}==set(m['directories'])
 for n,e in m['files'].items():assert (ROOT/n).stat().st_size==e['size'] and sha(ROOT/n)==e['sha256']
 tp=P/'sources/preprints-tree.json';tm=read(ROOT/'private/tree-selection.json')['incoming'];assert sha(tp)==tm['sha256']=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']};source=read(ROOT/'private/source-identities.json')+read(ROOT/'private/source-identities-addendum.json');assert len(source)==30
 for e in source:
  q=ROOT/e['selected_copy'];data=q.read_bytes();node=entries[e['canonical_path']];assert len(data)==e['size']==node['size'] and sha(q)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob_sha1']==node['sha'];assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['canonical_path']
 assert read(ROOT/'private/source-recheck.json')['count']==30
 initial=read(ROOT/'private/primary-identities02.json')+read(ROOT/'private/primary-identities03.json');failed=[e for e in initial if 'sha256' not in e];acquired=[e for e in initial if 'sha256' in e]+[dict(read(ROOT/'private/primary-identities04.json'),name='ekps00')];assert len(failed)==2 and len(acquired)==4
 for e in acquired:
  q=ROOT/'private/primary'/(e['name']+'.pdf');t=q.with_suffix('.txt');assert q.stat().st_size==e['size'] and sha(q)==e['sha256'] and t.stat().st_size==e['extract_size'] and sha(t)==e['extract_sha256']
 render=ROOT/'private/render/pp10-p15.png';assert render.read_bytes().startswith(b'\x89PNG\r\n\x1a\n')
 originals=read(ROOT/'private/incoming-original-identities.json')['originals'];selected=read(ROOT/'private/selected-original-membership.json');assert len(originals)==11 and len(selected)==12;stable=[]
 for i,e in enumerate(originals,1):
  p=P/e['incoming_original'];s=next(s for s in selected if s.get('original_number')==i);q=ROOT/s['selected_copy'];assert p.stat().st_size==q.stat().st_size==e['size']==s['size'] and sha(p)==sha(q)==e['sha256']==s['sha256'];stable.append({'path':e['incoming_original'],'bytes':e['size'],'sha256':e['sha256']})
 e=selected[-1];q=ROOT/e['selected_copy'];assert q.stat().st_size==e['size'] and sha(q)==e['sha256'] and q.read_bytes() in (P/e['source']).read_bytes()
 ctl=read(ROOT/'receipts/copied-controls.json');fixture=ROOT/'private/copied-controls';assert len(ctl['cases'])==8 and all(e['accepted']==e['expected_accept'] and e['nonmutation'] for e in ctl['cases']);assert all(sha(fixture/n)==v for n,v in ctl['anchors'].items()) and len(read(fixture/'MANIFEST.json')['files'])==3
 for a,b in [('notes/02-integrated-reduction-and-ending.md','math.md'),('code/finite_partitions.py','finite.py'),('receipts/finite-partitions.json','finite.json')]:assert (ROOT/a).read_bytes()==(fixture/b).read_bytes()
 cases=[]
 with tempfile.TemporaryDirectory(prefix='structural158-copy-',dir=O) as tmp:
  copy=Path(tmp)/'packet';shutil.copytree(ROOT,copy);args=[str(copy),*ANCHORS.values()]
  def check(label,want,custom=None):
   state=snap(copy);r=subprocess.run([sys.executable,'-I','-B',str(copy/'code/verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30);assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state;cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
  check('baseline_full_packet',True);q=copy/'notes/01-prefreeze-calculations.md';data=q.read_bytes();q.write_bytes(data+b'\nCONTROL\n');check('changed_payload',False);q.unlink();check('missing_payload',False);q.write_bytes(data);q=copy/'private/.extra';q.write_text('extra');check('hidden_extra',False);q.unlink();q=copy/'private/.empty';q.mkdir();check('empty_extra_directory',False);q.rmdir();wrong=args.copy();wrong[2]='0'*64;check('wrong_manifest_anchor',False,wrong);q=copy/'REPORT.md';data=q.read_bytes();q.write_bytes(data+b'\nCONTROL\n');check('changed_REPORT',False);q.write_bytes(data);check('restored',True);assert snap(copy)==before
  sandbox=Path(tmp)/'finite';sandbox.mkdir();(sandbox/'receipts').mkdir();original=(ROOT/'code/finite_partitions.py').read_text();patched,count=re.subn(r"^R=Path\('[^']+'\)$",'R=Path('+repr(str(sandbox))+')',original,count=1,flags=re.M);assert count==1;program=sandbox/'finite_partitions.py';program.write_text(patched);r=subprocess.run([sys.executable,'-I','-B',str(program)],capture_output=True,text=True,timeout=45,cwd=P);assert r.returncode==0,r.stderr;result=read(sandbox/'receipts/finite-partitions.json');assert result==read(ROOT/'receipts/finite-partitions.json');finite={'only_fixed_output_root_relocated':True,'original_sha256':sha(ROOT/'code/finite_partitions.py'),'relocated_program_sha256':sha(program),'matches_sealed_receipt':True,'two_input_rows':len(result['two_input_rows']),'four_leaf_markings':len(result['four_leaf_all_markings']),'distinct_finite_pairs':len(result['four_leaf_histogram']),'symbolic_stage_descriptors':len(result['first_64_core_stages'])}
 assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':6,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Artifact checks only;manifest binds exact files/directories/bytes,not modes;parent snapshots exclude root-directory mode.'})
 dump('finite-replay.json',dict(finite,limits='Exact rational finite identities only,no infinite tree instantiated/asymptotic theorem/independent grade.'))
 dump('input-authentication.json',{'source_blobs':30,'source_bytes':sum(e['size'] for e in source),'primary_pdf_text_pairs':4,'failed_primary_acquisitions':failed,'render_members':1,'stable_whole_original_copies':11,'selected_acceptance_excerpt':1,'selected_fixture_members':3,'limits':'Local byte/path/member authentication only,no fresh protected semantic/PDF/visual/transitive reading.EKPS extract remains glyph-garbled/not a mathematical premise.'})
 dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'payload_files':86,'whole_root_files':89,'subdirectories':20,'source_blobs':30,'primary_pdf_text_pairs':4,'failed_primary_acquisitions':2,'render_members':1,'stable_named_originals':stable,'selected_acceptance_excerpt':1,'artifact_cases':8,'negative_cases':6,'finite_diagnostic':finite,'whole_actual_root_unchanged':True,'limits':'Artifact and finite observations only;no independent mathematical or contribution grade.'})
 print(json.dumps({'payload':86,'files':89,'subdirs':20,'source_blobs':30,'pdf_text_pairs':4,'renders':1,'stable_originals':11,'artifact_cases':8,'finite':finite}))
if __name__=='__main__':main()
