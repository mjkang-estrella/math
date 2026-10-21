#!/usr/bin/env python3
"""Arithmetic124 archive byte authentication and disposable F2 diagnostic replay."""
import datetime,hashlib,importlib.util,json,re,shutil,subprocess,sys,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-arithmetic-discovery-r124'
spec=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'609c441b67a97dbb89cf6eb11365cb00ef61495c90c7e952697ae7f57e01ae86','MANIFEST.json':'d331f4c8fee1f08403b4cc9ac691d13d3be4e1b70bfe532786a0569d29e789e6','REPORT.md':'7d925fb080b8d6b374893c92e7df44d2527c2b7e177ebae4545049b17e9f60ac'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 now=datetime.datetime.now(datetime.timezone.utc).isoformat();base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'] and len(read(B/'tasks.json')['tasks'])==535
 before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current sealed root excludes root-directory mode.'})
 st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and st['workState']=='result_available' and not st['hasPendingChildRuns'] and not st['hasPendingQuestion'];assert all(v in st['summary'] and sha(ROOT/n)==v for n,v in ANCHORS.items())
 m=read(ROOT/'MANIFEST.json');assert len(m['files'])==66 and len(m['directories'])==9;assert {n for n,e in before.items() if e['kind']=='file'}==set(m['files'])|set(ANCHORS) and {n for n,e in before.items() if e['kind']=='directory'}==set(m['directories'])
 for n,e in m['files'].items():assert (ROOT/n).stat().st_size==e['size'] and sha(ROOT/n)==e['sha256']
 tp=P/'sources/preprints-tree.json';tm=read(ROOT/'private/tree-identity.json');assert sha(tp)==tm['sha256']=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']};source=read(ROOT/'private/source-identities.json');assert len(source)==6
 for e in source:
  q=ROOT/e['selected_copy'];data=q.read_bytes();node=entries[e['canonical_path']];assert len(data)==e['size']==node['size'] and sha(q)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']==node['sha'];assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['canonical_path']
 pa=read(ROOT/'private/primary/identities.json');acquired=[e for e in pa if 'sha256' in e];assert len(acquired)==3
 for e in acquired:
  q=ROOT/'private/primary'/(e['name']+'.pdf');t=q.with_suffix('.txt');assert q.stat().st_size==e['size'] and sha(q)==e['sha256'] and sha(t)==e['text_sha256']
 renders=read(ROOT/'private/primary/render-identities.json');assert len(renders)==15
 for e in renders:
  q=ROOT/e['path'];assert q.stat().st_size==e['size'] and sha(q)==e['sha256']
 originals=read(ROOT/'private/incoming-identities.json');assert len(originals)==10;stable=[];excerpts=[]
 for e in originals:
  p=P/e['original_path'];q=ROOT/e['selected_copy'];assert q.stat().st_size==e['selected_size'] and sha(q)==e['selected_sha256']
  if isinstance(e['selection'],str):
   assert p.stat().st_size==e['original_size'] and sha(p)==e['original_sha256'] and p.read_bytes()==q.read_bytes();stable.append({'path':e['original_path'],'bytes':e['original_size'],'sha256':e['original_sha256']})
  else:
   s=e['selection'];ls=s.get('lines');a,z=(min(ls),max(ls)) if ls else (s['first_line'],s['last_line']);assert q.read_bytes()==b''.join(p.read_bytes().splitlines(keepends=True)[a-1:z]);excerpts.append(e)
 assert len(stable)==7 and len(excerpts)==3
 ctl=read(ROOT/'private/copied-controls-results.json');fixture=ROOT/'private/copied-controls';assert len(ctl['tests'])==7 and all((e['returncode']==0)==e['expected_accept'] and e['read_only_snapshot_equal'] for e in ctl['tests']);assert all(sha(fixture/n)==v for n,v in ctl['independent_detached_anchors'].items()) and len(read(fixture/'MANIFEST.json')['files'])==2
 for a,b in [('private/pinned/04-norm-tori.tex','selected/04-norm-tori.tex'),('notes/integrated-norm-reduction.md','selected/integrated-norm-reduction.md')]:assert (ROOT/a).read_bytes()==(fixture/b).read_bytes()
 cases=[]
 with tempfile.TemporaryDirectory(prefix='arithmetic124-copy-',dir=O) as tmp:
  copy=Path(tmp)/'packet';shutil.copytree(ROOT,copy);args=[str(copy),'--final-sha256',ANCHORS['FINAL.md'],'--manifest-sha256',ANCHORS['MANIFEST.json'],'--report-sha256',ANCHORS['REPORT.md']]
  def check(label,want,custom=None):
   state=snap(copy);r=subprocess.run([sys.executable,'-I','-B',str(copy/'verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30);assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state;cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
  check('baseline_full_packet',True);q=copy/'notes/feasibility.md';data=q.read_bytes();q.write_bytes(data+b'\nCONTROL\n');check('changed_payload',False);q.unlink();check('missing_payload',False);q.write_bytes(data);q=copy/'private/.extra';q.write_text('extra');check('hidden_extra',False);q.unlink();q=copy/'private/.empty';q.mkdir();check('empty_extra_directory',False);q.rmdir();wrong=args.copy();wrong[4]='0'*64;check('wrong_manifest_anchor',False,wrong);check('restored',True);assert snap(copy)==before
  sandbox=Path(tmp)/'finite';sandbox.mkdir();(sandbox/'notes').mkdir();original=(ROOT/'tools/cyclic_diagnostic.py').read_text();patched,count=re.subn(r"^R=Path\('[^']+'\)$",'R=Path('+repr(str(sandbox))+')',original,count=1,flags=re.M);assert count==1;program=sandbox/'cyclic_diagnostic.py';program.write_text(patched);r=subprocess.run([sys.executable,'-I','-B',str(program)],capture_output=True,text=True,timeout=45,cwd=P);assert r.returncode==0,r.stderr;result=read(sandbox/'notes/finite-diagnostic.json');assert result==read(ROOT/'notes/finite-diagnostic.json') and len(result)==8;finite={'only_fixed_output_root_relocated':True,'original_sha256':sha(ROOT/'tools/cyclic_diagnostic.py'),'relocated_program_sha256':sha(program),'matches_sealed_receipt':True,'groups':result}
 assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':5,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Artifact checks only;manifest binds exact files/directories/bytes,not modes;parent snapshots exclude root-directory mode.'})
 dump('finite-replay.json',dict(finite,limits='Exact normalized F2 bar-complex observations for eight groups only,no classification/arithmetic realization/independent mathematical grade.'))
 dump('input-authentication.json',{'source_blobs':6,'source_selection_complete':False,'source_bytes':sum(e['size'] for e in source),'primary_pdf_text_pairs':3,'render_members':15,'stable_whole_original_copies':7,'selected_excerpts':3,'selected_fixture_members':2,'limits':'Local byte/path/member authentication only.No fresh protected semantic/PDF/visual/transitive reading.Sansuc is a whole scanned volume,not article OCR;Hurlimann and EuDML access limits remain disclosed.'})
 dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'payload_files':66,'whole_root_files':69,'subdirectories':9,'source_blobs':6,'primary_pdf_text_pairs':3,'render_members':15,'stable_named_originals':stable,'selected_original_excerpts':excerpts,'artifact_cases':7,'negative_cases':5,'finite_groups':8,'Q8_H2_dimension':2,'Q8_cyclic_kernel_dimension':2,'whole_actual_root_unchanged':True,'limits':'Artifact and finite observations only,no independent mathematical or contribution grade.No decomposition groups or arithmetic counterexample constructed.'})
 print(json.dumps({'payload':66,'files':69,'subdirs':9,'source_blobs':6,'pdf_text_pairs':3,'renders':15,'stable_originals':7,'excerpts':3,'artifact_cases':7,'finite_groups':8,'Q8_cyclic_kernel_dimension':2}))
if __name__=='__main__':main()
