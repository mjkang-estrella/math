#!/usr/bin/env python3
"""Arithmetic123 artifact authentication; no fresh protected semantic reading."""
import datetime,hashlib,importlib.util,json,shutil,subprocess,sys,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-arithmetic-discovery-r123'
spec=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'e5b9c97f1721575e2aea5033357c3dd04db96a378215c39ff95fc62ab26f7c7f','MANIFEST.json':'0cae42db378fcffdc45a6c5b9b641860c8fc4be72e0537f0506049d18116a6f3','REPORT.md':'929c0fb76c02a266edcb4114194397d8935f7e356302d09c1d3a4e23187abe46'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 now=datetime.datetime.now(datetime.timezone.utc).isoformat();base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'] and len(read(B/'tasks.json')['tasks'])==532
 before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current sealed root,excluding root-directory mode.'})
 st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and st['workState']=='result_available' and not st['hasPendingChildRuns'] and not st['hasPendingQuestion']
 assert all(v in st['summary'] and sha(ROOT/n)==v for n,v in ANCHORS.items())
 m=read(ROOT/'MANIFEST.json');assert len(m['files'])==78 and len(m['directories'])==15
 assert {n for n,e in before.items() if e['kind']=='file'}==set(m['files'])|set(ANCHORS) and {n for n,e in before.items() if e['kind']=='directory'}==set(m['directories'])
 for n,e in m['files'].items():assert (ROOT/n).stat().st_size==e['size'] and sha(ROOT/n)==e['sha256']
 tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']};source=read(ROOT/'private/source-identities.json');assert len(source)==26
 prefixes=['preprints/The-Margulis-Platonov-conjecture-over-global-function-fields-October-5-2026/','preprints/The-Margulis-Platonov-conjecture-over-number-fields-September-23-2026/']
 assert {e['canonical_path'] for e in source}<={p for p,e in entries.items() if e['type']=='blob' and any(p.startswith(x) for x in prefixes) and p.endswith(('.tex','.bib'))}
 omitted={p for p,e in entries.items() if e['type']=='blob' and any(p.startswith(x) for x in prefixes) and p.endswith(('.tex','.bib'))}-{e['canonical_path'] for e in source}
 assert omitted=={prefixes[0]+'build/paper/figures/even-degree-norms.tex'}
 for e in source:
  q=ROOT/e['selected_copy'];data=q.read_bytes();node=entries[e['canonical_path']]
  assert len(data)==e['size']==node['size'] and sha(q)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']==node['sha']
  assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['canonical_path']
 primary=read(ROOT/'private/primary/identities.json');assert len(primary)==4
 for e in primary:
  q=ROOT/'private/primary'/(e['name']+'.pdf');t=q.with_suffix('.txt');assert q.stat().st_size==e['size'] and sha(q)==e['sha256'] and sha(t)==e['text_sha256']
 renders=read(ROOT/'private/primary/render-identities.json');assert len(renders)==2
 for e in renders:
  q=ROOT/'private/primary'/e['file'];assert q.stat().st_size==e['size'] and sha(q)==e['sha256']
 originals=read(ROOT/'private/incoming-identities.json');assert len(originals)==13;stable=[];excerpts=[]
 for e in originals:
  p=P/e['original_path'];q=ROOT/e['selected_copy'];assert q.stat().st_size==e['selected_size'] and sha(q)==e['selected_sha256']
  if e.get('selection')=='whole':
   assert p.stat().st_size==e['original_size_at_late_capture'] and sha(p)==e['original_full_sha256'] and p.read_bytes()==q.read_bytes();stable.append({'path':e['original_path'],'bytes':p.stat().st_size,'sha256':sha(p)})
  else:
   a,z=e['selected_lines'];assert e['original_full_sha256'] is None and q.read_bytes()==b''.join(p.read_bytes().splitlines(keepends=True)[a-1:z]);excerpts.append(e)
 assert len(stable)==8 and len(excerpts)==5
 ctl=read(ROOT/'private/controls/results.json');fixture=ROOT/'private/controls/selected';assert len(ctl['cases'])==7 and all(e['actual_accept']==e['expected_accept'] and e['read_only_snapshot_unchanged'] for e in ctl['cases'])
 assert all(sha(fixture/n)==v for n,v in ctl['fixture_anchors'].items()) and len(read(fixture/'MANIFEST.json')['files'])==2
 intro=next(e for e in source if e['canonical_path'].endswith('build/sections/introduction.tex'))
 assert (fixture/'payload/feasibility.md').read_bytes()==(ROOT/'notes/feasibility.md').read_bytes() and (fixture/'payload/introduction.tex').read_bytes()==(ROOT/intro['selected_copy']).read_bytes()
 cases=[]
 with tempfile.TemporaryDirectory(prefix='arithmetic123-copy-',dir=O) as tmp:
  copy=Path(tmp)/'packet';shutil.copytree(ROOT,copy);args=[str(copy),'--final-sha256',ANCHORS['FINAL.md'],'--manifest-sha256',ANCHORS['MANIFEST.json'],'--report-sha256',ANCHORS['REPORT.md']]
  def check(label,want,custom=None):
   state=snap(copy);r=subprocess.run([sys.executable,'-I','-B',str(copy/'verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30)
   assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state
   cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
  check('baseline_full_packet',True);q=copy/'notes/feasibility.md';data=q.read_bytes();q.write_bytes(data+b'\nCONTROL\n');check('changed_payload',False);q.unlink();check('missing_payload',False);q.write_bytes(data)
  q=copy/'private/.extra';q.write_text('extra');check('hidden_extra',False);q.unlink();q=copy/'private/.empty';q.mkdir();check('empty_extra_directory',False);q.rmdir();wrong=args.copy();wrong[4]='0'*64;check('wrong_manifest_anchor',False,wrong);check('restored',True);assert snap(copy)==before
 assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':5,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Artifact checks only;manifest binds exact files/directories/bytes,not modes;parent snapshots exclude root-directory mode.'})
 dump('input-authentication.json',{'source_selection_complete':False,'unselected_canonical_text':sorted(omitted),'source_blobs':26,'source_bytes':sum(e['size'] for e in source),'primary_pdf_text_pairs':4,'render_members':2,'stable_whole_original_copies':8,'selected_excerpts':5,'selected_fixture_members':2,'limits':'Local byte/path/member authentication only;no fresh protected source/primary/history semantic reading,PDF text extraction or visual/transitive coverage.'})
 dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'payload_files':78,'whole_root_files':81,'subdirectories':15,'source_blobs':26,'primary_pdf_text_pairs':4,'render_members':2,'stable_named_originals':stable,'selected_original_excerpts':excerpts,'artifact_cases':7,'negative_cases':5,'whole_actual_root_unchanged':True,'limits':'Artifact integrity only,no independent mathematical or contribution grade.No finite/numerical/formal suite exists for this no-nominee round.'})
 print(json.dumps({'payload':78,'files':81,'subdirs':15,'source_blobs':26,'pdf_text_pairs':4,'renders':2,'stable_originals':8,'excerpts':5,'artifact_cases':7}))
if __name__=='__main__':main()
