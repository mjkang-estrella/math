#!/usr/bin/env python3
"""Arithmetic125 local archive authentication and redirected finite diagnostic."""
import datetime,hashlib,importlib.util,json,re,shutil,subprocess,sys,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-arithmetic-discovery-r125'
spec=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'ba04729b9df638ddb15b3c8342dc9186fd7ff806a9f8dbab5b67c42b19f32189','MANIFEST.json':'f92a32cf90d47c9bab6409df01cf1f557e4c01797783e4300ceb504ac561b2be','REPORT.md':'b630ebcf950388aefb00abe8bbc8b92a8528860a0b481dc02da8e37791805ffa'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 now=datetime.datetime.now(datetime.timezone.utc).isoformat();base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'] and len(read(B/'tasks.json')['tasks'])==538
 before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Observed sealed root excludes root-directory mode.'})
 st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and st['workState']=='result_available' and not st['hasPendingChildRuns'] and not st['hasPendingQuestion'];assert all(v in st['summary'] and sha(ROOT/n)==v for n,v in ANCHORS.items())
 m=read(ROOT/'MANIFEST.json');assert len(m['files'])==91 and len(m['directories'])==9;assert {n for n,e in before.items() if e['kind']=='file'}==set(m['files'])|set(ANCHORS) and {n for n,e in before.items() if e['kind']=='directory'}==set(m['directories'])
 for n,e in m['files'].items():assert (ROOT/n).stat().st_size==e['size'] and sha(ROOT/n)==e['sha256']
 incoming=read(ROOT/'private/incoming-identities.json');tree=read(P/'sources/preprints-tree.json');assert len(tree['tree'])==13223 and not tree['truncated'] and sha(P/'sources/preprints-tree.json')==incoming['complete_tree']['sha256']=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';entries={e['path']:e for e in tree['tree']};source=read(ROOT/'private/source-identities.json');assert len(source)==15
 for e in source:
  q=ROOT/e['copy'];data=q.read_bytes();node=entries[e['canonical']];assert len(data)==e['size']==node['size'] and sha(q)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']==node['sha'];assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['canonical']
 pa=read(ROOT/'private/primary/identities.json');acquired=[e for e in pa if 'sha256' in e];failed=[e for e in pa if 'failure' in e];assert len(acquired)==3 and len(failed)==3
 for e in acquired:
  q=ROOT/'private/primary'/(e['name']+'.pdf');assert q.stat().st_size==e['size'] and sha(q)==e['sha256'] and sha(q.with_suffix('.txt'))==e['text_sha256']
 renders=read(ROOT/'private/primary/render-identities.json');assert len(renders)==26
 for e in renders:
  q=ROOT/e['path'];assert q.stat().st_size==e['size'] and sha(q)==e['sha256']
 originals=incoming['full_and_selected'];assert len(originals)==12;stable=[];excerpts=[]
 for e in originals:
  p=P/e['original'];q=ROOT/e['selected_copy'];assert q.stat().st_size==e['selected_size'] and sha(q)==e['selected_sha256']
  if e['kind'].startswith('whole original'):
   assert p.stat().st_size==e['size'] and sha(p)==e['sha256'] and q.read_bytes()==p.read_bytes();stable.append({'path':e['original'],'bytes':e['size'],'sha256':e['sha256']})
  else:
   if 'lines' in e:a,z=e['lines'];assert q.read_bytes()==b''.join(p.read_bytes().splitlines(keepends=True)[a-1:z])
   else:assert q.read_bytes() in p.read_bytes()
   excerpts.append(e)
 assert len(stable)==7 and len(excerpts)==5
 ctl=read(ROOT/'private/control-results.json');fixture=ROOT/'private/copied-controls';assert len(ctl['cases'])==7 and all(e['accepted']==e['expected'] and e['read_only_snapshot_equal'] for e in ctl['cases']);assert all(sha(fixture/n)==ctl['detached_fixture_anchors'][k] for n,k in [('FINAL.md','FINAL'),('MANIFEST.json','MANIFEST'),('REPORT.md','REPORT')]) and len(read(fixture/'MANIFEST.json')['files'])==3
 for e in ctl['membership']:assert (ROOT/e['original']).read_bytes()==(fixture/e['selected_copy']).read_bytes()
 assert (ROOT/'verify.py').read_bytes()==(fixture/'verify.py').read_bytes()
 cases=[]
 with tempfile.TemporaryDirectory(prefix='arithmetic125-copy-',dir=O) as tmp:
  copy=Path(tmp)/'packet';shutil.copytree(ROOT,copy);args=[str(copy),*ANCHORS.values()]
  def check(label,want,custom=None):
   state=snap(copy);r=subprocess.run([sys.executable,'-I','-B',str(copy/'verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30);assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state;cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
  check('baseline_full_packet',True);q=copy/'notes/feasibility.md';data=q.read_bytes();q.write_bytes(data+b'\nCONTROL\n');check('changed_payload',False);q.unlink();check('missing_payload',False);q.write_bytes(data);q=copy/'private/.extra';q.write_text('extra');check('hidden_extra',False);q.unlink();q=copy/'private/.empty';q.mkdir();check('empty_extra_directory',False);q.rmdir();wrong=args.copy();wrong[2]='0'*64;check('wrong_manifest_anchor',False,wrong);check('restored',True);assert snap(copy)==before
  sandbox=Path(tmp)/'finite';sandbox.mkdir();out=sandbox/'diagnostic.json';original=(ROOT/'scratch/diagnostic.py').read_text();patched,count=re.subn(r'^OUT=Path\([^\n]+\)$','OUT=Path('+repr(str(out))+')',original,count=1,flags=re.M);assert count==1;program=sandbox/'diagnostic.py';program.write_text(patched);r=subprocess.run([sys.executable,'-I','-B',str(program)],capture_output=True,text=True,timeout=45,cwd=P);assert r.returncode==0,r.stderr;result=read(out);assert result==read(ROOT/'notes/diagnostic.json') and len(result['records'])==10 and result['associativity_basis_triples']==3132;finite={'only_OUT_destination_relocated':True,'original_sha256':sha(ROOT/'scratch/diagnostic.py'),'relocated_program_sha256':sha(program),'matches_sealed_receipt':True,'result':result}
 assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':5,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Artifact checks only;manifest binds files/directories/bytes,not modes.Parent snapshots exclude root-directory mode.'})
 dump('finite-replay.json',dict(finite,limits='Ten bounded exact records,3132basis-triple identities and one6561element enumeration only;no universal proof or mathematical/contribution grade.'))
 dump('input-authentication.json',{'source_blobs':15,'source_selection_complete':False,'source_bytes':sum(e['size'] for e in source),'primary_pdf_text_pairs':3,'failed_download_attempts':failed,'render_members':26,'stable_whole_original_copies':7,'selected_excerpts':5,'selected_fixture_members':2,'copied_fixture_verifier':1,'limits':'Local byte/path/member authentication only.No fresh protected semantic/PDF/visual/transitive proof reading.Friedl-Ronyai extract is not OCR;2024web-only reads have no fabricated local original.'})
 dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'payload_files':91,'whole_root_files':94,'subdirectories':9,'source_blobs':15,'primary_pdf_text_pairs':3,'render_members':26,'stable_named_originals':stable,'selected_original_excerpts':excerpts,'artifact_cases':7,'negative_cases':5,'finite_records':10,'finite_basis_triples':3132,'whole_actual_root_unchanged':True,'limits':'Artifact and bounded finite observations only;no independent mathematical/contribution grade.'})
 print(json.dumps({'payload':91,'files':94,'subdirs':9,'source_blobs':15,'pdf_text_pairs':3,'renders':26,'stable_originals':7,'excerpts':5,'artifact_cases':7,'finite_records':10,'basis_triples':3132}))
if __name__=='__main__':main()
