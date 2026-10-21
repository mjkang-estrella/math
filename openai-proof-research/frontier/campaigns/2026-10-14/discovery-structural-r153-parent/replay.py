#!/usr/bin/env python3
"""Completed structural153 artifact archive and bounded return-diagnostic replay."""
import datetime,hashlib,importlib.util,json,shutil,subprocess,sys,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-structural-discovery-r153'
spec=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'81a0ff9499f48f13c1d94c1f8a5692c274ca7a7cd21c980ebad13c78c9b50c28','MANIFEST.json':'5dbe64003f5861065e0c983eeed81a798f77e17b2ac2ee2aab7ca39bbdfb6154','REPORT.md':'0dcb587f0f109535bf9ad63a9aa0ae87f7149e3876504de87ffe9d8b16188bda'}
PROTECTED={'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json':'6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9','frontier/iterations/i31-nonconical-no-mcm.md':'d606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=P);assert len(read(B/'tasks.json')['tasks'])==517
 dump('integration-baseline.json',{'observed_utc':now,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip(),'initial_index_empty':True,'task_count':517,'task_index':514,'protected_unrelated_sha256':PROTECTED})
 before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Completed current root,snapshot excludes root-directory mode;not historical whole-project/OS certificate.'})
 st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and not st['hasPendingChildRuns'] and all(v in st['summary'] for v in ANCHORS.values())
 assert all(sha(ROOT/n)==v for n,v in ANCHORS.items());m=read(ROOT/'MANIFEST.json');assert m['schema']=='r153-exact-v1' and len(m['files'])==87 and len(m['directories'])==21
 rows={e['path']:e for e in m['files']};assert len(rows)==87 and {n for n,e in before.items() if e['kind']=='file'}==set(rows)|set(ANCHORS)
 assert {n for n,e in before.items() if e['kind']=='directory'}==set(m['directories'])-{'.'}
 for n,e in rows.items():assert (ROOT/n).stat().st_size==e['bytes'] and sha(ROOT/n)==e['sha256']
 tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']}
 source=read(ROOT/'private/sources/authentication.json');assert len(source)==23
 prefixes=['preprints/An-exponential-state-lower-bound-for-two-way-nondeterministic-complementation-September-25-2026/','preprints/An-exponential-two-way-deterministic-state-lower-bound-for-one-way-liveness-September-25-2026/']
 assert {e['canonical'] for e in source}=={p for p,e in entries.items() if e['type']=='blob' and any(p.startswith(q) for q in prefixes) and not p.endswith('.pdf')}
 for e in source:
  data=(ROOT/e['copy']).read_bytes();node=entries[e['canonical']];assert len(data)==e['bytes']==node['size'] and sha(ROOT/e['copy'])==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob_sha1']==node['sha'];assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['canonical']
 primary=read(ROOT/'private/primary/receipts.json');assert len(primary)==3
 for e in primary:
  if 'failure' in e:assert '403' in e['failure'];continue
  p=ROOT/'private/primary'/ (e['label']+'.pdf');q=p.with_suffix('.txt');assert p.stat().st_size==e['bytes'] and sha(p)==e['sha256'] and sha(q)==e['text_sha256']
 attempts=read(ROOT/'private/primary/dwork-stockmeyer-attempts.json');success=[e for e in attempts if 'sha256' in e];assert len(success)==1 and len(attempts)==3
 e=success[0];p=ROOT/'private/primary/dwork-stockmeyer.ps';assert p.stat().st_size==e['bytes'] and sha(p)==e['sha256'] and sha(p.with_suffix('.pdf'))==e['pdf_sha256'] and sha(p.with_suffix('.txt'))==e['text_sha256']
 e=read(ROOT/'private/primary/leighton-rivest-receipt.json');p=ROOT/'private/primary/leighton-rivest.pdf';assert p.stat().st_size==e['bytes'] and sha(p)==e['sha256'] and sha(p.with_suffix('.txt'))==e['text_sha256']
 membership=read(ROOT/'private/selected-copy-membership.json')['members'];assert len(membership)==13;stable=[];mutable=[]
 for e in membership:
  copy=ROOT/e['copy'];assert copy.stat().st_size==e['bytes'] and sha(copy)==e['sha256']
  p=P/e['original']
  if e['original']=='frontier/NEW-TEN-2026-10-14.md':mutable.append(e|{'current_sha256':sha(p),'matches_current':sha(p)==e['sha256'],'limit':'Retained whole historical capture,not post-append stability input.'})
  else:assert p.read_bytes()==copy.read_bytes();stable.append({'path':e['original'],'sha256':e['sha256'],'bytes':e['bytes']})
 assert len(stable)==12 and len(mutable)==1
 required=read(ROOT/'private/required/incoming-originals.json');history=read(ROOT/'private/history/incoming-selected.json');last=read(ROOT/'private/history/r117-direct-original.json');assert len(required)==8 and len(history)==4
 indexed={e['copy']:e for e in membership}
 for e in required:assert indexed[e['copy']]=={'copy':e['copy'],'original':e['path'],'bytes':e['bytes'],'sha256':e['sha256']}
 for e in history:assert indexed[e['copy']]==e
 assert indexed[last['selected_copy']]=={'copy':last['selected_copy'],'original':last['path'],'bytes':last['bytes'],'sha256':last['sha256']}
 ctl=read(ROOT/'private/controls/results.json');fixture=ROOT/'private/controls/selection';assert len(ctl['checks'])==8 and all(e['read_only_snapshot_equal'] and e['accepted']==(e['label'] in ['baseline','restored']) for e in ctl['checks'])
 assert all(sha(fixture/n)==v for n,v in ctl['anchors'].items())
 for e in ctl['selection']:assert (ROOT/e['source']).read_bytes()==(ROOT/e['selected_copy']).read_bytes() and sha(ROOT/e['source'])==e['sha256']
 cases=[]
 with tempfile.TemporaryDirectory(prefix='structural153-copy-',dir=O) as temp:
  copy=Path(temp)/'packet';shutil.copytree(ROOT,copy);args=[str(copy),'--final',ANCHORS['FINAL.md'],'--manifest',ANCHORS['MANIFEST.json'],'--report',ANCHORS['REPORT.md']]
  def check(label,want,custom=None):
   state=snap(copy);r=subprocess.run([sys.executable,'-I','-B',str(copy/'code/verify_packet.py'),*(custom or args)],capture_output=True,text=True,timeout=30);assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state;cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
  check('baseline_full_packet',True);p=copy/'notes/01-prefreeze-calculations.md';data=p.read_bytes();p.write_bytes(data+b'\nCONTROL\n');check('modified_payload',False);p.unlink();check('missing_payload',False);p.write_bytes(data)
  p=copy/'private/.extra';p.write_text('extra');check('hidden_extra',False);p.unlink();p=copy/'private/.empty';p.mkdir();check('empty_extra_directory',False);p.rmdir();wrong=args.copy();wrong[4]='0'*64;check('wrong_manifest_anchor',False,wrong)
  p=copy/'REPORT.md';data=p.read_bytes();p.write_bytes(data+b'x');check('changed_report_envelope',False);p.write_bytes(data);check('restored',True);assert snap(copy)==before
  r=subprocess.run([sys.executable,'-I','-B',str(copy/'code/return_diagnostic.py')],cwd=temp,capture_output=True,text=True,timeout=30);assert r.returncode==0,(r.stdout,r.stderr);assert json.loads(r.stdout)==read(ROOT/'private/return-diagnostic.json');assert snap(copy)==before
 assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in PROTECTED.items())
 dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':6,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Artifact evidence only;verifier does not authenticate modes.'})
 dump('finite-replay.json',{'script_sha256':sha(ROOT/'code/return_diagnostic.py'),'output_sha256':sha(ROOT/'private/return-diagnostic.json'),'output_exact_json_match':True,'result':json.loads(r.stdout),'whole_actual_root_unchanged':True,'scope':'Exact bounded rational diagnostic,not a general mathematical or contribution gate.'})
 dump('input-authentication.json',{'source_blobs':23,'primary_incoming_objects':4,'primary_received_pdfs':3,'primary_ps':1,'converted_primary_pdf':1,'byte_bound_text_derivatives':4,'byte_bound_renders':12,'stable_whole_original_copies':12,'historical_mutable_whole_copies':mutable,'selected_fixture_members':2,'limits':'Local bytes and selected membership only;no fresh network,protected-body semantic reading,extraction or PDF visual attestation.'})
 dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'payload_files':87,'whole_root_files':90,'subdirectories':20,'source_blobs':23,'primary_incoming_objects':4,'stable_named_originals':stable,'historical_mutable_whole_copies':mutable,'artifact_cases':8,'negative_cases':6,'whole_actual_root_unchanged':True,'limits':'Byte archive and bounded rational diagnostics,not mathematical/contribution grades;parent snapshots exclude root-directory mode.'})
 print(json.dumps({'files':90,'payload':87,'subdirectories':20,'source_blobs':23,'primary_objects':4,'stable_whole_copies':12,'mutable_whole_capture':1,'artifact_cases':8,'finite_diagnostic_match':True}))
if __name__=='__main__':main()
