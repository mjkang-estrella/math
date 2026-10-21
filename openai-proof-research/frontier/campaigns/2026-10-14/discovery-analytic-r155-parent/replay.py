#!/usr/bin/env python3
"""Analytic155 completed archive authentication; artifact checks only."""
import datetime,gzip,hashlib,importlib.util,json,shutil,subprocess,sys,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-analytic-discovery-r155'
spec=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'65730691f92c7cb67f2aade6c8aa22f05736d07c1084652780bfdaa075286073','MANIFEST.json':'c94ac70c51492cbcd56b30f082e10bbba4b9c1dd7e0267be0033f7db35c2b77f','REPORT.md':'1d4ad9be824e8d26864693b955d97e6f27ff693ffde0945749e33212a196e435'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 now=datetime.datetime.now(datetime.timezone.utc).isoformat();base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'] and len(read(B/'tasks.json')['tasks'])==542
 before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Snapshot excludes root-directory mode.'});st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and st['workState']=='result_available' and not st['hasPendingChildRuns'] and not st['hasPendingQuestion'];assert all(v in st['summary'] and sha(ROOT/n)==v for n,v in ANCHORS.items())
 m=read(ROOT/'MANIFEST.json');assert len(m['files'])==117;assert {n for n,e in before.items() if e['kind']=='file'}=={e['path'] for e in m['files']}|set(ANCHORS)
 for e in m['files']:assert (ROOT/e['path']).stat().st_size==e['size'] and sha(ROOT/e['path'])==e['sha256']
 tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']};source=read(ROOT/'private/source-auth.json');assert len(source)==30 and sum(e['size'] for e in source)==562471
 for e in source:
  q=ROOT/e['local'];data=q.read_bytes();node=entries[e['canonical_path']];assert len(data)==e['size']==node['size'] and sha(q)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']==node['sha'];assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['canonical_path']
 primary=read(ROOT/'private/primary/auth.json');assert len(primary)==3
 for e in primary:
  q=ROOT/'private/primary'/f"{e['tag']}.incoming";assert q.stat().st_size==e['incoming_size'] and sha(q)==e['incoming_sha256'] and len(e['members'])==1
  s=e['members'][0];p=ROOT/'private/primary'/s['selected_path'];assert p.stat().st_size==s['size'] and sha(p)==s['sha256'] and gzip.decompress(q.read_bytes())==p.read_bytes()
 additional=read(ROOT/'private/primary/additional-auth.json');assert len(additional)==9
 for e in additional:
  p=ROOT/'private/primary'/e.get('incoming',e.get('selected_local'));assert p.stat().st_size==e['size'] and sha(p)==e['sha256']
  if 'incoming' in e:assert p.read_bytes().startswith(b'%PDF')==e['actual_pdf']
 required=read(ROOT/'private/required-originals.json');assert len(required)==12;stable=[]
 for e in required:
  p=P/e['original'];q=ROOT/e['copy'];assert q.stat().st_size==e['size'] and sha(q)==e['sha256']
  if 'selection' in e:assert q.read_bytes() in p.read_bytes()
  else:assert p.stat().st_size==e['size'] and sha(p)==e['sha256'];stable.append({'path':e['original'],'bytes':e['size'],'sha256':e['sha256']})
 r91=read(ROOT/'private/history-r91-auth.json');p=P/r91['original'];q=ROOT/r91['selected_copy'];assert p.stat().st_size==q.stat().st_size==r91['size'] and sha(p)==sha(q)==r91['sha256'];stable.append({'path':r91['original'],'bytes':r91['size'],'sha256':r91['sha256']})
 hist=read(ROOT/'private/history-auth.json');p=P/hist['original_path'];q=ROOT/hist['selected_copy'];assert p.stat().st_size==hist['original_size'] and sha(p)==hist['original_sha256'] and q.stat().st_size==hist['selected_size'] and sha(q)==hist['selected_sha256'];a,b=hist['selection_lines'];assert b''.join(p.read_bytes().splitlines(keepends=True)[a-1:b])==q.read_bytes();stable.append({'path':hist['original_path'],'bytes':hist['original_size'],'sha256':hist['original_sha256']});assert len(stable)==13
 ctl=read(ROOT/'private/controls/controls-result.json');fixture=ROOT/'private/controls/selected-base';assert len(ctl['results'])==5 and ctl['originals_unchanged'];assert all(sha(fixture/n)==v for n,v in ctl['selected_copy_external_anchors'].items()) and len(read(fixture/'MANIFEST.json')['files'])==2
 for e in ctl['copied_original_members']:assert (ROOT/e['original_in_r155']).stat().st_size==e['size'] and sha(ROOT/e['original_in_r155'])==sha(fixture/e['selected_member'])==e['sha256']
 cases=[]
 with tempfile.TemporaryDirectory(prefix='analytic155-copy-',dir=O) as tmp:
  copy=Path(tmp)/'packet';shutil.copytree(ROOT,copy)
  # The sealed original is read-only. Permit deliberate perturbations only in
  # this disposable copy; verifier calls must preserve that copy's own modes.
  for p in [copy,*copy.rglob('*')]:p.chmod(p.stat().st_mode|0o200)
  copy_before=snap(copy);args=[str(copy),'--final-sha256',ANCHORS['FINAL.md'],'--manifest-sha256',ANCHORS['MANIFEST.json'],'--report-sha256',ANCHORS['REPORT.md']]
  def check(label,want,custom=None):
   state=snap(copy);r=subprocess.run([sys.executable,'-I','-B',str(copy/'scripts/verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30);assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state;cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
  check('baseline_full_packet',True);q=copy/'notes/FEASIBILITY.md';data=q.read_bytes();q.write_bytes(data+b'\nCONTROL\n');check('changed_payload',False);q.unlink();check('missing_payload',False);q.write_bytes(data);q.chmod(copy_before['notes/FEASIBILITY.md']['mode']);q=copy/'private/.extra';q.write_text('extra');check('hidden_extra',False);q.unlink();wrong=args.copy();wrong[6]='0'*64;check('wrong_report_anchor',False,wrong);check('restored',True);assert snap(copy)==copy_before
 run=subprocess.run([sys.executable,'-I','-B',str(ROOT/'scripts/wick_diagnostic.py')],capture_output=True,text=True,timeout=10);assert run.returncode==0 and not run.stderr and run.stdout==(ROOT/'notes/wick-diagnostic-output.txt').read_text();dump('finite-diagnostic.json',{'returncode':0,'stdout':run.stdout,'saved_output_matched':True,'limits':'Nine cubic/cubic coefficients and one cubic/three-linear star coefficient only;not QFT/source proof verification or a mathematical gate.'})
 assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items());dirs=sum(e['kind']=='directory' for e in before.values())
 dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':4,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Artifact checks only; exact file membership/bytes,not empty directories/modes. Parent snapshots observe directories/modes/links except root-directory mode.'})
 dump('input-authentication.json',{'source_blobs':30,'source_bytes':562471,'primary_single_gzip_sources':3,'primary_received_PDF':1,'nonPDF_archival_objects':3,'derived_OCR_members':1,'render_members':4,'stable_required_whole_copies':11,'stable_history_whole_copies':1,'stable_history_range_originals':1,'selected_acceptance_excerpt':1,'limits':'Local byte/path/member authentication only;no fresh protected source/primary/PDF/visual/transitive reading. OCR accuracy not independently established.'})
 dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'payload_files':117,'whole_root_files':120,'subdirectories':dirs,'source_blobs':30,'primary_single_gzip_sources':3,'primary_pdf_OCR_pairs':1,'nonPDF_archival_objects':3,'render_members':4,'stable_named_originals':stable,'whole_original_copies':12,'exact_history_range_selections':1,'selected_acceptance_excerpt':1,'artifact_cases':6,'negative_cases':4,'finite_diagnostic_coefficients':10,'whole_actual_root_unchanged':True,'limits':'Artifact/finite checks only;no independent mathematical/contribution grade.'})
 print(json.dumps({'payload':117,'files':120,'subdirs':dirs,'source_blobs':30,'primary_gzip_sources':3,'PDF_OCR_pairs':1,'renders':4,'stable_originals':13,'artifact_cases':6,'finite_coefficients':10}))
if __name__=='__main__':main()
