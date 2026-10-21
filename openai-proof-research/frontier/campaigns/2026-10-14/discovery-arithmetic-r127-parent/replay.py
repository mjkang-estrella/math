#!/usr/bin/env python3
"""Arithmetic127 byte/member authentication; no mathematical grade."""
import datetime,hashlib,importlib.util,json,shutil,subprocess,sys,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-arithmetic-discovery-r127'
spec=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'ea2aff4c267bc59eb15e3df0b37228a2e3bae35806d8b1ab278d87763ef9e1ee','MANIFEST.json':'45c5e542645f1af27699e1b448006ee114081427785e3348862dff2c729bbbab','REPORT.md':'56857b47bb18a34a73d96c2c4d5bbac509662f49cc3e55f55ba22313b97e217a'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 now=datetime.datetime.now(datetime.timezone.utc).isoformat();base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'] and len(read(B/'tasks.json')['tasks'])==545
 before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Snapshot excludes root-directory mode.'});st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and st['workState']=='result_available' and not st['hasPendingChildRuns'] and not st['hasPendingQuestion'];assert all(v in st['summary'] and sha(ROOT/n)==v for n,v in ANCHORS.items())
 m=read(ROOT/'MANIFEST.json');assert len(m['files'])==75 and len(m['directories'])==9;assert {n for n,e in before.items() if e['kind']=='file'}==set(m['files'])|set(ANCHORS);assert {n for n,e in before.items() if e['kind']=='directory'}==set(m['directories'])
 for n,e in m['files'].items():assert (ROOT/n).stat().st_size==e['size'] and sha(ROOT/n)==e['sha256']
 tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']};source=read(ROOT/'private/pinned-identities.json')+read(ROOT/'private/companion-identities.json');assert len(source)==16 and sum(e['size'] for e in source)==485737
 for e in source:
  q=ROOT/e['copy'];data=q.read_bytes();node=entries[e['canonical_path']];assert len(data)==e['size']==node['size'] and sha(q)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']==node['sha'];assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['canonical_path']
 primary=read(ROOT/'private/primary-identities.json');good=[e for e in primary if 'sha256' in e];assert len(good)==5 and len(primary)==6
 for e in good:assert (ROOT/'private/primary'/f"{e['name']}.pdf").stat().st_size==e['size'] and sha(ROOT/'private/primary'/f"{e['name']}.pdf")==e['sha256'] and sha(ROOT/'private/primary'/f"{e['name']}.txt")==e['text_sha256']
 renders=read(ROOT/'private/render-identities.json');assert len(renders)==8
 for e in renders:assert (ROOT/e['path']).stat().st_size==e['size'] and sha(ROOT/e['path'])==e['sha256']
 incoming=read(ROOT/'private/incoming-identities.json')['entries'];assert len(incoming)==13;stable=[];whole=0;excerpts=0
 for e in incoming:
  p=P/e['original_path'];q=ROOT/e['copy'];assert p.stat().st_size==e['original_size'] and sha(p)==e['original_sha256'] and q.stat().st_size==e['copy_size'] and sha(q)==e['copy_sha256'];stable.append({'path':e['original_path'],'bytes':e['original_size'],'sha256':e['original_sha256']})
  if e['selection']=='whole':assert p.read_bytes()==q.read_bytes();whole+=1
  else:
   lines=p.read_bytes().splitlines(keepends=True);assert b''.join(b''.join(lines[a-1:b]) for a,b in e['selection'])==q.read_bytes();excerpts+=1
 assert len(stable)==13 and whole==10 and excerpts==3 and (ROOT/'private/acceptance-section.txt').read_bytes() in (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes()
 ctl=read(ROOT/'private/copied-controls-results.json');fixture=ROOT/'private/copied-control';assert len(ctl['checks'])==8 and all(e['readonly_content'] and e['success']==e['expected_success'] for e in ctl['checks']);assert all(sha(fixture/n)==v for n,v in ctl['own_anchors'].items()) and len(read(fixture/'MANIFEST.json')['files'])==2
 assert (fixture/'verify.py').read_bytes()==(ROOT/'verify.py').read_bytes() and (fixture/'note.md').read_bytes()!=(ROOT/'notes/integrated-threshold-reduction.md').read_bytes() and 'before the Chen-version' in ctl['chronology']
 cases=[]
 with tempfile.TemporaryDirectory(prefix='arithmetic127-copy-',dir=O) as tmp:
  copy=Path(tmp)/'packet';shutil.copytree(ROOT,copy)
  for p in [copy,*copy.rglob('*')]:p.chmod(p.stat().st_mode|0o200)
  copy_before=snap(copy);args=['--root',str(copy),'--final-sha256',ANCHORS['FINAL.md'],'--manifest-sha256',ANCHORS['MANIFEST.json'],'--report-sha256',ANCHORS['REPORT.md']]
  def check(label,want,custom=None):
   state=snap(copy);r=subprocess.run([sys.executable,'-I','-B',str(copy/'verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30);assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state;cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
  check('baseline_full_packet',True);q=copy/'notes/feasibility.md';data=q.read_bytes();q.write_bytes(data+b'\nCONTROL\n');check('changed_payload',False);q.unlink();check('missing_payload',False);q.write_bytes(data);q.chmod(copy_before['notes/feasibility.md']['mode']);q=copy/'private/.extra';q.write_text('extra');check('hidden_extra',False);q.unlink();q=copy/'private/extra-empty';q.mkdir();check('extra_empty_directory',False);q.rmdir();wrong=args.copy();wrong[5]='0'*64;check('wrong_manifest_anchor',False,wrong);q=copy/'REPORT.md';data=q.read_bytes();q.write_bytes(data+b'\nCONTROL\n');check('changed_report',False);q.write_bytes(data);check('restored',True);assert snap(copy)==copy_before
 with tempfile.TemporaryDirectory(prefix='arithmetic127-finite-',dir=O) as tmp:
  out=Path(tmp);(out/'private').mkdir();code=(ROOT/'scripts/quotient_diagnostic.py').read_text();literal='frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r127';assert code.count(literal)==1;script=out/'diagnostic.py';script.write_text(code.replace(literal,str(out)));r=subprocess.run([sys.executable,'-I','-B',str(script)],cwd=P,capture_output=True,text=True,timeout=60);assert r.returncode==0 and read(out/'private/quotient-diagnostic.json')==read(ROOT/'private/quotient-diagnostic.json');assert len(read(out/'private/quotient-diagnostic.json')['rows'])==30;dump('finite-diagnostic.json',{'returncode':0,'stdout':r.stdout,'redirected_saved_record_equal':True,'cases':30,'temporary_outputs_removed':True,'limits':'Finite generator-factorization diagnostic only,no universal mathematical grade.'})
 assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':6,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Artifact checks only. Manifest binds exact regular-file and directory membership/bytes,not modes/timestamps/root-directory mode.'})
 dump('input-authentication.json',{'source_blobs':16,'source_bytes':485737,'primary_pdf_text_pairs':5,'render_members':8,'stable_original_identities':13,'whole_original_copies':10,'exact_range_selections':3,'selected_acceptance_excerpt':1,'recorded_failed_acquisitions':1,'copied_fixture_members':2,'fixture_note_is_explicit_earlier_draft':True,'limits':'Local byte/path/member authentication only. No fresh protected semantic/PDF/visual/transitive reading; no mathematical experiment or formal suite.'})
 dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'payload_files':75,'whole_root_files':78,'subdirectories':9,'source_blobs':16,'primary_pdf_text_pairs':5,'render_members':8,'stable_named_originals':stable,'whole_original_copies':10,'exact_range_selections':3,'selected_acceptance_excerpt':1,'artifact_cases':8,'negative_cases':6,'whole_actual_root_unchanged':True,'finite_cases':30,'limits':'Artifact/finite checks only; no independent mathematical/contribution grade.'})
 print(json.dumps({'payload':75,'files':78,'subdirs':9,'source_blobs':16,'primary_pairs':5,'renders':8,'stable_originals':13,'whole_copies':10,'range_selections':3,'artifact_cases':8}))
if __name__=='__main__':main()
