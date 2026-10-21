#!/usr/bin/env python3
"""Authenticate full-scope contribution review; correctness condition discharged."""
import datetime,hashlib,importlib.util,json,shutil,stat,subprocess,sys,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;C=O.parent;B=C.parent;P=B.parents[2];ROOT=B/'structural-r161-contribution-r1';AUTHOR=B/'fresh-structural-discovery-r161'
spec=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'d1c9322ba7dcb47fae3a59d5f5180be30e570589e8b2140a3e363e2b4e69c687','MANIFEST.json':'d984f5f1c67495a76a552130d1fc65616855e39bd2ed46f5a86d919e841e171c','REPORT.md':'595e4cba1ba7fa306da5b4f95e6527cc126449c8171c44aca5100ee389bcc479'}
SCOPE='b5c7b51d352e250df511fae5d3456ccbaa2756180111020b3108415c12a7d813';PROOF='f522cf05688e557aa7934946ee79564ee55238f0057423135a58c4d9abee451a'
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 now=datetime.datetime.now(datetime.timezone.utc).isoformat();base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'] and len(read(B/'tasks.json')['tasks'])==546
 before=snap(ROOT);author_before=snap(AUTHOR);assert author_before==read(C/'observed-root.json')['root'];dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Snapshot excludes root-directory mode.'})
 st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and st['workState']=='result_available' and not st['hasPendingChildRuns'] and not st['hasPendingQuestion'];assert 'TECHNICAL' in st['summary'] and all(v in st['summary'] and sha(ROOT/n)==v for n,v in ANCHORS.items());assert sha(AUTHOR/'scope-frozen.md')==SCOPE and sha(AUTHOR/'author-proof.md')==PROOF
 m=read(ROOT/'MANIFEST.json');assert len(m['files'])==39 and len(m['directories'])==12;assert {n for n,e in before.items() if e['kind']=='file'}==set(m['files'])|set(ANCHORS) and {n for n,e in before.items() if e['kind']=='directory'}==set(m['directories'])
 for n,e in m['files'].items():assert (ROOT/n).stat().st_size==e['size'] and sha(ROOT/n)==e['sha256'] and stat.S_IMODE((ROOT/n).stat().st_mode)==e['mode']
 for n,v in m['directories'].items():assert stat.S_IMODE((ROOT/n).stat().st_mode)==v
 ledger=read(B/'tasks.json');assert ledger['tasks'][540]['correctness']=='PASS' and ledger['tasks'][540]['scope_frozen_sha256']==SCOPE and ledger['tasks'][540]['author_proof_sha256']==PROOF and ledger['tasks'][543]['correctness']=='PASS' and not ledger['tasks'][543]['mathematical_repairs_required']
 stablemap={}
 for e in read(ROOT/'private/metadata/input-stability.json')['checks']:
  p=P/e['path'];stt=p.stat();assert sha(p)==e['sha256'] and oct(stat.S_IMODE(stt.st_mode))==e['mode']
  if 'mtime_ns' in e:assert stt.st_mtime_ns==e['mtime_ns']
  stablemap[e['path']]={'path':e['path'],'bytes':stt.st_size,'sha256':e['sha256'],'mode':e['mode']}
 stable=list(stablemap.values());assert len(stable)==21
 selected=read(ROOT/'private/metadata/selected-input-identities.json');assert len(selected)==16
 for e in selected:
  p=P/e['incoming_original_fixture'];q=ROOT/e['selected_member'];assert p.stat().st_size==q.stat().st_size==e['incoming_size'] and sha(p)==sha(q)==e['incoming_sha256'] and oct(stat.S_IMODE(p.stat().st_mode))==e['incoming_mode'] and p.stat().st_mtime_ns==e['incoming_mtime_ns']
 source=read(ROOT/'private/metadata/operative-source-identity.json');tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];e=source['canonical_candidates'][0];node=next(x for x in tree['tree'] if x['path']==e['path']);data=(P/source['original_fixture']).read_bytes();assert len(data)==source['size']==node['size']==15479 and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==source['git_blob']==node['sha'] and hashlib.sha256(data).hexdigest()==source['sha256']
 for e in read(ROOT/'private/metadata/input-authentication.json'):
  p=P/e['path'];assert sha(p)==e['sha256']
  if 'mode' in e:assert oct(stat.S_IMODE(p.stat().st_mode))==e['mode']
 assert len(list((ROOT/'private/render').glob('*.png')))==2
 ctl=read(ROOT/'private/metadata/copied-control-results.json');fixture=ROOT/'private/copied-controls';assert len(ctl['controls'])==7 and all(e['expected_match']==e['observed_match'] for e in ctl['controls']) and ctl['unchanged'] and ctl['source_target_before']==ctl['source_target_after'];inner=read(fixture/'MANIFEST.json');assert len(inner['files'])==2 and (fixture/'derivation-copy.txt').read_bytes()==(ROOT/'review.md').read_bytes()
 for n,e in inner['files'].items():assert (fixture/n).stat().st_size==e['size'] and sha(fixture/n)==e['sha256'] and stat.S_IMODE((fixture/n).stat().st_mode)==e['mode']
 misplaced=P.parent/'frontier/campaigns/2026-10-14/structural-r161-contribution-r1/private/search';assert not (misplaced/'search02.json').exists() and not (misplaced/'search03.json').exists()
 cases=[]
 with tempfile.TemporaryDirectory(prefix='contribution-copy-',dir=O) as tmp:
  copy=Path(tmp)/'packet';shutil.copytree(ROOT,copy);copy.chmod(copy.stat().st_mode|0o200);copied_before=snap(copy);args=[str(copy),*ANCHORS.values()]
  def check(label,want,custom=None):
   state=snap(copy);r=subprocess.run([sys.executable,'-I','-B',str(copy/'tools/verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30);assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state;cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
  check('baseline_full_packet',True);q=copy/'review.md';data=q.read_bytes();q.write_bytes(data+b'\nCONTROL\n');check('changed_payload',False);q.unlink();check('missing_payload',False);q.write_bytes(data);q.chmod(copied_before['review.md']['mode']);q=copy/'.extra';q.write_text('extra');check('hidden_extra',False);q.unlink();q=copy/'extra-empty';q.mkdir();check('extra_empty_directory',False);q.rmdir();wrong=args.copy();wrong[3]='0'*64;check('wrong_report_anchor',False,wrong);q=copy/'review.md';q.chmod(q.stat().st_mode^0o100);check('changed_payload_mode',False);q.chmod(copied_before['review.md']['mode']);check('restored',True);assert snap(copy)==copied_before
 assert snap(ROOT)==before and snap(AUTHOR)==author_before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':6,'copy_removed':True,'whole_actual_review_and_author_roots_unchanged':True,'limits':'Manifest binds files/directories/bytes/modes;no root-directory mode,timestamps or atimes binding.'})
 dump('input-authentication.json',{'review_payload_files':39,'source_blobs':1,'source_bytes':15479,'primary_pdf_text_pairs':6,'render_members':2,'stable_original_identities':21,'selected_whole_original_copies':16,'copied_fixture_members':2,'corrected_outside_project_search_receipts_absent_at_exact_paths':True,'limits':'Local bytes/path/member authentication only;no fresh source/primary/PDF/visual reading. Inner fixture hashes/membership are bound by independently anchored outer review,not a separately supplied inner detached transcript.'})
 dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'payload_files':39,'whole_root_files':42,'subdirectories':12,'scope_frozen_sha256':SCOPE,'author_proof_sha256':PROOF,'source_blobs':1,'primary_pdf_text_pairs':6,'render_members':2,'stable_named_originals':stable,'selected_whole_original_copies':16,'artifact_cases':8,'negative_cases':6,'review_and_author_roots_unchanged':True,'correctness_condition_discharged':True,'limits':'Full unchanged-scope conditional TECHNICAL adopted with existing full correctness PASS;no acceptance/count or downstream stages.'})
 print(json.dumps({'review_payload':39,'files':42,'dirs':12,'stable_originals':21,'selected_copies':16,'artifact_cases':8,'correctness_condition_discharged':True}))
if __name__=='__main__':main()
