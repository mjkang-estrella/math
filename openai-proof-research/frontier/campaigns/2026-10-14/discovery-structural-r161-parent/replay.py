#!/usr/bin/env python3
"""T126S161 author-packet authentication and finite diagnostics, no math grade."""
import datetime,hashlib,importlib.util,json,shutil,subprocess,sys,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-structural-discovery-r161'
spec=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'2c41bfa9a7cf3635729459a52fa345c529cf51eb128996d8c0cf01f063482e69','MANIFEST.json':'58987ced2f9a15587e2bdf3e7f51c5ac5c620924850f0969d251e1635a02c1b5','REPORT.md':'3b86e2f016c07f3ecab2f59d922ccdd502b23e4850f03f7d1b512ceb3af06e8d'}
SCOPE='b5c7b51d352e250df511fae5d3456ccbaa2756180111020b3108415c12a7d813';PROOF='f522cf05688e557aa7934946ee79564ee55238f0057423135a58c4d9abee451a'
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 now=datetime.datetime.now(datetime.timezone.utc).isoformat();base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'] and len(read(B/'tasks.json')['tasks'])==543
 before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Snapshot excludes root-directory mode.'});st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and st['workState']=='result_available' and not st['hasPendingChildRuns'] and not st['hasPendingQuestion'];assert all(v in st['summary'] and sha(ROOT/n)==v for n,v in ANCHORS.items());assert sha(ROOT/'scope-frozen.md')==SCOPE and sha(ROOT/'author-proof.md')==PROOF and read(ROOT/'freeze-record.json')['sha256']==SCOPE
 m=read(ROOT/'MANIFEST.json');assert len(m['files'])==81 and len(m['directories'])==11 and m['scope_frozen_sha256']==SCOPE;assert {n for n,e in before.items() if e['kind']=='file'}==set(m['files'])|set(ANCHORS) and {n for n,e in before.items() if e['kind']=='directory'}==set(m['directories'])
 for n,e in m['files'].items():assert (ROOT/n).stat().st_size==e['size'] and sha(ROOT/n)==e['sha256']
 tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']};source=read(ROOT/'private/source126-authentication.json');assert len(source)==10 and sum(e['size'] for e in source)==83443
 for e in source:
  q=ROOT/e['selected_copy'];data=q.read_bytes();node=entries[e['path']];assert len(data)==e['size']==node['size'] and sha(q)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['sha']==node['sha'];assert e['raw_url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
 primary=read(ROOT/'private/primary/acquisition01.json');assert len(primary)==5
 for e in primary:assert (ROOT/e['pdf']).stat().st_size==e['bytes'] and sha(ROOT/e['pdf'])==e['sha256'] and sha(ROOT/e['text'])==e['extracted_text_sha256']
 other=[e for e in read(ROOT/'private/primary/acquisition02.json') if 'sha256' in e]+[e for e in read(ROOT/'private/primary/acquisition03.json')['attempts'] if 'sha256' in e];e=read(ROOT/'private/primary/acquisition04.json');other.append(dict(name='bhattacharyya-et-al-2011.04144v1',size=e['size'],sha256=e['sha256']));assert len(other)==3
 for e in other:
  q=ROOT/'private/primary'/f"{e['name']}.pdf";assert q.stat().st_size==e.get('size',e.get('bytes')) and sha(q)==e['sha256'] and q.read_bytes().startswith(b'%PDF') and q.with_suffix('.txt').is_file()
 assert not (ROOT/'private/primary/finner-1992.pdf').read_bytes().startswith(b'%PDF');renders=list((ROOT/'private/render').glob('*.png'));assert len(renders)==2
 originals=read(ROOT/'private/incoming-identities.json');assert len(originals)==7;stable=[]
 for e in originals:
  p=P/e['original'];q=ROOT/e['selected_copy'];assert p.stat().st_size==q.stat().st_size==e['size'] and sha(p)==sha(q)==e['sha256'];stable.append({'path':e['original'],'bytes':e['size'],'sha256':e['sha256']})
 selected=read(ROOT/'private/history-selected/selected-identities.json');assert len(selected)==4
 for e in selected:
  p=P/e['original'];q=ROOT/e['selected_copy'];assert p.stat().st_size==e['original_bytes'] and sha(p)==e['original_sha256'] and q.stat().st_size==e['selected_copy_size'] and sha(q)==e['selected_copy_sha256'];stable.append({'path':e['original'],'bytes':e['original_bytes'],'sha256':e['original_sha256']})
  if e['semantic_selection']=='whole original':assert p.read_bytes()==q.read_bytes()
  else:
   a,b=e['semantic_selection'];assert b''.join(p.read_bytes().splitlines(keepends=True)[a-1:b])==q.read_bytes()
 assert len(stable)==11 and (ROOT/'private/acceptance-section.md').read_bytes() in (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes()
 ctl=read(ROOT/'private/copied-control-results.json');fixture=ROOT/'private/copied-control';assert len(ctl['checks'])==5 and all(e['expected_exit']==e['actual_exit'] and e['read_only_snapshot_equal'] for e in ctl['checks']);assert all(sha(fixture/n)==v for n,v in zip(ANCHORS,ctl['anchors'])) and len(read(fixture/'MANIFEST.json')['files'])==2;assert (fixture/'scope-frozen.md').read_bytes()==(ROOT/'scope-frozen.md').read_bytes() and (fixture/'author-proof.md').read_bytes()==(ROOT/'author-proof.md').read_bytes()
 cases=[];diagnostics=[]
 with tempfile.TemporaryDirectory(prefix='structural161-copy-',dir=O) as tmp:
  copy=Path(tmp)/'packet';shutil.copytree(ROOT,copy)
  for p in [copy,*copy.rglob('*')]:p.chmod(p.stat().st_mode|0o200)
  copied_before=snap(copy);args=[str(copy),*ANCHORS.values()]
  def check(label,want,custom=None):
   state=snap(copy);r=subprocess.run([sys.executable,'-I','-B',str(copy/'tools/verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30);assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state;cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
  check('baseline_full_packet',True);q=copy/'author-proof.md';data=q.read_bytes();q.write_bytes(data+b'\nCONTROL\n');check('changed_payload',False);q.unlink();check('missing_payload',False);q.write_bytes(data);q.chmod(copied_before['author-proof.md']['mode']);q=copy/'private/.extra';q.write_text('extra');check('hidden_extra',False);q.unlink();q=copy/'private/extra-empty';q.mkdir();check('extra_empty_directory',False);q.rmdir();wrong=args.copy();wrong[2]='0'*64;check('wrong_manifest_anchor',False,wrong);q=copy/'REPORT.md';data=q.read_bytes();q.write_bytes(data+b'\nCONTROL\n');check('changed_report',False);q.write_bytes(data);check('restored',True);assert snap(copy)==copied_before
  out=Path(tmp)/'finite';(out/'private').mkdir(parents=True)
  for tool,target,key in [('table_diagnostic.py','table-diagnostic.json','cases'),('mono_spectrum.py','mono-spectrum.json','results')]:
   code=(ROOT/'tools'/tool).read_text();literal='frontier/campaigns/2026-10-14/fresh-structural-discovery-r161';assert code.count(literal)==1;code=code.replace(literal,str(out));script=out/tool;script.write_text(code);r=subprocess.run([sys.executable,'-I','-B',str(script)],cwd=P,capture_output=True,text=True,timeout=180);assert r.returncode==0,(tool,r.stdout,r.stderr);assert read(out/'private'/target)==read(ROOT/'private'/target);diagnostics.append({'tool':tool,'cases':len(read(out/'private'/target)[key]),'stdout':r.stdout,'redirected_saved_record_equal':True,'actual_sealed_root_not_written':True})
 assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':6,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Disposable-copy permissions adjusted before tests;actual original modes unchanged. Exact file/directory membership and bytes only;not mathematics or rights.'})
 dump('finite-diagnostics.json',{'programs':diagnostics,'temporary_redirected_scripts_and_outputs_removed':True,'limits':'46 exact incidence/table/trace/selected-containment cases and six monochromatic spectral examples;no proof of universal bounds or contribution grade.'})
 dump('input-authentication.json',{'source_blobs':10,'source_bytes':83443,'primary_pdf_text_pairs':8,'render_members':2,'failed_primary_acquisition_families':2,'stable_original_identities':11,'whole_original_copies':9,'exact_history_range_selections':2,'selected_acceptance_excerpt':1,'limits':'Local byte/path/member authentication only. Parent did not freshly read protected source/primary/PDF/visual/transitive proofs;selected text/render identities are manifest-bound,not new OCR validation.'})
 dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'scope_frozen_sha256':SCOPE,'author_proof_sha256':PROOF,'payload_files':81,'whole_root_files':84,'subdirectories':11,'source_blobs':10,'primary_pdf_text_pairs':8,'render_members':2,'stable_named_originals':stable,'whole_original_copies':9,'exact_history_range_selections':2,'selected_acceptance_excerpt':1,'artifact_cases':8,'negative_cases':6,'finite_table_cases':46,'finite_monochromatic_cases':6,'whole_actual_root_unchanged':True,'limits':'Artifact/finite checks only;correctness and substantial-contribution independently unreviewed.'})
 print(json.dumps({'payload':81,'files':84,'dirs':11,'source_blobs':10,'primary_pairs':8,'stable_originals':11,'artifact_cases':8,'finite_table_cases':46,'monochromatic_cases':6}))
if __name__=='__main__':main()
