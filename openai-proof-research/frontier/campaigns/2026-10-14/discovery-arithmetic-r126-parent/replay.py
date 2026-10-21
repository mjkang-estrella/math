#!/usr/bin/env python3
"""Arithmetic126 byte/member authentication; no mathematical grade."""
import datetime,hashlib,importlib.util,json,shutil,subprocess,sys,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-arithmetic-discovery-r126'
spec=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'dbbf354f2942e9aba613fd7c3e26e93349c524fa57599a6a2631a3e79acc9d42','MANIFEST.json':'db3a0c285039f2ace38e89dba9645ff9f979b5b543a062d57260197f7197f1fd','REPORT.md':'363cc79aedd6f309d1a371f56bbe08e1c099d43fd91aa36c62a8c5583a32746b'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 now=datetime.datetime.now(datetime.timezone.utc).isoformat();base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'] and len(read(B/'tasks.json')['tasks'])==541
 before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Snapshot excludes root-directory mode.'});st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and st['workState']=='result_available' and not st['hasPendingChildRuns'] and not st['hasPendingQuestion'];assert all(v in st['summary'] and sha(ROOT/n)==v for n,v in ANCHORS.items())
 m=read(ROOT/'MANIFEST.json');assert len(m['files'])==69 and len(m['directories'])==7;assert {n for n,e in before.items() if e['kind']=='file'}==set(m['files'])|set(ANCHORS);assert {n for n,e in before.items() if e['kind']=='directory'}==set(m['directories'])
 for n,e in m['files'].items():assert (ROOT/n).stat().st_size==e['size'] and sha(ROOT/n)==e['sha256']
 tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']};source=read(ROOT/'private/pinned-identities.json');assert len(source)==8 and sum(e['size'] for e in source)==81199
 for e in source:
  q=ROOT/e['selected_copy'];data=q.read_bytes();node=entries[e['canonical_path']];assert len(data)==e['size']==node['size'] and sha(q)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']==node['sha'];assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['canonical_path']
 primary=read(ROOT/'private/primary-identities.json');good=[e for e in primary if 'sha256' in e];assert len(good)==5 and len(primary)==6
 for e in good:assert (ROOT/'private/primary'/f"{e['name']}.pdf").stat().st_size==e['size'] and sha(ROOT/'private/primary'/f"{e['name']}.pdf")==e['sha256'] and sha(ROOT/'private/primary'/f"{e['name']}.txt")==e['text_sha256']
 renders=read(ROOT/'private/render-identities.json');assert len(renders)==8
 for e in renders:assert (ROOT/e['path']).stat().st_size==e['size'] and sha(ROOT/e['path'])==e['sha256']
 incoming=read(ROOT/'private/incoming-identities.json');assert len(incoming)==14;stable=[];whole=0;excerpts=0
 for e in incoming:
  a,s=e['incoming_original'],e['selection'];q=ROOT/s['path'];assert q.stat().st_size==s['size'] and sha(q)==s['sha256']
  if 'sha256' in a:
   p=P/a['path'];assert p.stat().st_size==a['size'] and sha(p)==a['sha256'];stable.append({'path':a['path'],'bytes':a['size'],'sha256':a['sha256']})
   if s['kind']=='whole original':assert p.read_bytes()==q.read_bytes();whole+=1
   else:
    assert s['kind']=='exact LF line ranges';lines=p.read_bytes().splitlines(keepends=True);assert b''.join(b''.join(lines[a-1:b]) for a,b in s['ranges'])==q.read_bytes();excerpts+=1
  else:assert q.read_bytes() in (P/a['path']).read_bytes()
 assert len(stable)==13 and whole==11 and excerpts==2
 ctl=read(ROOT/'private/copied-controls-results.json');fixture=ROOT/'private/copied-controls';assert len(ctl['controls'])==8 and all(e['read_only_content_snapshot'] and (e['exit_code']==0)==e['expected_accept'] for e in ctl['controls'])
 for n,e in ctl['copied_members'].items():assert sha(ROOT/e['source'])==sha(fixture/n)==e['sha256']
 for n,v in ctl['independent_selection_anchors'].items():assert sha(fixture/({'final':'FINAL.md','manifest':'MANIFEST.json','report':'REPORT.md'}[n]))==v
 assert len(read(fixture/'MANIFEST.json')['files'])==2
 cases=[]
 with tempfile.TemporaryDirectory(prefix='arithmetic126-copy-',dir=O) as tmp:
  copy=Path(tmp)/'packet';shutil.copytree(ROOT,copy);args=[str(copy),'--final',ANCHORS['FINAL.md'],'--manifest',ANCHORS['MANIFEST.json'],'--report',ANCHORS['REPORT.md']]
  def check(label,want,custom=None):
   state=snap(copy);r=subprocess.run([sys.executable,'-I','-B',str(copy/'verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30);assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state;cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
  check('baseline_full_packet',True);q=copy/'notes/feasibility.md';data=q.read_bytes();q.write_bytes(data+b'\nCONTROL\n');check('changed_payload',False);q.unlink();check('missing_payload',False);q.write_bytes(data);q=copy/'private/.extra';q.write_text('extra');check('hidden_extra',False);q.unlink();q=copy/'private/extra-empty';q.mkdir();check('extra_empty_directory',False);q.rmdir();wrong=args.copy();wrong[4]='0'*64;check('wrong_manifest_anchor',False,wrong);q=copy/'REPORT.md';data=q.read_bytes();q.write_bytes(data+b'\nCONTROL\n');check('changed_report',False);q.write_bytes(data);check('restored',True);assert snap(copy)==before
 assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':6,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Artifact checks only. Manifest binds exact regular-file and directory membership/bytes,not modes/timestamps/root-directory mode.'})
 dump('input-authentication.json',{'source_blobs':8,'source_bytes':81199,'primary_pdf_text_pairs':5,'render_members':8,'stable_original_identities':13,'whole_original_copies':11,'exact_range_selections':2,'selected_acceptance_excerpt':1,'recorded_failed_acquisitions':1,'copied_fixture_members':2,'limits':'Local byte/path/member authentication only. No fresh protected semantic/PDF/visual/transitive reading; no mathematical experiment or formal suite.'})
 dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'payload_files':69,'whole_root_files':72,'subdirectories':7,'source_blobs':8,'primary_pdf_text_pairs':5,'render_members':8,'stable_named_originals':stable,'whole_original_copies':11,'exact_range_selections':2,'selected_acceptance_excerpt':1,'artifact_cases':8,'negative_cases':6,'whole_actual_root_unchanged':True,'limits':'Artifact checks only; no independent mathematical/contribution grade.'})
 print(json.dumps({'payload':69,'files':72,'subdirs':7,'source_blobs':8,'primary_pairs':5,'renders':8,'stable_originals':13,'whole_copies':11,'range_selections':2,'artifact_cases':8}))
if __name__=='__main__':main()
