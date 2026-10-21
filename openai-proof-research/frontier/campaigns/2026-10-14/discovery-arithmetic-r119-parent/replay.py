#!/usr/bin/env python3
"""Completed arithmetic119 artifact archive;no mathematical suite or independent grade."""
import datetime,hashlib,importlib.util,json,shutil,subprocess,sys,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-arithmetic-discovery-r119'
spec=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'a29eb33e543087d0c697d3dd822a16c009db185315905187ef4b439b4af8d2b8','MANIFEST.json':'a426a725e5b0ca74d10b2cba532cab2112ab2373d9391dd048d50dd2f987ba5c','REPORT.md':'d8ab914dc490bdad05c5dd023843401a5d44af73f74ade6758f488a3d04a5b96'}
PROTECTED={'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json':'6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9','frontier/iterations/i31-nonconical-no-mcm.md':'d606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=P);assert len(read(B/'tasks.json')['tasks'])==520
 dump('integration-baseline.json',{'observed_utc':now,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip(),'initial_index_empty':True,'task_count':520,'task_index':517,'protected_unrelated_sha256':PROTECTED})
 before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current completed root,excluding root-directory mode;not historical whole-project/OS provenance.'})
 st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and not st['hasPendingChildRuns'] and all(v in st['summary'] for v in ANCHORS.values());assert all(sha(ROOT/n)==v for n,v in ANCHORS.items())
 m=read(ROOT/'MANIFEST.json');assert m['schema']=='r119-exact-v1' and len(m['files'])==71 and len(m['directories'])==23
 rows={e['path']:e for e in m['files']};assert len(rows)==71 and {n for n,e in before.items() if e['kind']=='file'}==set(rows)|set(ANCHORS) and {n for n,e in before.items() if e['kind']=='directory'}==set(m['directories'])
 for n,e in rows.items():assert (ROOT/n).stat().st_size==e['size'] and sha(ROOT/n)==e['sha256']
 tp=P/'sources/preprints-tree.json';tree_meta=read(ROOT/'packet/tree-identity.json');assert tp.stat().st_size==tree_meta['bytes']==4858136 and sha(tp)==tree_meta['sha256']=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=read(tp);assert len(tree['tree'])==tree_meta['entries']==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']}
 source=read(ROOT/'packet/source-identities.json');assert len(source)==27;prefixes=['preprints/Reconstruction-from-Milnor-K-theory-modulo-the-characteristic-October-5-2026/','preprints/Reconstruction-of-Function-Fields-from-Mod-ell-Milnor-K-Theory-October-5-2026/','preprints/The-Bogomolov-Pop-reconstruction-theorem-September-23-2026/']
 assert {e['path'] for e in source}=={p for p,e in entries.items() if e['type']=='blob' and any(p.startswith(q) for q in prefixes) and p.endswith(('.tex','.bib'))}
 for e in source:
  data=(ROOT/e['local']).read_bytes();node=entries[e['path']];assert len(data)==e['size']==node['size'] and sha(ROOT/e['local'])==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['sha']==node['sha'];assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
 primary=read(ROOT/'packet/primary-identities.json');assert len(primary)==4;pdfs=0
 for e in primary:
  ext='.pdf' if e['name'].startswith('topaz-') else '.html';p=ROOT/'private/primary'/(e['name']+ext);assert p.stat().st_size==e['bytes'] and sha(p)==e['sha256']
  if 'text_sha256' in e:assert sha(p.with_suffix('.txt'))==e['text_sha256'];pdfs+=1
 assert pdfs==2
 stable=[];excerpts=[];incoming=read(ROOT/'packet/incoming-identities.json');assert len(incoming)==13
 for e in incoming:
  q=ROOT/e['copy_path'];assert q.stat().st_size==e['copy_size'] and sha(q)==e['copy_sha256']
  if e['selection']=='whole':
   p=P/e['original_path'];assert p.read_bytes()==q.read_bytes() and p.stat().st_size==e['original_size'] and sha(p)==e['original_sha256'];stable.append({'path':e['original_path'],'bytes':e['original_size'],'sha256':e['original_sha256']})
  else:excerpts.append(e|{'limit':'Independent retained excerpt only;whole observation not a current/future post-append stability input.'})
 assert len(stable)==10 and len(excerpts)==3
 recheck=read(ROOT/'packet/identity-recheck.json');assert len(recheck['source'])==27 and all(e['match'] for e in recheck['source']) and len(recheck['incoming'])==13 and all(e['whole_original_matches_late_capture'] and e['selected_copy_matches'] for e in recheck['incoming']) and len(recheck['primary'])==4 and all(e['match'] for e in recheck['primary'])
 ctl=read(ROOT/'packet/control-results.json');fixture=ROOT/'private/controls/selected-copy';assert len(ctl['results'])==7 and all(e['control_succeeded'] and e['readonly_snapshot_equal'] and (e['exit_code']==0)==e['expected_accept'] for e in ctl['results']) and len(ctl['selection_mapping'])==3
 assert all(sha(fixture/n)==v for n,v in ctl['selected_copy_anchors'].items());fm=read(fixture/'MANIFEST.json');assert len(fm['files'])==3
 for e in ctl['selection_mapping']:assert (ROOT/e['original_path']).read_bytes()==(ROOT/e['copy_path']).read_bytes() and sha(ROOT/e['original_path'])==e['sha256'] and (ROOT/e['copy_path']).stat().st_size==e['bytes']
 cases=[]
 with tempfile.TemporaryDirectory(prefix='arithmetic119-copy-',dir=O) as temp:
  copy=Path(temp)/'packet';shutil.copytree(ROOT,copy);args=['--root',str(copy),'--final-sha256',ANCHORS['FINAL.md'],'--manifest-sha256',ANCHORS['MANIFEST.json'],'--report-sha256',ANCHORS['REPORT.md']]
  def check(label,want,custom=None):
   state=snap(copy);r=subprocess.run([sys.executable,'-I','-B',str(copy/'packet/code/verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30);assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state;cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
  check('baseline_full_packet',True);p=copy/'packet/notes/start.md';data=p.read_bytes();p.write_bytes(data+b'\nCONTROL\n');check('modified_payload',False);p.unlink();check('missing_payload',False);p.write_bytes(data);p=copy/'private/.extra';p.write_text('extra');check('hidden_extra',False);p.unlink();p=copy/'private/.empty';p.mkdir();check('empty_extra_directory',False);p.rmdir();wrong=args.copy();wrong[5]='0'*64;check('wrong_manifest_anchor',False,wrong);check('restored',True);assert snap(copy)==before
 assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in PROTECTED.items())
 dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':5,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Artifact checks,not mathematics;verifier binds files/directories and rejects links/nonregular files,not modes.'})
 dump('input-authentication.json',{'source_blobs':27,'primary_received_objects':4,'primary_pdfs':2,'primary_html_captures':2,'byte_bound_text_derivatives':2,'byte_bound_renders':2,'stable_whole_original_copies':10,'selected_excerpts':3,'selected_fixture_members':3,'limits':'Local bytes/selection membership only;no fresh remote,protected-body semantic reading,extraction or PDF visual attestation.Late HTML capture is not original web-render identity.'})
 dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'payload_files':71,'whole_root_files':74,'subdirectories':23,'source_blobs':27,'primary_received_objects':4,'stable_named_originals':stable,'selected_original_excerpts':excerpts,'artifact_cases':7,'negative_cases':5,'whole_actual_root_unchanged':True,'limits':'Byte archive only,no mathematical numerical/formal suite or independent grade.Parent snapshots exclude root-directory mode.'})
 print(json.dumps({'files':74,'payload':71,'subdirectories':23,'source_blobs':27,'primary_objects':4,'stable_whole_copies':10,'excerpts':3,'artifact_cases':7}))
if __name__=='__main__':main()
