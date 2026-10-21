#!/usr/bin/env python3
"""Arithmetic122 artifact archive; no mathematical grade."""
import datetime,hashlib,importlib.util,json,shutil,subprocess,sys,tempfile
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-arithmetic-discovery-r122'
spec=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'4dd7bd902acd856329331ff8dc436a9d69afe5e2b9bf3f1d10561e1d1d7addab','MANIFEST.json':'b315916f85ab6a8b4786c89522a80c64f5d17fb2d016149b67f795b13a822de9','REPORT.md':'9d1f540f3e0e510ddfeef887bef83ce667a8eea06adbb0e9722c47afb8fedd1e'}
PROTECTED={'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json':'6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9','frontier/iterations/i31-nonconical-no-mcm.md':'d606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=P)
 head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip();assert head=='47bea182824cba471da9d422230ae9fe10f5ac57' and len(read(B/'tasks.json')['tasks'])==529
 dump('integration-baseline.json',{'observed_utc':now,'head':head,'initial_index_empty':True,'task_count':529,'task_index':526,'protected_unrelated_sha256':PROTECTED})
 before=snap(ROOT);dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current completed root,excluding root-directory mode;not historical whole-project or OS isolation.'})
 st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and st['workState']=='result_available' and not st['hasPendingChildRuns'] and not st['hasPendingQuestion']
 assert all(v in st['summary'] and sha(ROOT/n)==v for n,v in ANCHORS.items())
 m=read(ROOT/'MANIFEST.json');assert m['schema']==1 and m['outside_envelopes']==list(ANCHORS) and len(m['payload'])==85 and len(m['directories'])==38
 rows={e['path']:e for e in m['payload']};assert len(rows)==85 and {n for n,e in before.items() if e['kind']=='file'}==set(rows)|set(ANCHORS)
 assert {n for n,e in before.items() if e['kind']=='directory'}==set(m['directories'])
 for n,e in rows.items():assert (ROOT/n).stat().st_size==e['size'] and sha(ROOT/n)==e['sha256']
 tm=read(ROOT/'private/tree-identity.json');tp=P/tm['path'];assert tp.stat().st_size==tm['size']==4858136 and sha(tp)==tm['sha256']=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
 tree=read(tp);assert len(tree['tree'])==tm['entries']==13223 and not tree['truncated'] and not tm['truncated'];entries={e['path']:e for e in tree['tree']}
 source=read(ROOT/'private/source-identities.json');assert len(source)==37 and len({e['canonical_path'].split('/')[1] for e in source})==7
 for e in source:
  q=ROOT/e['selected_copy'];data=q.read_bytes();node=entries[e['canonical_path']]
  assert len(data)==e['size']==node['size'] and sha(q)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']==node['sha']
  assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['canonical_path']
 primary=read(ROOT/'private/primary-identities.json');assert len(primary)==6
 for e in primary:
  q=ROOT/e['pdf_copy'];t=ROOT/e['text_copy'];assert q.stat().st_size==e['pdf_size'] and sha(q)==e['pdf_sha256'] and sha(t)==e['text_sha256']
 render=read(ROOT/'private/render-identity.json');q=ROOT/render['path'];assert q.stat().st_size==render['size'] and sha(q)==render['sha256'] and render['one_based_page']==17
 incoming=read(ROOT/'private/incoming-identities.json');assert len(incoming)==11;stable=[];excerpts=[];whole=0
 for e in incoming:
  q=ROOT/e['selected_copy'];p=P/e['original_path'];assert q.stat().st_size==e['selected_size'] and sha(q)==e['selected_sha256'];mutable=e['original_path']=='frontier/NEW-TEN-2026-10-14.md'
  if not mutable:
   assert p.stat().st_size==e['original_size'] and sha(p)==e['original_sha256'];stable.append({'path':e['original_path'],'bytes':e['original_size'],'sha256':e['original_sha256']})
  if e['selection']=='whole':assert p.read_bytes()==q.read_bytes();whole+=1
  else:
   lines=p.read_text().splitlines(keepends=True);s=e['selection'];assert s['prefix']=='original line number + colon space'
   selected=''.join(f'{i}: {lines[i-1]}' for a,b in s['inclusive_line_ranges'] for i in range(a,b+1));assert selected.encode()==q.read_bytes()
   excerpts.append(e|{'whole_current_sha256':sha(p),'whole_capture_still_matches':sha(p)==e['original_sha256'],'limit':'Late selected excerpt;no initial or post-append whole-original stability.'})
 assert len(stable)==10 and whole==9 and len(excerpts)==2
 pre=read(ROOT/'private/preseal-byte-check.json');assert pre['source_blobs']==37 and pre['primary_pdf_text_pairs']==6 and pre['selected_incoming_copies']==11 and sum(e['matches_late_capture'] for e in pre['late_incoming_stability'])==10
 ctl=read(ROOT/'private/copied-control-results.json');fixture=ROOT/ctl['fixture'];assert len(ctl['cases'])==7 and all((e['exit_code']==0)==e['expected_accept'] and e['read_only_snapshot_unchanged'] and e['expected_behavior'] for e in ctl['cases'])
 assert all(sha(fixture/n)==v for n,v in ctl['detached_fixture_anchors'].items()) and len(read(fixture/'MANIFEST.json')['payload'])==2
 for e in ctl['selected_originals']:assert (ROOT/e['source']).read_bytes()==(fixture/e['selected_copy']).read_bytes() and sha(ROOT/e['source'])==e['sha256']
 cases=[]
 with tempfile.TemporaryDirectory(prefix='arithmetic122-copy-',dir=O) as tmp:
  copy=Path(tmp)/'packet';shutil.copytree(ROOT,copy);args=[str(copy),'--final-sha256',ANCHORS['FINAL.md'],'--manifest-sha256',ANCHORS['MANIFEST.json'],'--report-sha256',ANCHORS['REPORT.md']]
  def check(label,want,custom=None):
   state=snap(copy);r=subprocess.run([sys.executable,'-I','-B',str(copy/'tools/verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30)
   assert (r.returncode==0)==want,(label,r.stdout,r.stderr);assert snap(copy)==state
   cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
  check('baseline_full_packet',True);q=copy/'packet/notes/start.md';data=q.read_bytes();q.write_bytes(data+b'\nCONTROL\n');check('modified_payload',False)
  q.unlink();check('missing_payload',False);q.write_bytes(data);q=copy/'private/.extra';q.write_text('extra');check('hidden_extra',False);q.unlink()
  q=copy/'private/.empty';q.mkdir();check('empty_extra_directory',False);q.rmdir();wrong=args.copy();wrong[4]='0'*64;check('wrong_manifest_anchor',False,wrong);check('restored',True);assert snap(copy)==before
 assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in PROTECTED.items())
 dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':5,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Artifact only.Manifest binds exact files/directories and bytes,not modes.Parent snapshots additionally observe modes/links,excluding root-directory mode.'})
 dump('input-authentication.json',{'selected_source_blobs':37,'source_titles':7,'primary_pdf_text_pairs':6,'bound_render':render['path'],'stable_whole_original_byte_identities':10,'selected_whole_copies':9,'selected_excerpts':2,'selected_fixture_members':2,'limits':'Local bytes/paths/selected membership only.Not complete source-family acquisition,no fresh protected semantic/PDF visual reading,remote retrieval or transitive/published-final coverage.'})
 dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'payload_files':85,'whole_root_files':88,'subdirectories':38,'source_blobs':37,'primary_pdfs':6,'stable_named_originals':stable,'selected_original_excerpts':excerpts,'artifact_cases':7,'negative_cases':5,'whole_actual_root_unchanged':True,'limits':'Artifact archive only,no mathematical/formal/numerical suite or grade.Parent snapshots exclude root-directory mode.'})
 print(json.dumps({'files':88,'payload':85,'subdirectories':38,'source_blobs':37,'source_titles':7,'primary_pdfs':6,'stable_original_identities':10,'whole_copies':9,'excerpts':2,'artifact_cases':7}))
if __name__=='__main__':main()
