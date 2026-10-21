#!/usr/bin/env python3
"""Arithmetic120 archive authentication and disposable artifact controls only."""
import datetime, hashlib, importlib.util, json, shutil, subprocess, sys, tempfile
from pathlib import Path
O=Path(__file__).resolve().parent; B=O.parent; P=B.parents[2]
ROOT=B/'fresh-arithmetic-discovery-r120'; PACKET=ROOT/'packet'
spec=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py')
h=importlib.util.module_from_spec(spec); spec.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'c49e4215f362fc474c7fda4ff4546b1e3ae21840c41f43936c1df7a22d152096','MANIFEST.json':'25883afada21e5ad8da12c4f04176d8c73b56b892373a6db15e39b07a52f5e07','REPORT.md':'81326bc334e4acf2afaea31a5f42b3c16e4081d29fff2eff0d7bfe78b5539fb0'}
PROTECTED={'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json':'6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9','frontier/iterations/i31-nonconical-no-mcm.md':'d606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a'}
def read(p): return json.loads(p.read_text())
def dump(n,d): (O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 now=datetime.datetime.now(datetime.timezone.utc).isoformat()
 assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=P)
 assert len(read(B/'tasks.json')['tasks'])==523
 head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()
 assert head=='f15c25d226439d1201cb9129d88779392457262a'
 dump('integration-baseline.json',{'observed_utc':now,'head':head,'initial_index_empty':True,'task_count':523,'task_index':520,'protected_unrelated_sha256':PROTECTED})
 before=snap(ROOT)
 dump('observed-root.json',{'observed_utc':now,'root':before,'limits':'Current completed root; excludes root-directory mode. No historical whole-project or OS-isolation assertion.'})
 st=read(O/'task-status.json')['structuredContent']
 assert st['status']=='completed' and st['workState']=='result_available' and not st['hasPendingChildRuns'] and not st['hasPendingQuestion']
 assert all(v in st['summary'] and sha(ROOT/n)==v for n,v in ANCHORS.items())
 m=read(ROOT/'MANIFEST.json'); rows=m['files']
 assert m['schema']==1 and isinstance(rows,dict) and len(rows)==61 and len(m['directories'])==12
 assert {'FINAL.md','REPORT.md'}<=set(rows) and 'MANIFEST.json' not in rows
 assert {n for n,e in before.items() if e['kind']=='file'}==set(rows)|{'MANIFEST.json'}
 assert {n for n,e in before.items() if e['kind']=='directory'}==set(m['directories'])
 for n,e in rows.items(): assert (ROOT/n).stat().st_size==e['size'] and sha(ROOT/n)==e['sha256']
 treepath=P/'sources/preprints-tree.json'
 assert sha(treepath)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
 tree=read(treepath); assert len(tree['tree'])==13223 and not tree['truncated']
 entries={e['path']:e for e in tree['tree']}; source=read(PACKET/'source-identities.json'); assert len(source)==17
 mainprefix='preprints/The-Abelian-Zilber-Pink-Conjecture-September-24-2026/'
 assert {e['path'] for e in source if e['path'].startswith(mainprefix)}=={p for p,e in entries.items() if e['type']=='blob' and p.startswith(mainprefix) and p.endswith(('.tex','.bib'))}
 assert len([e for e in source if e['path'].startswith(mainprefix)])==14
 for e in source:
  q=PACKET/e['local']; data=q.read_bytes(); node=entries[e['path']]
  assert len(data)==e['size']==node['size'] and sha(q)==e['sha256']
  assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']==node['sha']
  assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
 primary=read(PACKET/'primary-identities.json'); assert len(primary)==6
 received=[e for e in primary if 'local' in e]; assert len(received)==4
 for e in received:
  q=PACKET/e['local']; assert q.stat().st_size==e['size'] and sha(q)==e['sha256'] and sha(q.with_suffix('.txt'))==e['text_sha256']
 assert all(e['received_file'] is False and 'error' in e for e in primary if 'local' not in e)
 renders=[n for n in rows if n.startswith('packet/private/primary/') and n.endswith('.png')]; assert len(renders)==4
 stable=[]; excerpts=[]; originals=read(PACKET/'incoming-identities.json'); assert len(originals)==11
 whole=0
 for e in originals:
  p=P/e['original_path']; kind=e['selection']['kind']; mutable=e['original_path']=='frontier/NEW-TEN-2026-10-14.md'
  if not mutable:
   assert p.stat().st_size==e['original_size'] and sha(p)==e['original_sha256']
   stable.append({'path':e['original_path'],'bytes':e['original_size'],'sha256':e['original_sha256']})
  if e['copy'] is None: assert kind=='identity_only'; continue
  q=PACKET/e['copy']; assert q.stat().st_size==e['copy_size'] and sha(q)==e['copy_sha256']
  if kind=='whole': assert p.read_bytes()==q.read_bytes(); whole+=1
  else:
   lines=p.read_text().splitlines(keepends=True)
   if kind=='line_ranges':
    expected=''.join(''.join(lines[a-1:b]) for a,b in e['selection']['ranges']).encode()
    assert expected==q.read_bytes()
   else:
    assert kind=='numbered_lines'
    # The retained catalogue selection is byte-bound independently; its numbering
    # format and the child's historical body-read chronology are not re-certified.
   excerpts.append(e|{'whole_current_sha256':sha(p),'whole_capture_still_matches':sha(p)==e['original_sha256'],'limit':'Selected copy only; mutable journal is not a stable original after parent appends.'})
 assert len(stable)==10 and whole==7 and len(excerpts)==3
 recheck=read(PACKET/'identity-recheck.json')
 assert len(recheck['source'])==17 and all(e['match'] for e in recheck['source'])
 assert len(recheck['incoming'])==11 and all(e['capture_to_recheck_match'] for e in recheck['incoming'])
 assert all(e['selected_copy_match'] for e in recheck['incoming'] if e['selected_copy_match'] is not None)
 assert len(recheck['primary'])==4 and all(e['pdf_match'] and e['text_match'] for e in recheck['primary'])
 ctl=read(PACKET/'control-results.json'); fixture=PACKET/'private/copied-controls'
 assert len(ctl['tests'])==7 and all(e['matched'] and e['read_only_snapshot_equal'] and e['actual_accept']==e['expected_accept'] for e in ctl['tests'])
 assert len(ctl['selection_mapping'])==3 and all(sha(fixture/n)==v for n,v in ctl['anchors'].items())
 fm=read(fixture/'MANIFEST.json'); assert len(fm['files'])==5 and len(fm['directories'])==1
 for e in ctl['selection_mapping']:
  assert (PACKET/e['original']).read_bytes()==(fixture/e['copy']).read_bytes()
  assert sha(PACKET/e['original'])==e['original_sha256']==e['copy_sha256']
 cases=[]
 with tempfile.TemporaryDirectory(prefix='arithmetic120-copy-',dir=O) as tmp:
  copy=Path(tmp)/'packet'; shutil.copytree(ROOT,copy)
  args=[str(copy),'--final-sha256',ANCHORS['FINAL.md'],'--manifest-sha256',ANCHORS['MANIFEST.json'],'--report-sha256',ANCHORS['REPORT.md']]
  def check(label,want,custom=None):
   state=snap(copy); r=subprocess.run([sys.executable,'-I','-B',str(copy/'packet/verify.py'),*(custom or args)],capture_output=True,text=True,timeout=30)
   assert (r.returncode==0)==want,(label,r.stdout,r.stderr)
   assert snap(copy)==state
   cases.append({'case':label,'expected_pass':want,'returncode':r.returncode,'fixture_unchanged':True,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
  check('baseline_full_packet',True)
  q=copy/'packet/notes/start.md'; data=q.read_bytes(); q.write_bytes(data+b'\nCONTROL\n'); check('modified_payload',False)
  q.unlink(); check('missing_payload',False); q.write_bytes(data)
  q=copy/'packet/private/.extra'; q.write_text('extra'); check('hidden_extra',False); q.unlink()
  q=copy/'packet/private/.empty'; q.mkdir(); check('empty_extra_directory',False); q.rmdir()
  wrong=args.copy(); wrong[4]='0'*64; check('wrong_manifest_anchor',False,wrong); check('restored',True)
  assert snap(copy)==before
 assert snap(ROOT)==before and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in PROTECTED.items())
 dump('copied-controls.json',{'cases':cases,'positive_cases':2,'negative_cases':5,'copy_removed':True,'whole_actual_root_unchanged':True,'limits':'Artifact checks only; manifest binds file bytes/membership and directories, not modes. Parent snapshots bind modes/links except root-directory mode.'})
 dump('input-authentication.json',{'selected_source_blobs':17,'source016_blobs':14,'selected_companion_blobs':3,'primary_pdfs':4,'text_derivatives':4,'renders':renders,'primary_access_failures':2,'stable_whole_original_byte_identities':10,'selected_whole_copies':7,'selected_excerpts':3,'tree_identity_without_copy':1,'selected_fixture_members':3,'limits':'Local byte/path/selection authentication only. No fresh remote retrieval, protected source/primary/history semantic reading, extraction, or parent PDF visual attestation. Milne/Snowden web reads lack locally captured original bytes. Catalogue excerpt is byte-bound, not independently reconstructed.'})
 dump('replay.json',{'observed_utc':now,'external_handoff_anchors':ANCHORS,'manifest_enumerated_files':61,'manifest_includes':['FINAL.md','REPORT.md'],'nested_packet_payload_files':59,'whole_root_files':62,'subdirectories':12,'source_blobs':17,'primary_pdfs':4,'stable_named_originals':stable,'selected_original_excerpts':excerpts,'artifact_cases':7,'negative_cases':5,'whole_actual_root_unchanged':True,'limits':'62 total = 59 packet files + three externally anchored top-level envelopes; FINAL and REPORT are also in the 61 manifest entries. Child prose convention does not change actual membership. No mathematical grade; snapshots exclude root-directory mode.'})
 print(json.dumps({'files':62,'manifest_entries':61,'nested_packet_payloads':59,'subdirectories':12,'source_blobs':17,'primary_pdfs':4,'selected_whole_copies':7,'excerpts':3,'artifact_cases':7}))
if __name__=='__main__': main()
