#!/usr/bin/env python3
"""Structural165 authentication and existing read-only fixture replay; no math gate."""
import datetime,hashlib,importlib.util,json,stat,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-structural-discovery-r165'
sp=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r156-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'6ca6b11d93b5540c89dc1f8be0ed0e97d522cc63b05e49ede8c09a2ec6789ee8','MANIFEST.json':'99164897b77b77db7f2cd2f90a195feae47ecde33453910f1e55b4fe3e830336','REPORT.md':'f9e038cfdabb5ff5588fff3cae49a6d77ec7056febfad0db2945e43656468615'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'] and len(read(B/'tasks.json')['tasks'])==558
 before=snap(ROOT);rm=stat.S_IMODE(ROOT.stat().st_mode);st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and st['workState']=='result_available' and not st['hasPendingChildRuns'] and not st['hasPendingQuestion'];assert all(sha(ROOT/n)==v and v in st['summary'] for n,v in ANCHORS.items())
 m=read(ROOT/'MANIFEST.json');assert len(m['files'])==72 and len(m['directories'])==14 and rm==m['directories']['.'];assert {n for n,e in before.items() if e['kind']=='file'}==set(m['files'])|set(ANCHORS)
 for n,e in m['files'].items():
  q=ROOT/n;assert q.stat().st_size==e['size'] and sha(q)==e['sha256'] and stat.S_IMODE(q.stat().st_mode)==e['mode'] and q.stat().st_nlink==1
 tree=read(P/'sources/preprints-tree.json');assert sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b' and len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']};source=read(ROOT/'private/source/authentication.json');assert len(source)==23
 for e in source:
  q=ROOT/'private/source'/e['path'].split('/build/',1)[1];data=q.read_bytes();node=entries[e['path']];assert len(data)==e['size']==node['size'] and sha(q)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['sha']==e['git_blob_verified']==node['sha'];assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
 stable=[];whole=selected=0
 for e in read(ROOT/'private/history/original-identities.json'):
  p=P/e['original_path'];q=ROOT/e['selected_copy']
  if 'selection_bytes_half_open' in e:
   lo,hi=e['selection_bytes_half_open'];assert p.read_bytes()[lo:hi]==q.read_bytes() and sha(q)==e['selected_copy_sha256'];continue
  assert p.stat().st_size==e['original_size'] and sha(p)==e['original_sha256'];stable.append({'path':e['original_path'],'bytes':e['original_size'],'sha256':e['original_sha256']})
  if e['selection']=='entire original':body=p.read_bytes();whole+=1
  else:lines=p.read_bytes().splitlines(keepends=True);body=b''.join(lines[44:58]+lines[339:370]);selected+=1
  assert q.read_bytes()==body and sha(q)==e['selected_copy_sha256']
 assert len(stable)==8 and whole==7 and selected==1
 for n,expected in [('AGENTS.md','e9ab951853e1607e8d125adb5609a89214a46bb655fda39874257b8210093e7e'),('sources/upstream.json','3784eb61f1efa141ed49d00c5d13a5206502c4081759abff4f64c99183b5f30c'),('sources/preprints-tree.json','eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b')]:assert sha(P/n)==expected;stable.append({'path':n,'bytes':(P/n).stat().st_size,'sha256':expected})
 primary=read(ROOT/'private/primary/acquisition.json');success=[e for e in primary if 'failure' not in e];assert len(success)==5 and len(primary)==6 and '403' in next(e['failure'] for e in primary if 'failure' in e)
 for e in success:
  q=ROOT/'private/primary'/(e['name']+'.pdf');assert q.stat().st_size==e['bytes'] and sha(q)==e['sha256'] and q.read_bytes().startswith(b'%PDF') and sha(q.with_suffix('.txt'))==e['text_sha256']
 renders=list((ROOT/'private/primary').glob('*.png'));assert len(renders)==5 and all(q.read_bytes().startswith(b'\x89PNG\r\n\x1a\n') for q in renders)
 ctl=read(ROOT/'private/controls/results.json');assert len(ctl['controls'])==9 and all(e['expected']==e['observed'] for e in ctl['controls']);fixture=ROOT/'private/controls/selected-fixture';assert all((fixture/n).read_bytes()==(ROOT/n).read_bytes() for n in ['notes/02-integrated-calculation.md','private/source/main.tex','tools/verify_packet.py']);diag=read(ROOT/'notes/pair-diagnostic.json');assert diag['restriction_cases']==567 and diag['normalizer_and_domination_cases']==233 and diag['pointwise_pair_comparisons']==8388
 runs=[]
 for root,anchors in [(ROOT,ANCHORS),(fixture,ctl['fixture_own_detached_anchors'])]:
  state=snap(root);mode=stat.S_IMODE(root.stat().st_mode);r=subprocess.run([sys.executable,'-I','-B',str(ROOT/'tools/verify_packet.py'),str(root),'--final-sha256',anchors['FINAL.md'],'--manifest-sha256',anchors['MANIFEST.json'],'--report-sha256',anchors['REPORT.md']],capture_output=True,text=True,timeout=30);assert r.returncode==0,(r.stdout,r.stderr);assert snap(root)==state and stat.S_IMODE(root.stat().st_mode)==mode;runs.append({'root':'actual packet' if root==ROOT else 'existing selected fixture','returncode':r.returncode,'unchanged':True,'stdout':r.stdout.strip()})
 assert snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==rm and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 dump('observed-root.json',{'root':before,'root_mode':rm});dump('replay.json',{'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'external_handoff_anchors':ANCHORS,'payload_files':72,'whole_root_files':75,'directories_including_root':14,'source_blobs':23,'source_bytes':sum(e['size'] for e in source),'primary_PDF_text_pairs':5,'render_members':5,'recorded_failed_primary_response':1,'stable_named_originals':stable,'incoming_history_whole_identities':8,'whole_history_copies':7,'exact_selected_history_excerpts':1,'child_recorded_artifact_cases':9,'parent_read_only_replays':runs,'finite_restriction_cases':567,'finite_qualifying_cases':233,'finite_pair_comparisons':8388,'finite_diagnostic_not_rerun':True,'new_parent_tamper_suite':False,'whole_actual_root_unchanged':True,'limits':'Artifact integrity only; no mathematical gate or fresh primary/visual proof reading. Manifest binds exact file/directory bytes,membership,modes including root; verifier checks single links and rejects symlinks. No atomicity/rights/priority certificate.'})
 print(json.dumps({'payload':72,'files':75,'source_blobs':23,'primary_pairs':5,'renders':5,'stable_originals':11,'read_only_replays':2}))
if __name__=='__main__':main()
