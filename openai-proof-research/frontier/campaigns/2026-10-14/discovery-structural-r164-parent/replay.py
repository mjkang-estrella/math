#!/usr/bin/env python3
"""Structural164 intake authentication and existing read-only fixture replay."""
import datetime,hashlib,importlib.util,json,stat,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-structural-discovery-r164'
sp=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r156-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'9b118b576d3789d4131989d9e9e8b8bfdb4fd68d09b657d29c413d5507a01032','MANIFEST.json':'a9949ce25aa24bc9eb826dc81a6b5277ca7275dd09b89d338e03280f01535fbb','REPORT.md':'8db58471e4ab79a5878578960d862ed3be3ecfd0acfdc37c983ee1fd4b4e4c6e'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'] and len(read(B/'tasks.json')['tasks'])==555
 before=snap(ROOT);rm=stat.S_IMODE(ROOT.stat().st_mode);st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and st['workState']=='result_available' and not st['hasPendingChildRuns'] and not st['hasPendingQuestion'];assert all(sha(ROOT/n)==v and v in st['summary'] for n,v in ANCHORS.items());m=read(ROOT/'MANIFEST.json');assert len(m['files'])==76 and len(m['directories'])==20 and rm==m['directories']['.'];assert {n for n,e in before.items() if e['kind']=='file'}==set(m['files'])|set(ANCHORS)
 for n,e in m['files'].items():assert (ROOT/n).stat().st_size==e['bytes'] and sha(ROOT/n)==e['sha256'] and stat.S_IMODE((ROOT/n).stat().st_mode)==e['mode'] and (ROOT/n).stat().st_nlink==1
 tree=read(P/'sources/preprints-tree.json');assert sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b' and len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']};source=read(ROOT/'private/source/authentication.json');assert len(source)==19
 for e in source:
  q=ROOT/e['copy'];data=q.read_bytes();node=entries[e['canonical_path']];assert len(data)==e['size']==node['size'] and sha(q)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']==node['sha'];assert e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['canonical_path']
 stable=[];copied=0
 for e in read(ROOT/'private/history/incoming-original-identities.json'):
  p=P/e['original_path'];assert p.stat().st_size==e['original_bytes'] and sha(p)==e['original_sha256'];stable.append({'path':e['original_path'],'bytes':e['original_bytes'],'sha256':e['original_sha256']})
  if e['original_path'].startswith(str(B.relative_to(P))+'/') and 'r163' in e['original_path']:
   q=ROOT/'private/history'/e['original_path'].removeprefix(str(B.relative_to(P))+'/').replace('/','__');assert q.read_bytes()==p.read_bytes();copied+=1
 assert len(stable)==11 and copied==5;assert (ROOT/'private/history/r44-preliminary-dp-screen.md').read_bytes()==(B/'fresh-structural-discovery-r44/preliminary-dp-screen.md').read_bytes();assert (ROOT/'private/history/acceptance-section.txt').read_bytes() in (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes()
 primary=read(ROOT/'private/primary/acquisition.json');assert len(primary)==5
 for e in primary:
  q=ROOT/'private/primary'/(e['name']+'.pdf');assert q.stat().st_size==e['bytes'] and sha(q)==e['sha256'] and q.read_bytes().startswith(b'%PDF') and sha(q.with_suffix('.txt'))==e['text_sha256']
 e=read(ROOT/'private/primary/freedman-recovery.json');q=ROOT/'private/primary/freedman-1975-mirror.pdf';assert q.stat().st_size==e['bytes'] and sha(q)==e['sha256'] and sha(q.with_suffix('.txt'))==e['text_sha256'];assert len(list(q.parent.glob('freedman-page-*.png')))==4 and 'failure' in read(ROOT/'private/primary/freedman-acquisition.json')
 ctl=read(ROOT/'seal/control-receipt.json');assert len(ctl['controls'])==ctl['control_count']==9 and all(e['expected_accept']==e['accepted'] for e in ctl['controls']);fixture=ROOT/'seal/selected-control';assert sha(fixture/'original/calculation.md')==sha(ROOT/'notes/02-integrated-calculations.md') and sha(fixture/'protected/source.tex')==sha(ROOT/'private/source/list/sections/02-preliminaries.tex') and sha(fixture/'tools/verify_packet.py')==sha(ROOT/'tools/verify_packet.py');diag=read(ROOT/'private/variance-diagnostic.json');assert diag['cases']==27 and diag['conditional_contexts_total']==6993
 runs=[]
 for root,anchors in [(ROOT,ANCHORS),(fixture,ctl['detached_fixture_anchors'])]:
  state=snap(root);mode=stat.S_IMODE(root.stat().st_mode);r=subprocess.run([sys.executable,'-I','-B',str(ROOT/'tools/verify_packet.py'),'--root',str(root),'--final-sha256',anchors['FINAL.md'],'--manifest-sha256',anchors['MANIFEST.json'],'--report-sha256',anchors['REPORT.md']],capture_output=True,text=True,timeout=30);assert r.returncode==0,(r.stdout,r.stderr);assert snap(root)==state and stat.S_IMODE(root.stat().st_mode)==mode;runs.append({'root':'actual packet' if root==ROOT else 'existing selected fixture','returncode':r.returncode,'unchanged':True,'stdout':r.stdout.strip()})
 assert snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==rm and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 dump('observed-root.json',{'root':before,'root_mode':rm});dump('replay.json',{'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'external_handoff_anchors':ANCHORS,'payload_files':76,'whole_root_files':79,'directories_including_root':20,'source_blobs':19,'source_bytes':sum(e['size'] for e in source),'primary_PDF_text_pairs':6,'render_members':4,'recorded_failed_primary_response':1,'stable_named_originals':stable,'required_completed_whole_copies':5,'other_whole_history_copy':1,'selected_i22_passage_range_equivalence_not_asserted':True,'child_recorded_artifact_cases':9,'parent_read_only_replays':runs,'finite_diagnostic_cases':27,'finite_diagnostic_contexts':6993,'finite_diagnostic_not_rerun':True,'new_parent_tamper_suite':False,'whole_actual_root_unchanged':True,'limits':'Artifact integrity only; no independent mathematical gate or fresh primary/visual proof reading. Manifest binds exact file/directory bytes/membership/modes including root; parent separately checked actual single links.'})
 print(json.dumps({'payload':76,'files':79,'directories_including_root':20,'source_blobs':19,'primary_pairs':6,'renders':4,'stable_originals':11,'read_only_replays':2}))
if __name__=='__main__':main()
