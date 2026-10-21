#!/usr/bin/env python3
"""Arithmetic131 handoff authentication; existing fixture replays, no math gate."""
import datetime,hashlib,importlib.util,json,stat,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-arithmetic-discovery-r131'
sp=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r156-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'envelopes/FINAL.md':'51bb14c3cfc9ade21c723c83be1ae82ba571790a938d7d6ed92ce74ef4570bf9','envelopes/MANIFEST.json':'7843fda8e4af21f3d9a1c4eff263ef63848a3067026892025d406352eafa6dd2','envelopes/REPORT.md':'485a43351526bc937fcc4233e1c6704f66d72adf6997251ab808d55e36d94e74'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'] and len(read(B/'tasks.json')['tasks'])==557
 before=snap(ROOT);rm=stat.S_IMODE(ROOT.stat().st_mode);st=read(O/'task-status.json')['structuredContent'];assert st['status']=='completed' and st['workState']=='result_available' and not st['hasPendingChildRuns'] and not st['hasPendingQuestion'];handoff=read(O/'terminal-handoff.json');assert handoff['threadId']==st['childThreadId'] and handoff['items'][0]['position']==139 and not handoff['items'][0]['textTruncated'];assert all(sha(ROOT/n)==v and v in handoff['items'][0]['text'] for n,v in ANCHORS.items())
 m=read(ROOT/'envelopes/MANIFEST.json');assert len(m['files'])==56 and len(m['directories'])==13;assert {n for n,e in before.items() if e['kind']=='file'}==set(m['files'])|set(ANCHORS)
 for n,e in m['files'].items():
  q=ROOT/n;assert q.stat().st_size==e['size'] and sha(q)==e['sha256'] and q.stat().st_nlink==1
 tree=read(P/'sources/preprints-tree.json');assert sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b' and len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']};source=read(ROOT/'private/source/authentication.json');assert len(source)==10
 for e in source:
  q=ROOT/e['local'];data=q.read_bytes();node=entries[e['path']];assert len(data)==e['size']==node['size'] and sha(q)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['sha']==node['sha'];assert e['url_acquired']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
 stable=[];whole=selected=0
 for e in read(ROOT/'private/history/incoming-originals.json'):
  p=P/e['path'];assert p.stat().st_size==e['bytes'] and sha(p)==e['sha256'];stable.append({'path':e['path'],'bytes':e['bytes'],'sha256':e['sha256']})
  if 'selected_copy' in e:
   if e['selection']=='whole original':body=p.read_bytes();whole+=1
   else:
    lines=p.read_bytes().splitlines(keepends=True);body=b'\n'.join(b''.join(lines[lo-1:hi]) for lo,hi in e['ranges_inclusive']);selected+=1
   assert (ROOT/e['selected_copy']).read_bytes()==body
 assert len(stable)==13 and whole==9 and selected==3
 primary=read(ROOT/'private/primary/acquisition.json');assert len(primary)==3
 for e in primary:
  q=ROOT/'private/primary'/(e['name']+'.pdf');assert q.stat().st_size==e['bytes'] and sha(q)==e['sha256'] and q.read_bytes().startswith(b'%PDF') and e['extraction_returncode']==0 and q.with_suffix('.txt').stat().st_size>0
 renders=list((ROOT/'private/primary').glob('*-page*.png'));assert len(renders)==2 and all(q.read_bytes().startswith(b'\x89PNG\r\n\x1a\n') for q in renders)
 ctl=read(ROOT/'notes/artifact-controls.json');assert len(ctl['results'])==6 and all(e['expected_acceptance']==e['observed_acceptance'] for e in ctl['results']);fixture=ROOT/'controls/baseline';assert all((fixture/n).read_bytes()==(ROOT/n).read_bytes() for n in ['notes/reduction-boundary.md','tools/verify.py']);diag=read(ROOT/'notes/finite-diagnostic.json');assert len(diag['tuple_cases'])==16 and diag['recurrence_cases']==4352
 runs=[]
 for root,anchors,project in [(ROOT,ANCHORS,True),(fixture,ctl['anchors'],False)]:
  state=snap(root);mode=stat.S_IMODE(root.stat().st_mode);cmd=[sys.executable,'-I','-B',str(ROOT/'tools/verify.py'),str(root),anchors['envelopes/FINAL.md'],anchors['envelopes/MANIFEST.json'],anchors['envelopes/REPORT.md']]+(['--project',str(P)] if project else []);r=subprocess.run(cmd,capture_output=True,text=True,timeout=30);assert r.returncode==0,(r.stdout,r.stderr);assert snap(root)==state and stat.S_IMODE(root.stat().st_mode)==mode;runs.append({'root':'actual packet with project identity checks' if root==ROOT else 'existing selected fixture','returncode':r.returncode,'unchanged':True,'stdout':r.stdout.strip()})
 assert snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==rm and all(sha(P/e['path'])==e['sha256'] for e in stable) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 dump('observed-root.json',{'root':before,'root_mode':rm});dump('replay.json',{'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'external_handoff_anchors':ANCHORS,'external_anchor_recovery':'Completed-child messages position139; shorter position140 is task_status summary. No child restart.','payload_files':56,'whole_root_files':59,'directories_excluding_root':13,'source_blobs':10,'source_bytes':sum(e['size'] for e in source),'primary_PDF_text_pairs':3,'render_members':2,'stable_named_originals':stable,'whole_original_copies':9,'selected_original_excerpts':3,'child_recorded_artifact_cases':6,'parent_read_only_replays':runs,'finite_tuple_cases':16,'finite_recurrence_cases':4352,'finite_diagnostic_not_rerun':True,'new_parent_tamper_suite':False,'whole_actual_root_unchanged':True,'limits':'Artifact integrity only; no mathematical gate or fresh primary/visual proof reading. Manifest binds exact file/directory membership and file bytes. Verifier checks single links; modes/timestamps/atomicity are not certified. Parent separately observed full tree/modes.'})
 print(json.dumps({'payload':56,'files':59,'source_blobs':10,'primary_pairs':3,'renders':2,'stable_originals':13,'read_only_replays':2}))
if __name__=='__main__':main()
