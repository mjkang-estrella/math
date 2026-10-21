#!/usr/bin/env python3
"""Read-only Arithmetic135 no-nominee artifact archive."""
import hashlib,importlib.util,json,stat,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-arithmetic-discovery-r135';X=ROOT/'private'
sp=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r161-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'486815d56e3ea3829d0205c9023bc13c1606c2c9f7bb6b33ab70ead6bce3c12a','MANIFEST.json':'52ff8ccfd85442ad67dc61a4f53ef2a4aa417c5da43998558c0597fbffab38de','REPORT.md':'ee1dc632de4413074de9a5fb0cf41a0d067b7628d213ead15da6758d769f8618'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'] and len(read(B/'tasks.json')['tasks'])==571
 before=snap(ROOT);mode=stat.S_IMODE(ROOT.stat().st_mode);s=read(O/'task-status.json')['structuredContent'];assert s['status']=='completed' and s['workState']=='result_available' and not s['hasPendingChildRuns'] and not s['hasPendingQuestion'] and s['pendingApproval'] is None;assert all(sha(ROOT/n)==v and v in s['summary']for n,v in ANCHORS.items())
 m=read(ROOT/'MANIFEST.json');assert len(m['files'])==94 and {n for n,e in before.items()if e['kind']=='file'}=={e['path']for e in m['files']}|set(ANCHORS)
 tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']};source=read(X/'source-identities.json')+read(X/'companion-identities.json');assert len(source)==22
 for e in source:
  q=ROOT/e['local'];data=q.read_bytes();node=entries[e['path']];assert len(data)==e['bytes']==node['size'] and sha(q)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']==node['sha'] and e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
 primary=read(X/'primary/identities.json');assert len(primary)==8;acquired=[e for e in primary if 'error'not in e];assert len(acquired)==6
 for e in acquired:
  q=X/'primary'/(e['name']+'.pdf');assert q.read_bytes().startswith(b'%PDF') and q.stat().st_size==e['bytes'] and sha(q)==e['sha256'] and sha(q.with_suffix('.txt'))==e['text_sha256']
 assert (X/'primary/wronski-page11.png').read_bytes().startswith(b'\x89PNG\r\n\x1a\n')
 stable=[];selected=read(X/'selected-originals.json');assert len(selected)==19
 for e in selected:
  p=P/e['original'];q=ROOT/e['local'];assert q.read_bytes()==p.read_bytes()[e['start']:e['end']] and sha(q)==e['selection_sha256']
  if e['original']!='frontier/NEW-TEN-2026-10-14.md':
   assert sha(p)==e['capture_full_sha256'] and ('initial_full_sha256' in e or e['original'] in ['AGENTS.md','sources/upstream.json']) and e.get('initial_full_sha256',sha(p))==sha(p);stable.append({'path':e['original'],'bytes':p.stat().st_size,'sha256':sha(p)})
 stable.append({'path':'sources/preprints-tree.json','bytes':tp.stat().st_size,'sha256':sha(tp)})
 def verify(root,anchors):
  args=[sys.executable,'-I','-B',str(X/'verify_packet.py'),str(root)]
  for n,opt in [('FINAL.md','--final-sha256'),('MANIFEST.json','--manifest-sha256'),('REPORT.md','--report-sha256')]:args.extend([opt,anchors[n]])
  r=subprocess.run(args,cwd=P,capture_output=True,text=True,timeout=30);assert r.returncode==0,(r.stdout,r.stderr);return {'returncode':r.returncode,'stdout':r.stdout.strip()}
 actual=verify(ROOT,ANCHORS);controls=read(X/'control-results.json');assert len(controls['checks'])==2 and controls['original_unchanged'];clean=X/'controls/clean';modified=X/'controls/modified';control=verify(clean,controls['checks'][0]['anchors']);assert (clean/'notes/start.md').read_bytes()==(ROOT/'notes/start.md').read_bytes() and (clean/'MANIFEST.json').read_bytes()==(modified/'MANIFEST.json').read_bytes() and (clean/'notes/start.md').read_bytes()!=(modified/'notes/start.md').read_bytes() and controls['checks'][1]['returncode']==1
 assert snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==mode and all(sha(P/e['path'])==e['sha256']for e in stable) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 dump('observed-root.json',{'root':before,'root_mode':mode});dump('replay.json',{'external_handoff_anchors':ANCHORS,'payload_files':94,'whole_root_files':97,'directories_excluding_root':18,'source_objects':22,'source_bytes':sum(e['bytes']for e in source),'primary_PDF_text_pairs':6,'failed_primary_acquisitions':2,'render_members':1,'selected_original_copies':19,'stable_named_originals':stable,'actual_read_only_replay':actual,'existing_reduced_fixture_replay':control,'copied_control_cases_recorded':2,'root_unchanged':True,'limits':'Artifact authentication only. Parent read six complete original mathematical notes,FINAL/REPORT,private reading account and verifier. Protected source/primary/visual proof bodies not semantically read by parent. Finite diagnostic script not rerun. Parent observes modes/single links in addition to verifier membership/bytes. Protected identities,replay,navigation and private reading accounts remain local unstaged.'});print(json.dumps({'payload':94,'files':97,'source_objects':22,'primary_pairs':6,'stable_named_originals':len(stable),'read_only_replays':2}))
if __name__=='__main__':main()
