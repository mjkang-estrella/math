#!/usr/bin/env python3
"""Read-only Structural167 archive authentication, not mathematical review."""
import datetime,hashlib,importlib.util,json,stat,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-structural-discovery-r167'
sp=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r161-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'b5fb75067b5eafd71c62a586e4c6a8e273ffff5ced0995c76c872ee09d97d11b','MANIFEST.json':'33e042a7b4f2d443591fb2424129864378883fe22af91c97f4acbf3376355148','REPORT.md':'5aa7288da8dfc5ac33d106884eb6cfb9db177ae4aa16a83d97eebb506a44477b'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'] and len(read(B/'tasks.json')['tasks'])==563
 before=snap(ROOT);mode=stat.S_IMODE(ROOT.stat().st_mode);s=read(O/'task-status.json')['structuredContent'];assert s['status']=='completed' and s['workState']=='result_available' and not s['hasPendingChildRuns'] and not s['hasPendingQuestion'];assert all(sha(ROOT/n)==v and v in s['summary'] for n,v in ANCHORS.items())
 m=read(ROOT/'MANIFEST.json')['payload'];assert len(m['files'])==44 and len(m['directories'])==12 and {n for n,e in before.items() if e['kind']=='file'}==set(m['files'])|set(ANCHORS)
 for n,e in m['files'].items():assert sha(ROOT/n)==e['sha256'] and (ROOT/n).stat().st_size==e['size'] and stat.S_IMODE((ROOT/n).stat().st_mode)==e['mode'] and (ROOT/n).stat().st_nlink==e['nlink']==1
 tree=read(P/'sources/preprints-tree.json');assert sha(P/'sources/preprints-tree.json')=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b' and len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']};source=read(ROOT/'private/source/authentication.json')['objects'];assert len(source)==3
 for e in source:
  q=ROOT/e['local'];data=q.read_bytes();node=entries[e['path']];assert len(data)==e['size']==node['size'] and sha(q)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']==node['sha'];assert e['url']==e['resolved_url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
 stable={};whole=sections=0
 for e in read(ROOT/'private/history/identities.json'):
  p=P/e['path'];q=ROOT/e['local'];assert p.stat().st_size==e['bytes'] and sha(p)==e['sha256'];stable[e['path']]={'path':e['path'],'bytes':e['bytes'],'sha256':e['sha256']}
  if 'selection_bytes' in e:
   lo,hi=e['selection_bytes'];assert q.read_bytes()==p.read_bytes()[lo:hi] and sha(q)==e['selection_sha256'];sections+=1
  else:assert p.read_bytes()==q.read_bytes();whole+=1
 journal=None
 for e in read(ROOT/'private/history/direct-input-identities.json'):
  p=P/e['path']
  if e['path']=='frontier/NEW-TEN-2026-10-14.md':
   prefix=p.read_bytes()[:e['size']];assert hashlib.sha256(prefix).hexdigest()==e['sha256'];lo,hi=e['selection_bytes'];assert (ROOT/e['selection_local']).read_bytes()==prefix[lo:hi] and sha(ROOT/e['selection_local'])==e['selection_sha256'];journal={'child_recorded_bytes':e['size'],'prefix_sha256':e['sha256'],'current_bytes':p.stat().st_size,'child_whole_identity_preserved_as_unchanged_prefix':True};continue
  assert p.stat().st_size==e['size'] and sha(p)==e['sha256'];stable[e['path']]={'path':e['path'],'bytes':e['size'],'sha256':e['sha256']}
 primary=read(ROOT/'private/primary/acquisition.json');assert len(primary)==3
 for e in primary:
  q=ROOT/'private/primary'/(e['name']+'.pdf');assert q.read_bytes().startswith(b'%PDF') and q.stat().st_size==e['bytes'] and sha(q)==e['sha256'] and sha(q.with_suffix('.txt'))==e['text_sha256']
 png=ROOT/'private/primary/bkn-printed12.png';assert png.read_bytes().startswith(b'\x89PNG\r\n\x1a\n')
 ctl=read(ROOT/'private/controls/artifact-controls.json');assert len(ctl['results'])==8 and all(e['expected_accept']==e['observed_accept'] and e['verifier_left_bytes_unchanged'] for e in ctl['results']);fixture=ROOT/'private/controls/copied-fixture';fa=ctl['fixture_detached_anchors'];assert (fixture/'notes/calculation.md').read_bytes()==(ROOT/'notes/02-integrated-calculation.md').read_bytes() and (fixture/'artifact/verify.py').read_bytes()==(ROOT/'artifact/verify.py').read_bytes()
 runs=[]
 for root,anchors in [(ROOT,ANCHORS),(fixture,fa)]:
  state=snap(root);rm=stat.S_IMODE(root.stat().st_mode);args=[sys.executable,'-I','-B',str(ROOT/'artifact/verify.py'),str(root)]
  for n,opt in [('FINAL.md','--final'),('MANIFEST.json','--manifest'),('REPORT.md','--report')]:args.extend([opt,anchors[n]])
  r=subprocess.run(args,cwd=P,capture_output=True,text=True,timeout=30);assert r.returncode==0,(r.stdout,r.stderr);assert snap(root)==state and stat.S_IMODE(root.stat().st_mode)==rm;runs.append({'root':'actual packet' if root==ROOT else 'existing exact selected fixture','returncode':r.returncode,'unchanged':True,'stdout':r.stdout.strip()})
 assert snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==mode and all(sha(P/e['path'])==e['sha256'] for e in stable.values()) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 dump('observed-root.json',{'root':before,'root_mode':mode});dump('replay.json',{'external_handoff_anchors':ANCHORS,'payload_files':44,'whole_root_files':47,'directories_including_root':12,'source_blobs':3,'source_bytes':sum(e['size'] for e in source),'primary_PDF_text_pairs':3,'render_members':1,'whole_original_copies':whole,'exact_selected_history_sections':sections,'stable_named_originals':list(stable.values()),'mutable_journal':journal,'child_artifact_controls':8,'parent_read_only_replays':runs,'root_unchanged':True,'limits':'Artifact checks only. Child finite arithmetic receipt retained, not rerun by parent. No protected source/primary/visual proof reread, independent mathematical grade or exhaustive isolation claim. Identity records and replay stay local unstaged.'});print(json.dumps({'payload':44,'files':47,'directories_including_root':12,'stable_named_originals':len(stable),'whole_originals':whole,'sections':sections,'read_only_replays':2}))
if __name__=='__main__':main()
