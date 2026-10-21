#!/usr/bin/env python3
"""Read-only Structural168 no-nominee archive authentication."""
import hashlib,importlib.util,json,stat,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-structural-discovery-r168'
sp=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r161-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'65eef292397048f5b0b6979aea30d0acb8e2be121711fa8069dee25f8dad8898','MANIFEST.json':'362d2ac867b161f9cfab6399986652e54a1a542812260317cb725150976f1173','REPORT.md':'25e1f6c256eb616a65279619e17989ba94c1b75dd34cc096eeeb15fee6896cb3'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'] and len(read(B/'tasks.json')['tasks'])==567
 before=snap(ROOT);mode=stat.S_IMODE(ROOT.stat().st_mode);s=read(O/'task-status.json')['structuredContent'];assert s['status']=='completed' and s['workState']=='result_available' and not s['hasPendingChildRuns'] and not s['hasPendingQuestion'];assert all(sha(ROOT/n)==v and v in s['summary'] for n,v in ANCHORS.items())
 m=read(ROOT/'MANIFEST.json')['payload'];assert len(m['files'])==78 and len(m['directories'])==17 and {n for n,e in before.items() if e['kind']=='file'}=={e['path'] for e in m['files']}|set(ANCHORS)
 for e in m['files']:assert sha(ROOT/e['path'])==e['sha256'] and (ROOT/e['path']).stat().st_size==e['size'] and stat.S_IMODE((ROOT/e['path']).stat().st_mode)==e['mode']
 tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']};source=read(ROOT/'private/source/authentication.json');assert len(source)==27
 for e in source:
  q=ROOT/e['local'];data=q.read_bytes();node=entries[e['path']];assert len(data)==e['size']==node['size'] and sha(q)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']==node['sha'] and e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
 stable={};whole=0;journal=None
 for e in read(ROOT/'private/direct-reads.json'):
  p=P/e['path'];q=ROOT/e['local'];data=p.read_bytes();assert q.read_bytes()==data[e['start']:e['end']]
  if e['path']=='frontier/NEW-TEN-2026-10-14.md':assert hashlib.sha256(data[:e['total']]).hexdigest()==e['sha256'];journal={'child_recorded_bytes':e['total'],'child_recorded_sha256':e['sha256'],'matched_as_current_prefix':True};continue
  assert len(data)==e['total'] and sha(p)==e['sha256'];stable[e['path']]={'path':e['path'],'bytes':e['total'],'sha256':e['sha256']};whole+=e['start']==0 and e['end']==e['total']
 for e in read(ROOT/'private/history-selections.json'):
  p=P/e['path'];q=ROOT/'private'/('i22-'+str(e['start'])+'-'+str(e['end'])+'.md');assert sha(p)==e['original_sha256'] and sha(q)==e['selected_sha256'] and q.read_bytes()==p.read_bytes()[e['start']:e['end']];stable[e['path']]={'path':e['path'],'bytes':p.stat().st_size,'sha256':e['original_sha256']}
 stable['sources/preprints-tree.json']={'path':'sources/preprints-tree.json','bytes':tp.stat().st_size,'sha256':sha(tp)}
 primary=read(ROOT/'private/primary/acquisition.json');assert len(primary)==3
 for e in primary:
  q=ROOT/'private/primary'/(e['name']+'.pdf');assert q.read_bytes().startswith(b'%PDF') and q.stat().st_size==e['bytes'] and sha(q)==e['pdf_sha256'] and sha(q.with_suffix('.txt'))==e['text_sha256']
 pngs=list((ROOT/'private/primary').glob('*.png'));assert len(pngs)==4 and all(p.read_bytes().startswith(b'\x89PNG\r\n\x1a\n') for p in pngs)
 ctl=read(ROOT/'private/copied-control-results.json');assert len(ctl['results'])==8 and all(e['accepted']==e['expected'] and e['read_only'] for e in ctl['results']);fixture=ROOT/'private/copied-control';assert (fixture/'notes/calculation.md').read_bytes()==(ROOT/'notes/02-integrated-calculation.md').read_bytes() and (fixture/'verify_packet.py').read_bytes()==(ROOT/'verify_packet.py').read_bytes()
 runs=[]
 for root,anchors in [(ROOT,ANCHORS),(fixture,ctl['anchors'])]:
  state=snap(root);rm=stat.S_IMODE(root.stat().st_mode);args=[sys.executable,'-I','-B',str(ROOT/'verify_packet.py'),str(root)]
  for n,opt in [('FINAL.md','--final'),('MANIFEST.json','--manifest'),('REPORT.md','--report')]:args.extend([opt,anchors[n]])
  r=subprocess.run(args,cwd=P,capture_output=True,text=True,timeout=30);assert r.returncode==0,(r.stdout,r.stderr);assert snap(root)==state and stat.S_IMODE(root.stat().st_mode)==rm;runs.append({'root':'actual packet' if root==ROOT else 'existing clean reduced fixture','returncode':r.returncode,'stdout':r.stdout.strip(),'unchanged':True})
 assert snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==mode and all(sha(P/e['path'])==e['sha256'] for e in stable.values()) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 dump('observed-root.json',{'root':before,'root_mode':mode});dump('replay.json',{'external_handoff_anchors':ANCHORS,'payload_files':78,'whole_root_files':81,'directories_including_root':17,'source_objects':27,'source_bytes':sum(e['size'] for e in source),'primary_PDF_text_pairs':3,'render_members':4,'whole_direct_original_copies':whole,'exact_direct_byte_spans':2,'historical_byte_sections':2,'stable_named_originals':list(stable.values()),'mutable_journal':journal,'child_integrity_controls':8,'parent_read_only_replays':runs,'root_unchanged':True,'limits':'Artifact authentication only. Parent reads complete original notes/code, not protected source/primary/visual proof bodies. Finite exact diagnostics retained but not rerun. Protected identity inventory/replay remain local unstaged; no mathematical gates or perfect-isolation claim.'});print(json.dumps({'payload':78,'files':81,'source_objects':27,'stable_named_originals':len(stable),'read_only_replays':2}))
if __name__=='__main__':main()
