#!/usr/bin/env python3
"""Read-only Structural170 no-nominee artifact archive; no mathematical gate."""
import hashlib,importlib.util,json,stat,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-structural-discovery-r170';X=ROOT/'private'
sp=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r161-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'1bdf71dd233e0451ab14f47d573fcf0f5241395ad2357826519453266fdbead2','MANIFEST.json':'ad1f222519d7269295cfbce9eb657512e386110cb92157379ad609aacb5221a9','REPORT.md':'596b76a76cf0a05e893345a89a34eeff97430d197469eaf3c1e0f0d580b0cdfe'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'] and len(read(B/'tasks.json')['tasks'])==572
 before=snap(ROOT);mode=stat.S_IMODE(ROOT.stat().st_mode);s=read(O/'task-status.json')['structuredContent'];assert s['status']=='completed' and s['workState']=='result_available' and not s['hasPendingChildRuns'] and not s['hasPendingQuestion'] and s['pendingApproval'] is None;assert all(sha(ROOT/n)==v and v in s['summary']for n,v in ANCHORS.items());assert read(ROOT/'ANCHORS.json')==ANCHORS
 m=read(ROOT/'MANIFEST.json');assert len(m['files'])==60 and len(m['directories'])==12 and {n for n,e in before.items()if e['kind']=='file'}==set(m['files'])|set(ANCHORS)|{'ANCHORS.json'}
 tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']};source=read(X/'source/objects.json');assert len(source)==8
 for e in source:
  q=ROOT/e['local'];data=q.read_bytes();node=entries[e['path']];assert len(data)==e['size']==node['size'] and sha(q)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['sha']==node['sha'] and e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
 primary=read(X/'primary/acquisition.json');assert len(primary)==9;acquired=[e for e in primary if 'error'not in e];assert len(acquired)==8
 for e in acquired:
  q=X/'primary'/(e['name']+'.pdf');assert q.read_bytes().startswith(b'%PDF') and q.stat().st_size==e['bytes'] and sha(q)==e['sha256'] and q.with_suffix('.txt').is_file()
 for e in read(X/'primary/read-extents.json'):
  p=X/'primary'/(e['name']+'.txt');assert sha(p)==e['text_sha256'] and all(0<=a<=b<=p.stat().st_size for a,b in e['byte_ranges_half_open'])
 for p in (X/'render').glob('*.png'):assert p.read_bytes().startswith(b'\x89PNG\r\n\x1a\n')
 stable=[];direct=read(X/'initial-direct-reads.json');assert len(direct)==6
 for e in direct:
  p=P/e['path'];assert sha(p)==e['sha256'] and e['bytes']==[0,p.stat().st_size] and oct(stat.S_IMODE(p.stat().st_mode))==e['mode'];stable.append({'path':e['path'],'bytes':p.stat().st_size,'sha256':sha(p)})
 history=read(X/'history-selected.json');assert len(history)==4
 for e in history:
  p=P/e['path'];a,b=e['bytes'];assert sha(p)==e['sha256'] and p.read_bytes()[a:b]==e['selected'].encode();stable.append({'path':e['path'],'bytes':p.stat().st_size,'sha256':sha(p)})
 assert (X/'r80-selected-original.md').read_bytes()==(P/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r80/proof-attempt.md').read_bytes();assert (X/'contents-entry.txt').read_bytes()==(P/'sources/CONTENTS.md').read_bytes()[279581:280657]
 for p in [P/'sources/CONTENTS.md',tp,P/'AGENTS.md',P/'sources/upstream.json']:stable.append({'path':str(p.relative_to(P)),'bytes':p.stat().st_size,'sha256':sha(p)})
 def verify(root,anchors):
  args=[sys.executable,'-I','-B',str(ROOT/'verify_packet.py'),str(root)]
  for n,opt in [('FINAL.md','--final-sha256'),('MANIFEST.json','--manifest-sha256'),('REPORT.md','--report-sha256')]:args.extend([opt,anchors[n]])
  r=subprocess.run(args,cwd=P,capture_output=True,text=True,timeout=30);assert r.returncode==0,(r.stdout,r.stderr);return {'returncode':r.returncode,'stdout':r.stdout.strip()}
 actual=verify(ROOT,ANCHORS);c=read(X/'controls/anchors.json');control=verify(X/'controls/selected',{n:c[n.split('.')[0].lower()]for n in ANCHORS});results=read(X/'controls/results.json');assert results['selected_packet']['returncode']==0 and results['wrong_detached_anchor']['returncode']==results['altered_copy']['returncode']==1
 assert (X/'controls/selected/selected.md').read_bytes()==(ROOT/'notes/00-start.md').read_bytes() and (X/'controls/selected/selected.md').read_bytes()!=(X/'controls/altered/selected.md').read_bytes()
 assert snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==mode and all(sha(P/e['path'])==e['sha256']for e in stable) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 dump('observed-root.json',{'root':before,'root_mode':mode});dump('replay.json',{'external_handoff_anchors':ANCHORS,'payload_files':60,'whole_root_files':64,'directories_including_root':12,'source_objects':8,'source_bytes':sum(e['size']for e in source),'primary_PDF_text_pairs':8,'failed_primary_acquisitions':1,'retained_render_members':4,'operative_render_pages_recorded':3,'whole_completed_exception_originals':6,'history_section_originals':4,'stable_named_originals':stable,'actual_read_only_replay':actual,'existing_reduced_fixture_replay':control,'copied_control_cases_recorded':3,'root_unchanged':True,'limits':'Artifact authentication only. Parent read four complete original notes,FINAL/REPORT,private reading account and verifier. Protected source/primary/visual proof bodies not semantically read by parent. Parent observes single links in addition to verifier bytes/modes. Protected identities,replay,navigation and reading account remain local unstaged. No mathematical gate.'});print(json.dumps({'payload':60,'files':64,'source_objects':8,'primary_pairs':8,'stable_named_originals':len(stable),'read_only_replays':2}))
if __name__=='__main__':main()
