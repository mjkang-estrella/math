#!/usr/bin/env python3
"""Read-only T054L136 author-packet intake; mathematical gates remain open."""
import hashlib,importlib.util,json,stat,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-arithmetic-discovery-r136';X=ROOT/'private'
sp=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r161-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'bab1195e237be196619cee66fb91eb8c6ef0f82354c34bcee4cb8d42841adedf','MANIFEST.json':'e254a814525e744bc9d08782af3419b44fc0b4904b155781ee2c1f3207abb8b5','REPORT.md':'45c42a11b87278d573a5f009ffacfd64b6d8292047bb9b80985f9253d873f75a'}
FROZEN='cde199a706104ed0db542704b0470d451ce5e11bd7ff0cc74d62df68130b4a77';PROOF='6c9ea784ead7d96835a69a3a41d15f89ec3a13ac4faa83b342a6adcc76c53446'
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'] and len(read(B/'tasks.json')['tasks'])==575
 before=snap(ROOT);mode=stat.S_IMODE(ROOT.stat().st_mode);s=read(O/'task-status.json')['structuredContent'];assert s['status']=='completed' and s['workState']=='result_available' and not s['hasPendingChildRuns'] and not s['hasPendingQuestion'] and s['pendingApproval'] is None;assert all(sha(ROOT/n)==v and v in s['summary']for n,v in ANCHORS.items());assert sha(ROOT/'FROZEN.md')==FROZEN and sha(ROOT/'notes/author-proof.md')==PROOF and read(X/'freeze.json')['sha256']==FROZEN
 m=read(ROOT/'MANIFEST.json');assert len(m['files'])==77 and m['frozen_sha256']==FROZEN and {n for n,e in before.items()if e['kind']=='file'}=={e['path']for e in m['files']}|set(ANCHORS)
 tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']};source=read(X/'source-identities.json');assert len(source)==9
 for e in source:
  q=ROOT/e['local'];data=q.read_bytes();node=entries[e['path']];assert len(data)==e['size']==node['size'] and sha(q)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['sha']==node['sha'] and e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
 records=[]
 for n in ['identities.json','identities-2.json','identities-3.json','identities-4.json','identities5.json','identities6.json']:
  v=read(X/'primary'/n);records.extend(v if isinstance(v,list)else[v])
 primary=[e for e in records if 'sha256'in e];assert len(primary)==10
 for e in primary:
  q=X/'primary'/(e['name']+'.pdf');assert q.read_bytes().startswith(b'%PDF') and q.stat().st_size==e.get('size',e.get('bytes')) and sha(q)==e['sha256'] and q.with_suffix('.txt').is_file()
  if 'text_sha256'in e:assert sha(q.with_suffix('.txt'))==e['text_sha256']
 assert (X/'primary/blmpns-page121.png').read_bytes().startswith(b'\x89PNG\r\n\x1a\n')
 stable={};direct=read(X/'direct-reads.json');assert len(direct)==8
 for e in direct:
  p=P/e['path'];assert sha(p)==e['sha256'] and p.stat().st_size==e['bytes'] and oct(stat.S_IMODE(p.stat().st_mode))==e['mode'] and p.read_bytes()==(P/e['copy']).read_bytes();stable[e['path']]={'path':e['path'],'bytes':p.stat().st_size,'sha256':sha(p)}
 history=[json.loads(v)for v in (X/'selected-history.jsonl').read_text().splitlines()];assert len(history)==2
 for e in history:
  p=P/e['path'];a,b=e['bytes'];q=ROOT/e['local'];assert sha(p)==e['sha256'] and p.stat().st_size==e['total'] and oct(stat.S_IMODE(p.stat().st_mode))==e['mode'] and q.read_bytes()==p.read_bytes()[a:b] and sha(q)==e['selected_sha256'];stable[e['path']]={'path':e['path'],'bytes':p.stat().st_size,'sha256':sha(p)}
 for e in read(X/'direct-instruction-identities.json'):
  p=P/e['path']
  if e['path']=='frontier/NEW-TEN-2026-10-14.md':assert hashlib.sha256(p.read_bytes()[:e['bytes']]).hexdigest()==e['sha256']
  else:assert sha(p)==e['sha256'] and p.stat().st_size==e['bytes'];stable[e['path']]={'path':e['path'],'bytes':p.stat().st_size,'sha256':sha(p)}
 stable['sources/preprints-tree.json']={'path':'sources/preprints-tree.json','bytes':tp.stat().st_size,'sha256':sha(tp)}
 assert (X/'acceptance.txt').read_bytes()==(P/'frontier/NEW-TEN-2026-10-14.md').read_bytes()[4801:6347]
 args=[sys.executable,'-I','-B',str(ROOT/'verify_packet.py'),str(ROOT),*[ANCHORS[n]for n in ['FINAL.md','MANIFEST.json','REPORT.md']]];r=subprocess.run(args,cwd=P,capture_output=True,text=True,timeout=30);assert r.returncode==0,(r.stdout,r.stderr)
 c=read(X/'controls/control.json');assert c['clean_matches'] and not c['changed_matches'] and sha(X/'controls/clean.copy')==c['expected_sha256']==FROZEN and sha(X/'controls/changed.copy')==c['changed_sha256']!=FROZEN
 assert snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==mode and all(sha(P/e['path'])==e['sha256']for e in stable.values()) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 dump('observed-root.json',{'root':before,'root_mode':mode});dump('replay.json',{'external_handoff_anchors':ANCHORS,'frozen_sha256':FROZEN,'author_proof_sha256':PROOF,'payload_files':77,'whole_root_files':80,'directories_including_root':1+sum(e['kind']=='dir'for e in before.values()),'source_objects':9,'source_bytes':sum(e['size']for e in source),'primary_PDF_text_pairs':10,'failed_acquisition_records':len(records)-len(primary),'render_members':1,'whole_completed_exception_originals':8,'history_section_originals':2,'stable_named_originals':list(stable.values()),'actual_read_only_replay':{'returncode':r.returncode,'stdout':r.stdout.strip()},'copied_control_clean_and_changed_hashes_independently_checked':True,'root_unchanged':True,'limits':'Artifact authentication only. Parent read complete frozen scope,author proof,self-check,feasibility,start,local diagnostic code,FINAL/REPORT,private reading account and verifier. Protected source/primary/visual proof bodies not semantically read by parent. Author diagnostic code not rerun. Verifier does not bind directory census/envelope modes; parent observes whole-root modes,single links and directories. Private identity inventory,replay and reading records remain local unstaged. Parent P1 is an open mathematical objection,not a gate.'});print(json.dumps({'payload':77,'files':80,'source_objects':9,'primary_pairs':10,'stable_named_originals':len(stable),'read_only_replays':1,'frozen_unchanged':True}))
if __name__=='__main__':main()
