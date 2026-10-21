#!/usr/bin/env python3
"""Read-only Structural171 artifact archive and existing copied-control replay."""
import hashlib,importlib.util,json,stat,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-structural-discovery-r171';X=ROOT/'private'
sp=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r161-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'1e1823712e99b5ba035ed4b7993ad15bc9291f06962a19ca2a4b69b8f5183c51','MANIFEST.json':'01a204a8b82d8b8293b66a9284a6988d47111eb4ca39dc6ae63b7158f1c43206','REPORT.md':'35ac2d2d361f39077c0072549b2392346799b63571cb7ee590c0b50a93b27035'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'] and len(read(B/'tasks.json')['tasks'])==574
 before=snap(ROOT);mode=stat.S_IMODE(ROOT.stat().st_mode);s=read(O/'task-status.json')['structuredContent'];assert s['status']=='completed' and s['workState']=='result_available' and not s['hasPendingChildRuns'] and not s['hasPendingQuestion'] and s['pendingApproval'] is None;assert all(sha(ROOT/n)==v and v in s['summary']for n,v in ANCHORS.items())
 m=read(ROOT/'MANIFEST.json');assert len(m['files'])==69 and len(m['directories'])==12 and {n for n,e in before.items()if e['kind']=='file'}==set(m['files'])|set(ANCHORS)
 tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']};source=read(X/'source-objects.json');assert len(source)==11
 for e in source:
  q=P/e['local'];data=q.read_bytes();node=entries[e['path']];assert len(data)==e['bytes']==node['size'] and sha(q)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['git_blob']==node['sha'] and e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
 primary=read(X/'primary/acquisitions.json')+read(X/'primary/later-acquisitions.json');k=read(X/'primary/kim-v2-acquisition.json');primary.append({'id':'2508.11725v2',**k});assert len(primary)==7
 for e in primary:
  q=X/'primary'/(e['id']+'.pdf');assert q.read_bytes().startswith(b'%PDF') and q.stat().st_size==e['bytes'] and sha(q)==e['sha256'] and q.with_suffix('.txt').is_file()
 e=read(X/'primary/demaine-langerman-version.json');q=X/'primary/demaine-langerman-slop.texlish';assert q.stat().st_size==e['bytes'] and sha(q)==e['sha256'] and e['commit']=='5309313e662377d2efb353acba454859469606bd'
 for p in (X/'render').glob('*.png'):assert p.read_bytes().startswith(b'\x89PNG\r\n\x1a\n')
 stable=[];direct=read(X/'direct-reads.json');assert len(direct)==6
 for e in direct:
  p=P/e['path'];assert sha(p)==e['sha256'] and p.stat().st_size==e['bytes'] and oct(p.stat().st_mode)==e['mode'];stable.append({'path':e['path'],'bytes':p.stat().st_size,'sha256':sha(p)})
 history=read(X/'history-selected/reads.json');assert len(history)==1;e=history[0];p=P/e['path'];assert sha(p)==e['sha256'] and p.stat().st_size==e['original_bytes'] and oct(p.stat().st_mode)==e['mode'] and (X/'history-selected/r78-source155.txt').read_bytes()==p.read_bytes()[e['start']:e['end']];stable.append({'path':e['path'],'bytes':p.stat().st_size,'sha256':sha(p)})
 assert (X/'contents-row.txt').read_bytes()==(P/'sources/CONTENTS.md').read_bytes()[255381:255907]
 for p in [P/'sources/CONTENTS.md',tp,P/'AGENTS.md',P/'sources/upstream.json']:stable.append({'path':str(p.relative_to(P)),'bytes':p.stat().st_size,'sha256':sha(p)})
 def verify(root,anchors,success=True):
  args=[sys.executable,'-I','-B',str(ROOT/'verify.py'),'--root',str(root)]
  for n,opt in [('FINAL.md','--final'),('MANIFEST.json','--manifest'),('REPORT.md','--report')]:args.extend([opt,anchors[n]])
  r=subprocess.run(args,cwd=P,capture_output=True,text=True,timeout=30);assert (r.returncode==0)==success,(r.stdout,r.stderr);return {'returncode':r.returncode,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()}
 actual=verify(ROOT,ANCHORS);controls=read(X/'control-outcomes.json');assert len(controls)==3;c=controls[0]['anchors'];clean=verify(X/'controls/clean',c);altered=verify(X/'controls/tampered',c,False);wrong=verify(X/'controls/clean',{**c,'FINAL.md':'0'*64},False);assert (X/'controls/clean/sample.md').read_bytes()==(ROOT/'notes/01-operative-comparison.md').read_bytes() and (X/'controls/clean/source.tex').read_bytes()==(X/'source/paper.tex').read_bytes()
 assert snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==mode and all(sha(P/e['path'])==e['sha256']for e in stable) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 dump('observed-root.json',{'root':before,'root_mode':mode});dump('replay.json',{'external_handoff_anchors':ANCHORS,'payload_files':69,'whole_root_files':72,'directories_including_root':12,'source_objects':11,'source_bytes':sum(e['bytes']for e in source),'primary_PDF_text_pairs':7,'primary_technical_texts':1,'render_members':2,'whole_completed_exception_originals':6,'history_section_originals':1,'stable_named_originals':stable,'actual_read_only_replay':actual,'existing_reduced_fixture_replay':clean,'existing_altered_fixture_rejection':altered,'wrong_external_anchor_rejection':wrong,'root_unchanged':True,'limits':'Artifact authentication only. Parent read four complete original notes,FINAL/REPORT,private reading account and verifier. Protected source/primary/visual proof bodies not semantically read by parent. Finite digit script not rerun. Parent observes single links and envelope modes beyond verifier requirements. Private identity inventory,replay,navigation and reading account remain local unstaged. No mathematical gate.'});print(json.dumps({'payload':69,'files':72,'source_objects':11,'primary_pairs':7,'stable_named_originals':len(stable),'read_only_checks':4}))
if __name__=='__main__':main()
