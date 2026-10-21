#!/usr/bin/env python3
"""Read-only Structural169 no-nominee artifact archive."""
import hashlib,importlib.util,json,stat,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2];ROOT=B/'fresh-structural-discovery-r169';X=ROOT/'private'
sp=importlib.util.spec_from_file_location('helpers',B/'discovery-analytic-r161-parent/replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
sha,snap=h.sha,h.snap
ANCHORS={'FINAL.md':'207b97641639ed4f12a1fe5221caeec5f11a132c50bd3af9d1d69555123d4018','MANIFEST.json':'bdfcacea09b520ef9eb728dce4050adf9f953b60031aea86bcc1be17502ee3a8','REPORT.md':'e7e09ef1f736d6547f26aeba82d2c4849ae9fc89b273dfb0285d298063ac1efc'}
def read(p):return json.loads(p.read_text())
def dump(n,d):(O/n).write_text(json.dumps(d,indent=2)+'\n')
def main():
 base=read(O/'integration-baseline.json');assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==base['head'] and len(read(B/'tasks.json')['tasks'])==570
 before=snap(ROOT);mode=stat.S_IMODE(ROOT.stat().st_mode);s=read(O/'task-status.json')['structuredContent'];assert s['status']=='completed' and s['workState']=='result_available' and not s['hasPendingChildRuns'] and not s['hasPendingQuestion'] and s['pendingApproval'] is None;assert all(sha(ROOT/n)==v and v in s['summary']for n,v in ANCHORS.items());assert read(ROOT/'ANCHORS.json')==ANCHORS
 m=read(ROOT/'MANIFEST.json');assert len(m['files'])==69 and {n for n,e in before.items()if e['kind']=='file'}==set(m['files'])|set(ANCHORS)|{'ANCHORS.json'}
 tp=P/'sources/preprints-tree.json';assert sha(tp)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=read(tp);assert len(tree['tree'])==13223 and not tree['truncated'];entries={e['path']:e for e in tree['tree']};source=read(X/'source/objects.json');assert len(source)==9
 for e in source:
  q=X/'source'/e['local'];data=q.read_bytes();node=entries[e['path']];assert len(data)==e['size']==node['size'] and sha(q)==e['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['blob']==node['sha'] and e['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+e['path']
 primary=read(X/'primary/acquisition.json');assert len(primary)==6
 for e in primary:
  q=X/'primary'/(e['name']+'.pdf');assert q.read_bytes().startswith(b'%PDF') and q.stat().st_size==e['bytes'] and sha(q)==e['sha256'];q=q.with_suffix('.txt');assert q.stat().st_size==e['textbytes'] and sha(q)==e['textsha256']
 for name in ['ns1994-page8.png','btw-v1-page10.png','fhkl-v3-page11.png']:assert (X/'primary'/name).read_bytes().startswith(b'\x89PNG\r\n\x1a\n')
 for e in read(X/'primary/read-extents.json'):
  p=X/'primary'/e['file'];assert 0<=e['start']<=e['end']<=p.stat().st_size and sha(p)==e['sha256']
 stable=[];completed=[B/'discovery-structural-r168-parent/assessment.md']+[B/'fresh-structural-discovery-r168/notes'/n for n in ['00-start.md','01-operative-reading.md','02-integrated-calculation.md','03-limits-and-outcome.md']]
 for i,p in enumerate(completed):
  assert p.read_bytes()==(X/('completed-exception-%d.txt'%i)).read_bytes();stable.append({'path':str(p.relative_to(P)),'bytes':p.stat().st_size,'sha256':sha(p)})
 history=read(X/'history-selections.json');assert len(history)==2
 for e,n in zip(history,['history-r25-candidate.md','history-r25-scope.md']):
  p=P/e['path'];assert sha(p)==e['sha256'] and (X/n).read_bytes()==p.read_bytes()[e['start']:e['end']];stable.append({'path':e['path'],'bytes':p.stat().st_size,'sha256':sha(p)})
 assert (X/'acceptance.txt').read_bytes()==(P/'frontier/NEW-TEN-2026-10-14.md').read_bytes()[4801:6346];assert (X/'contents-source192.txt').read_bytes()==(P/'sources/CONTENTS.md').read_bytes()[298303:299572]
 for p in [P/'sources/CONTENTS.md',tp,P/'AGENTS.md',P/'sources/upstream.json']:stable.append({'path':str(p.relative_to(P)),'bytes':p.stat().st_size,'sha256':sha(p)})
 def verify(root,anchors):
  args=[sys.executable,'-I','-B',str(ROOT/'verify.py'),str(root)]
  for n,opt in [('FINAL.md','--final'),('MANIFEST.json','--manifest'),('REPORT.md','--report')]:args.extend([opt,anchors[n]])
  r=subprocess.run(args,cwd=P,capture_output=True,text=True,timeout=30);assert r.returncode==0,(r.stdout,r.stderr);return {'returncode':r.returncode,'stdout':r.stdout.strip()}
 actual=verify(ROOT,ANCHORS);clean=X/'controls';control=verify(clean,{n:sha(clean/n)for n in ANCHORS});assert len(read(X/'control-results.json')['tests'])==6 and read(X/'control-results.json')['all_expected_outcomes'];diagnostic=read(X/'exact-diagnostic.json');assert diagnostic['passed'] and diagnostic['checks']=={'all_truth_tables_normalized':270,'balanced_compositions':84,'compression_examples':1,'noise_recursions':3}
 assert snap(ROOT)==before and stat.S_IMODE(ROOT.stat().st_mode)==mode and all(sha(P/e['path'])==e['sha256']for e in stable) and all(sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 dump('observed-root.json',{'root':before,'root_mode':mode});dump('replay.json',{'external_handoff_anchors':ANCHORS,'payload_files':69,'whole_root_files':73,'directories_including_root':7,'source_objects':9,'source_bytes':sum(e['size']for e in source),'primary_PDF_text_pairs':6,'render_members':3,'whole_completed_exception_copies':5,'whole_history_originals':2,'stable_named_originals':stable,'actual_read_only_replay':actual,'existing_reduced_fixture_replay':control,'copied_control_cases_recorded':6,'root_unchanged':True,'limits':'Artifact authentication only. Parent read all four public original notes,programs/envelopes and private reading/start accounts. Protected source/primary/visual proof bodies were not semantically read by parent. Finite exact script not rerun. Parent additionally observes directory/envelope modes and links absent from verifier manifest. Private identity inventory,replay and navigation stay local unstaged.'});print(json.dumps({'payload':69,'files':73,'source_objects':9,'primary_pairs':6,'stable_named_originals':len(stable),'read_only_replays':2}))
if __name__=='__main__':main()
