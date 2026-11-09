import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(15,15)); resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3))
import pathlib,sys,subprocess,json,hashlib,datetime,time
P=pathlib.Path(__file__).resolve().parent; Q=P.parent/'expanded-corpus-r361'; start=time.monotonic()
def wr(n,s):
 r=subprocess.run([sys.executable,'-I','-B',str(P/'write_lane.py'),n],input=s,text=True,capture_output=True); assert r.returncode==0,r.stderr

def js(n,d): wr(n,json.dumps(d,indent=2,ensure_ascii=False)+'\n')
record=json.loads((P/'target-record.json').read_text()); literal=json.loads((Q/'literals/355016.json').read_text()); assert record==literal
old=json.loads((Q/'results.json').read_text())
if isinstance(old,list): old=next(x for x in old if x.get('mathdb_id')==355016)
else:
 if '355016' in old: old=old['355016']
 else:
  values=[x for v in old.values() for x in (v if isinstance(v,list) else [v]) if isinstance(x,dict) and x.get('mathdb_id')==355016]; old=values[0]
js('history-keyed355016.json',dict(mathdb_id=355016,source=str(Q/'results.json'),disposition=old.get('disposition'),accepted_credit=old.get('accepted_credit'),scope='Exact assigned completed r361 result only; no broad history clearance'))
js('literal-binding.json',dict(mathdb_id=355016,equal=True,target_sha256=hashlib.sha256((P/'target-record.json').read_bytes()).hexdigest(),original_sha256=hashlib.sha256((Q/'literals/355016.json').read_bytes()).hexdigest()))
js('keyed355016results.json',{'355016':dict(disposition='HOLD_DEPTH_AT_LEAST_TWO_KERNEL_ENVELOPE_GAP',accepted_credit=0,full_endpoint_closed=False,new_lane_progress=['All of up epsilon(A0) is R-dependent for every actual representation','A minimal initial marked family need not even be cyclic: hand-constructed F2 graphic K4','Necessary one-dimensional-relation and envelope-overlap deficit for a depth-two failure'],proof_or_gap='GAP.md',review='REVIEW.md',pi_plan=None,dispatch=False,campaign=dict(accepted_new=52,target_new=60,delta=0),novelty='No literature novelty claim; partial helper only')})
js('keyed355016review.json',{'355016':dict(literal_fidelity='restored with version/index caveats',ordinary_full='unresolved',partial_lemma='same-investigator adversarially rederived',independent_acceptance_review=False,prior_art='not cleared',significance='zero-credit partial progress',formalization='not attempted',replay='not attempted',protected_inputs_before=267,protected_inputs_after=267)})
js('supplemental-read-inventory.json',[
 dict(path=str(Q/'ORDINARY.md'),depth='355016 section actually surfaced; terminal output also contained neighboring material not relied upon'),
 dict(path=str(Q/'sources/derived.html.txt'),depth='Terminal reads: Section3.2; Definitions4.1-4.3/Remark4.4; Lemma8.1/Conj8.4; character ranges15500:17300,39700:44900,49000:50200,0:2000. Earlier multi-term print truncated; no full-body read claim'),
 dict(path=str(Q/'sources/maximal-matroids.html.txt'),depth='Introduction proper sequences and Lemmas1.1/1.2 with proof; no full body review'),
 dict(path='/home/mj-kang/Documents/Dev/math/openai-proof-research/sources/upstream.json',depth='Full short immutable revision metadata read'),
 dict(path='/home/mj-kang/Documents/Dev/math/openai-proof-research/sources/CONTENTS.md',depth='Only target literal-match filtering; no body review'),
 dict(path=str(Q/'sources/leanpool-head.html'),depth='Only canonical title/URLs and currentOid extracted')])
js('search-receipt.json',dict(tool='web.run search via functions.exec',queries=['"combinatorial derived matroid" "genericity" conjecture','"combinatorial derived matroids" conjecture counterexample maximal'],depth='Search snippets only; actual journal and author passages separately read',primary_hits=['https://arxiv.org/abs/2206.06881','https://www.combinatorics.org/ojs/index.php/eljc/article/download/v30i2p8/pdf/','https://matroidunion.org/?p=5265'],limitation='Tool did not provide HTTP byte hashes or exact request UTC; no such telemetry invented. This file records query and reading scope, not raw response. Nonprimary hits not relied upon.'))
entries=[]
for x in json.loads((P/'read-inventory.json').read_text()):
 entries.append(x)
for p in sorted((P/'sources').iterdir()):
 b=p.read_bytes(); entries.append(dict(path=str(p.relative_to(P)),bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),depth='Acquisition and routing snippets only; see access/registry receipts; no proof-body clearance'))
js('source-inventory.json',entries)
u=resource.getrusage(resource.RUSAGE_SELF)
js('finalize-job-receipt.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),exit=0,caps_before_reads=True,affinity=sorted(os.sched_getaffinity(0)),CPU_limit=15,AS_limit=1024**3,self_CPU_seconds=u.ru_utime+u.ru_stime,self_highwater_RSS_KiB=u.ru_maxrss,sampled_RSS=[s for s in pathlib.Path('/proc/self/status').read_text().splitlines() if s.startswith('VmRSS:')],wall_seconds=time.monotonic()-start,scope='self-only, not group/cgroup peak',all_children_reaped=True,limitation='Early one-shot read commands have tool exit/wall receipts but no per-command sampled RSS/CPU logs; do not claim retrospective telemetry'))
files=[]
for p in sorted(P.rglob('*')):
 if p.is_file() and p.name not in ['manifest.json','manifest-verification.json']:
  assert not p.is_symlink(); b=p.read_bytes(); files.append(dict(path=str(p.relative_to(P)),bytes=len(b),sha256=hashlib.sha256(b).hexdigest()))
js('manifest.json',dict(algorithm='sha256',files=files,excludes=['manifest.json','manifest-verification.json'],scope='This lane only; hashes of actual files'))
m=json.loads((P/'manifest.json').read_text()); errors=[]
for x in m['files']:
 b=(P/x['path']).read_bytes()
 if len(b)!=x['bytes'] or hashlib.sha256(b).hexdigest()!=x['sha256']: errors.append(x['path'])
js('manifest-verification.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),listed=len(files),mismatches=errors,manifest_sha256=hashlib.sha256((P/'manifest.json').read_bytes()).hexdigest(),verified=not errors))
assert not errors
print(json.dumps(dict(files_verified=len(files),mismatches=errors,credit=0,campaign='52/60 unchanged')))
