"""Root record of the MATCH closure and preparation of the 352303 Lean lane on DeepSeek. No root Lean or mathematics."""
import os,resource,subprocess
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,ast,shutil
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();assert read(P/'ledger.json')['accepted_new']==58
Q=P/'biharmonic-tree-primary-qualification-claude-r1';T=P/'transitive-bunkbed-endpoint-assembly-formal-deepseek-r23';L=P/'biharmonic-tree-formal-deepseek-r1';assert not L.exists()
ledger=[json.loads(l) for l in (Q/'guard-ledger.jsonl').read_text().splitlines()];un=next(e for e in ledger if e['event']=='unavailable');assert 'match.pmf.kg.ac.rs' in un['url']
work='MATCH Commun. Math. Comput. Chem. 91(2) pages 285-286, identity unread';fs=f'ENTIRE identified work {work}: ALL NEW body/METADATA/query/hosts/versions/arxiv/authors/cache/mirror/DOI/API/indirect deliveries unavailable after a request timeout; no retry.'
den=read(ROOT/'inherited-denials-r575.json');den['utc']=now;den['root_match_timeout_closure']=fs
den['blocked_keys']=sorted(set(den['blocked_keys'])|{un.get('url_key') or un['url']});den['blocked_artifacts']=sorted(set(den['blocked_artifacts'])|{work.lower()})
den['records'].append(dict(url=un['url'],reason=dict(status='timeout',artifact=work,restriction=fs),evidence=dict(path=str(Q/'guard-ledger.jsonl'),sha256=sha(Q/'guard-ledger.jsonl'),guard_sha256=sha(Q/'guard-ledger.jsonl'))))
save(ROOT/'inherited-denials-r576.json',den)
save(ROOT/'root-search-352303-20261109.json',dict(utc=now,mathdb_id=352303,mode='standard',queries=['biharmonic index of trees extremal star path conjecture proved Lin "biharmonic index"','sum of squared reciprocals of Laplacian eigenvalues of trees maximum path minimum star proof','biharmonic distance trees conjecture "biharmonic index" tree maximum attained by path 2023 2024 2025'],finding='No proof or disproof of Conjecture 5.3 surfaced. Results were the source, Wei-Li-Yang, and unrelated work. MATCH 91(2) 285-286 appeared by file name only and was not opened.',scope='Navigation only; not a novelty certificate.'))
led=read(P/'ledger.json');led['process_notes'].append(dict(utc=now,item='352303 prospective scientific pass; Lean started on DeepSeek.'));(P/'ledger.json').write_text(json.dumps(led,indent=2)+'\n')
L.mkdir();origins={}
def copy(src,rel):
 d=L/rel;d.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,d);assert sha(src)==sha(d);origins[rel]=dict(path=str(src),sha256=sha(src))
for h in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','PINS.json','formal_command.py','run_lean_32g.py','check32.sh','checker32.sh']:copy(T/h,h)
for h in ['check32.sh','checker32.sh']:(L/h).chmod(0o755)
save(L/'model-policy.json',read(ROOT/'model-policy-claude-deepseek-20261109.json'))
for d in ['src','build','cache','audit','results','logs']:(L/d).mkdir()
for rel,q in {'inputs/reviewer-PROOF.md':Q/'PROOF.md','inputs/reviewer-REVIEW.md':Q/'REVIEW.md','inputs/author-candidate.md':Q/'inputs/author-candidate.md','inputs/author-formal-plan.md':Q/'inputs/author-formal-plan.md','inputs/literal352303.json':Q/'inputs/literal352303.json'}.items():copy(q,rel)
(L/'inputs/sources').mkdir()
for q in sorted(list((Q/'sources').glob('*.pdf'))+list((Q/'inputs/sources').glob('*.pdf'))):
 copy(q,'inputs/sources/'+q.name);r=subprocess.run(['pdftotext','-layout',str(q),str(L/'inputs/sources'/(q.stem+'.txt'))],capture_output=True);assert r.returncode==0,r.stderr
save(L/'INPUT-ORIGINS.json',origins)
peers=['expanded-corpus-r536','zeckendorf-games-formal-deepseek-r1']
task=f'''MathDB 352303: Lean formalization of the extremal biharmonic index theorem for trees, first lane. Pi DeepSeek V4.1 Flash, high thinking. Do the work yourself; no children or fallback model. Write ONLY inside {L}. Credit 0; campaign 58 of 80 unchanged.

TARGET, from inputs/literal352303.json and inputs/reviewer-REVIEW.md section 6. For every n >= 5, every finite vertex type V of cardinality n and every tree G on V: BH(star on n vertices) <= BH(G) <= BH(path on n vertices), with equality on the left iff G is isomorphic to the star and on the right iff G is isomorphic to the path. BH(G) = n times the sum over nonzero Laplacian eigenvalues of 1/lambda^2, stated with mathlib's SimpleGraph.lapMatrix and Matrix.IsHermitian.eigenvalues. Prove that for a connected graph exactly one eigenvalue is zero, so "sum over nonzero eigenvalues" and "i = 2 to n" agree. Read section 6 of the review closely and follow its cautions.

MATHEMATICS. inputs/author-candidate.md and inputs/reviewer-PROOF.md. The exact formula BH(T) = N(T)/n, with N(T) the sum over edge pairs from the inverse edge Laplacian; the lower bound from a_e b_e >= n-1 and alpha(e;f) alpha(f;e) >= 1; the upper bound by a pendant-path shift with an exact positive difference. The reviewer used a different, symmetric shift merging two whole pendant paths; choose whichever formalizes better.

FIRST command EXACTLY: timeout 20 python3 -I -B {L}/bootstrap.py
SECOND command EXACTLY: timeout 140 python3 -I -B {L}/verify_frozen.py before

RULES. Peers {peers[0]} and {peers[1]} and every other lane are protected: no read, stat, hash, list or glob. No network, git, installs, accounts, browser, other models, mathematical programs, solvers or background jobs. Do not modify helpers, PINS or inputs. Authored files go through {L}/write_lane.py RELATIVE_PATH with content on stdin. Non-Lean local work goes through: timeout 140 python3 -I -B {L}/run.py UNIQUE_LABEL with Python on stdin.
Lean runs only through these wrappers, one at a time, with unique labels:
  {L}/check32.sh MODULE LABEL     compile src/MODULE.lean strictly
  {L}/checker32.sh MODULE LABEL   kernel-check the compiled module
Unchanged: 6 GiB real memory, CPU 115 s, -j1, -M3500, LEAN_NUM_THREADS 1, -DwarningAsError=true. Use specific mathlib imports; `import Mathlib` is killed by the memory guard. `set_option maxHeartbeats N in` is allowed where it helps within the CPU limit. Keep modules small. No unchanged retries; every changed attempt needs a new label. Keep every failure and its true exit. Name new modules with the prefix BiH.

ROUTE. Start writing real Lean at once. Tree surgery on arbitrary SimpleGraph data is the expensive part, so plan for it: a finite maximizer argument over trees, or a rooted encoding with a proved bridge, as the review suggests.
1. BiHBase: BH as defined above, connectedness gives exactly one zero eigenvalue, and the star and path as explicit graphs.
2. BiHFormula: the trace identity giving BH(T) = N(T)/n for a tree. Use whichever matrix route is cheapest in Lean, for example L + J/n, or the edge Laplacian with its explicit inverse. Check against the source's double-star value if practical.
3. BiHLower: the lower bound and its equality case.
4. BiHShift and BiHUpper: the shift identity and the upper bound with its equality case.
5. BiHEndpoint: the literal theorem with no added premise, including the isomorphism equality clauses.

SUSTAIN. Do not stop at a helper. Work as far as you can, in order. If blocked, keep the source and exact diagnostic, try a genuinely different route, and only then stop with a precise statement of what is unpaid. A later lane will continue, so leave a clean state. A module that compiles but fails its kernel check is NOT green. Never add sorry, admit, axiom, unsafe, native_decide, a weakened target or a conclusion-bearing premise.

EVIDENCE. Every green module needs a passing compile, a passing kernel check, and an audit module with #print axioms for each main theorem, compiled through check32.sh. Only propext, Classical.choice and Quot.sound are allowed. Keep results/352303.json updated with strict_green_modules (name, source_sha256, olean_sha256, compile_label, check_label, audit_label), steps completed, exact theorem statements, and an unpaid list. Write SUMMARY.md at the end, honest about partial progress.

STATUS. Prospective scientific pass, modest significance. Acceptance is root-only and may be refused. Do not claim credit.

SEAL. Run timeout 140 python3 -I -B {L}/verify_frozen.py after, then under run.py with label seal_manifest write MANIFEST.json: a dict with count, credit 0, files as a list of objects with path, sha256 and bytes covering every lane file except the three terminal ones, and terminal_noncircular_self_exclusions listing exactly MANIFEST.json, seal_manifest.receipt.json and seal_manifest.output.txt. Stop at handback.
'''
(L/'TASK.txt').write_text(task)
ff=[q for q in L.rglob('*') if q.is_file()];save(L/'frozen-inputs.json',{str(q):sha(q) for q in ff})
ready=dict(utc=now,lane=str(L),mathdb_id=352303,task_sha256=sha(L/'TASK.txt'),frozen_bindings=len(ff),provider='pi',model='spark/DeepSeek-V4.1-Flash-1017',thinking='high',credit=0,accepted_new=58,target_new=80,protected_peers=peers)
save(ROOT/'biharmonic-formal-r1-ready.json',ready);save(ROOT/'selection-routing-biharmonic-formal-r1.json',dict(ids=[352303],sources=['https://arxiv.org/abs/2110.09931'],lane=str(L),task_sha256=ready['task_sha256'],metadata_only=True))
print(json.dumps({k:ready[k] for k in ['lane','task_sha256','frozen_bindings']}))
