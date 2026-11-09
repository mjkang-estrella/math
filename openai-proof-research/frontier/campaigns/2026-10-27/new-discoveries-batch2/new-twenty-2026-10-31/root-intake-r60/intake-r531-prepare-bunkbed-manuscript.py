"""Root documentary verification of r531 (zero qualified survivors, no network use) and preparation of the 382297 manuscript lane. No root mathematics."""
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,re,ast,shutil
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
now=datetime.datetime.now(datetime.timezone.utc).isoformat();led=read(P/'ledger.json');assert led['accepted_new']==57 and led['target_new']==80
A=P/'expanded-corpus-r531';F=P/'transitive-bunkbed-endpoint-assembly-formal-deepseek-r23';Q=P/'transitive-bunkbed-primary-qualification-sol-r2';L=P/'transitive-bunkbed-manuscript-deepseek-r1';assert not L.exists()

# Every documentary check precedes any root mutation.
m=read(A/'manifest.json');assert m['file_count']==91==len(m['files'])
names=set()
for x in m['files']:
 n=x['path'];assert not Path(n).is_absolute() and '..' not in Path(n).parts;names.add(n)
 q=A/n;assert not q.is_symlink() and sha(q)==x['sha256'] and q.stat().st_size==x['bytes'],n
aex=[x['path'] for x in m['self_exclusions']];assert set(aex)=={'manifest.json','manifest-compute.output.txt','manifest-compute.receipt.json'}
inventory=set()
for q in A.rglob('*'):
 assert not q.is_symlink()
 if q.is_file():inventory.add(str(q.relative_to(A)))
assert inventory==names|set(aex)
frozen(A,13);arec=receipts(A,{'check-bindings-1.receipt.json':1,'check-bindings-2.receipt.json':1,'emit-literal-bindings.receipt.json':1,'task-read-c00000-c15000.receipt.json':1})
route=read(ROOT/'selection-routing-r531.json');assert sha(A/'TASK.txt')==route['task_sha256'] and sha(A/'reservation.json')==route['reservation_sha256']
ids=read(A/'reservation.json')['ids'];bind=read(A/'literal-bindings.json');rows=bind['bindings'];assert len(ids)==len(rows)==20 and [int(v['id']) for v in rows]==ids
brief=(A/'ACTUALBRIEF.md').read_text();assert all(str(i) in brief for i in ids)
root=Path(bind['corpus_dir']);assert root==P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus'
sources={}
for v in rows:
 q=root/v['chunk']
 if str(q) not in chunks:
  data=q.read_bytes();chunks[str(q)]=(dg(data),data.splitlines(keepends=True))
 h,lines=chunks[str(q)];assert h==v['chunk_sha256'];raw=lines[int(v['line_1based'])-1];assert raw.endswith(b'\n') and v['trailing_newline'] is True and dg(raw.rstrip(b'\n'))==v['raw_line_sha256']
 obj=json.loads(raw);assert obj['mathdb_id']==int(v['id']) and obj['statement']==v['statement'] and dg(obj['statement'].encode())==v['decoded_statement_sha256'];sources[str(v['id'])]=obj['source_url']
assert read(A/'search-budget.json')==dict(calls_used=0,queries_used=0,maximum_calls=3,maximum_queries=9,charged_before_call=True) and not (A/'guard-ledger.jsonl').exists()
assert not list(A.glob('FULLCANDIDATE*')) and not list(A.glob('DORMANT*')) and (A/'NO-SURVIVOR.md').is_file()
src=[Q/'PROOF.md',Q/'REVIEW.md',Q/'inputs/author-CANDIDATE.md',Q/'inputs/literal382297.json',F/'SUMMARY.md',F/'audit_final2.output.txt',P/'cmdrr-five-three-root-final-r7/source/cmdrr-five-three-proof.roff']
for q in src:assert q.is_file(),q
leans=['BunkbedBase','BunState','BunFinalEndpoint','BunFinalWindow','BunFinalModel','BunDomAbstract','BunDomFinal','BunReachBridge']
for n in leans:assert (F/'src'/(n+'.lean')).is_file(),n

ass='r531 zero qualified survivors, DeepSeek lane with no network use: zero searches and zero GET hops, so prior art and novelty are unpaid for every target. 361816 Arad-Herzog keeps a class-sum criterion and A5 and PSL(2,7) exclusions at n=3,4, no general proof. 349042 Rosen lifting has k=1, n=2,3,4 by p-adic pairing and a precise gap at n>=5. 380771 has only the elementary bound. 368351, 360178, 347791 and 371095 have literal defects. No FULLCANDIDATE. Four failed runner receipts retained, and one file written directly inside a runner is disclosed. Verified 91 manifest files, 20 corpus bindings against the corpus, 13 frozen. Credit 0, 57/80.'
ar=dict(utc=now,source_lane=str(A),manifest_sha256=sha(A/'manifest.json'),task_reservation_genesis_verified=True,verified_manifest_files=91,verified_frozen_bindings=13,verified_original_bindings=ids,source_url_by_id=sources,runner_receipts=arec,search_budget=read(A/'search-budget.json'),model='spark/DeepSeek-V4.1-Flash-1017',scientific_summary=ass,root_disposition='ZERO_QUALIFIED_SURVIVORS_NO_NETWORK_USE',credit=0,accepted_new=57,terminal_self_exclusions=sorted(aex),root_scope='Documentary integrity only; no mathematical execution by root.')
save(P/'expanded-corpus-r531-parent-integration.json',ar)
den=read(ROOT/'inherited-denials-r564.json');den['utc']=now;den['root_r531_scope']=ass;save(ROOT/'inherited-denials-r565.json',den)

L.mkdir();origins={}
def copy(src,rel):
 d=L/rel;d.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,d);assert sha(src)==sha(d);origins[rel]=dict(path=str(src),sha256=sha(src))
for h in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py']:copy(F/h,h)
save(L/'model-policy.json',read(ROOT/'model-policy-claude-deepseek-20261109.json'))
for d in ['source','output/pdf','qa']:(L/d).mkdir(parents=True,exist_ok=True)
for rel,q in {'inputs/shortest-proof-PROOF.md':Q/'PROOF.md','inputs/second-review-REVIEW.md':Q/'REVIEW.md','inputs/author-CANDIDATE.md':Q/'inputs/author-CANDIDATE.md','inputs/literal382297.json':Q/'inputs/literal382297.json','inputs/r23-SUMMARY.md':F/'SUMMARY.md','inputs/r23-audit-output.txt':F/'audit_final2.output.txt','inputs/format-example.roff':P/'cmdrr-five-three-root-final-r7/source/cmdrr-five-three-proof.roff'}.items():copy(q,rel)
for n in leans:copy(F/'src'/(n+'.lean'),'inputs/lean/'+n+'.lean')
for n in ['bunkbed.clean.txt','bunkbed-journal.txt','bunkbed-thesis.txt','bunkbed-acyclic.txt','bunkbed-complete-correct.txt','bunkbed-leander.txt']:copy(Q/'inputs/sources'/n,'inputs/sources/'+n)
save(L/'INPUT-ORIGINS.json',origins)
peers=['expanded-corpus-r532','transitive-bunkbed-formal-independent-review-claude-r1']
task=f'''MathDB 382297: draft paper. Pi DeepSeek V4.1 Flash, high thinking. Do the work yourself; no children or fallback model. Write ONLY inside {L}. Credit 0; campaign 57 of 80 unchanged. Root alone decides acceptance.

GOAL. A short, accurate, readable draft paper, 4 to 6 pages, titled "The bunkbed conjecture for transitive tournaments". It presents the proof of Hollom's Conjecture 6.4, BBC(E7,T_n), and its Lean certificate.

FIRST command EXACTLY: timeout 20 python3 -I -B {L}/bootstrap.py
SECOND command EXACTLY: timeout 140 python3 -I -B {L}/verify_frozen.py before

RULES. Peers {peers[0]} and {peers[1]} and every other lane are protected: no read, stat, hash, list or glob. No network, git, installs, accounts, browser, other models, or background jobs. Local work goes through: timeout 140 python3 -I -B {L}/run.py UNIQUE_LABEL with Python on stdin. Python under run.py may call groff, ps2pdf, pdftoppm and pdftotext by subprocess. Authored files go through {L}/write_lane.py RELATIVE_PATH with content on stdin. Do not modify helpers or inputs. Keep every failure and its true exit.

INTEGRITY RULES, which matter more than style:
- Do not invent authors, affiliations, dates, acknowledgements, citations, page numbers or results. Write the author line as: "Draft prepared with AI assistance; authorship to be determined."
- Cite only works present in inputs/sources, inputs/second-review-REVIEW.md or inputs/author-CANDIDATE.md, using bibliographic details printed there. If a detail is not there, leave it out.
- State only what the inputs support. The Lean statements must be quoted exactly from inputs/lean and inputs/r23-audit-output.txt.
- Do not claim acceptance, peer review, priority or worldwide novelty.

CONTENT.
1. Introduction: the bunkbed conjecture in brief, Hollom's directed models and that E7 is called D7 in the journal version, the fact that the statement fails for general acyclic digraphs (Przybylowski), and why tournaments were singled out. Quote or closely paraphrase what Hollom says, with a reference to where.
2. Model and theorem: define T_n, the two layers, one independent fair horizontal token per arc per layer, one shared bidirectional vertical token per index, uniform on 2^(n^2) outcomes, reachability including the zero-length path. State the theorem for all n and all u, v: P((u,0)→(v,0)) >= P((u,0)→(v,1)).
3. Proof, written carefully and fully, following inputs/shortest-proof-PROOF.md and inputs/author-CANDIDATE.md: reveal columns in index order; the counts (A,B) of reachable copies; why those counts are sufficient, which is where completeness in the order is used; the increment law with X, Y, Z and the four probabilities; reflection equivariance and no crossing; the paired-sum induction for reflected mass dominance; the initial law; the payoff (2^-b - 2^-a)/2; and the cases v<u and v=u. Say exactly where transitivity is used and why the argument does not extend to general acyclic digraphs.
4. Remarks: the column-homogeneous generalization, clearly labelled as an immediate extension with no novelty claim. Also say that reflection until meeting is an old technique.
5. Lean certificate: Lean 4.34.1, mathlib d13f23b723b8a846827a245b89c10fc7d3f11612; the exact statement of Bun.bunkbed_E7_transitive; the model checks card Token n = n*n and card Out n = 2^(n*n); that the axioms are exactly propext, Classical.choice and Quot.sound; that 33 modules were rebuilt from an empty build; and the two main bridges (Reach bridge and state-level inequality). Write one clearly marked placeholder paragraph: "[INDEPENDENT AUDIT STATUS: to be completed by root]".
6. Limits: state plainly that the prior-art search was bounded, that the final journal version of Przybylowski's paper (DOI 10.1016/j.ejc.2025.104289) was not read, that the proof is short and the method elementary, and that no worldwide novelty is claimed. Disclose AI assistance.
Mention the MathDB record 382297 once.

FORMAT. Use groff, following inputs/format-example.roff for page setup only, and keep the source at source/bunkbed-transitive-tournaments.roff. Set mathematics plainly and legibly; do not use symbols that render as blanks or boxes. Build output/pdf/bunkbed-transitive-tournaments.pdf.

QA. Render every page with pdftoppm to qa/page-N.png, extract text with pdftotext, and check that no formula is missing, that no line overflows the margin and that the page count is 4 to 6. Save qa/QA.json with the checks you actually made and how. If you cannot view images, say so; root will inspect them. Also write CLAIMS.json: for each mathematical or bibliographic claim in the paper, the input file and passage or Lean theorem name that supports it.

SEAL. Run timeout 140 python3 -I -B {L}/verify_frozen.py after, then under run.py with label seal_manifest write MANIFEST.json: a dict with count, credit 0, files as a list of objects with path, sha256 and bytes covering every lane file except the three terminal ones, and terminal_noncircular_self_exclusions listing exactly MANIFEST.json, seal_manifest.receipt.json and seal_manifest.output.txt. Stop at handback.
'''
(L/'TASK.txt').write_text(task)
ff=[q for q in L.rglob('*') if q.is_file()];save(L/'frozen-inputs.json',{str(q):sha(q) for q in ff})
ready=dict(utc=now,lane=str(L),mathdb_id=382297,task_sha256=sha(L/'TASK.txt'),frozen_bindings=len(ff),provider='pi',model='spark/DeepSeek-V4.1-Flash-1017',thinking='high',credit=0,accepted_new=57,target_new=80,protected_peers=peers)
save(ROOT/'bunkbed-manuscript-r1-ready.json',ready)
print(json.dumps(dict(r531_manifest=91,frozen=13,corpus=20,next={k:ready[k] for k in ['lane','task_sha256','frozen_bindings']},credit=0,accepted_new=57)))
