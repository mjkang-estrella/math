"""Generic root preparation of an independent adversarial qualification lane. Argument: path to a JSON spec with id, source_lane, lane, denials, peers, what, questions, source_files. No root mathematics."""
import os,resource,sys
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,hashlib,datetime,ast,shutil
ROOT=Path(__file__).resolve().parent;P=ROOT.parent;chunks={}
t=ast.parse((ROOT/'intake-planar-review-r506-prepare-r508-r509.py').read_text());exec(compile(ast.Module(body=[x for x in t.body if isinstance(x,ast.FunctionDef)],type_ignores=[]),'<documentary-functions>','exec'),globals())
sp=json.loads(Path(sys.argv[1]).read_text());mid=int(sp['id']);A=P/sp['source_lane'];L=P/sp['lane'];assert not L.exists();V=P/'regular-palm-locating-primary-qualification-claude-r1'
now=datetime.datetime.now(datetime.timezone.utc).isoformat();led=read(P/'ledger.json');cur=led['accepted_new']
bf=next(q for q in [A/'corpus-bindings.json',A/'literal-bindings.json',A/'literals.json'] if q.exists());d=read(bf);d=d.get('bindings',d.get('rows',d)) if isinstance(d,dict) and ('bindings' in d or 'rows' in d) else d
v=d[str(mid)] if isinstance(d,dict) else next(y for y in d if str(y.get('id',y.get('mathdb_id')))==str(mid))
def pick(v,*keys):
 for k in keys:
  if k in v:return v[k]
 raise KeyError(keys,list(v))
root=P.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus';c=Path(pick(v,'chunk_path','chunk','chunk_file'));q=c if c.is_absolute() else root/c.name
raw=q.read_bytes().splitlines(keepends=True)[int(pick(v,'one_based_line','line_one_based','chunk_line_one_based','line'))-1];assert pick(v,'raw_line_sha256_with_newline','raw_line_with_newline_sha256','raw_line_sha256_including_newline','raw_line_sha256') in (dg(raw),dg(raw.rstrip(b'\n')));literal=json.loads(raw);assert literal['mathdb_id']==mid
denpath=ROOT/sp['denials'];assert denpath.is_file()
L.mkdir();(L/'inputs').mkdir();(L/'inputs/sources').mkdir()
for h in ['bootstrap.py','run.py','write_lane.py','verify_frozen.py','registry-roots.json','source_get_guard.py','charge_search.py','model-policy.json']:shutil.copyfile(V/h,L/h)
shutil.copyfile(denpath,L/'inherited-denials.json');(L/f'inputs/original{mid}.raw.jsonl').write_bytes(raw);save(L/f'inputs/literal{mid}.json',literal)
shutil.copyfile(A/'FULLCANDIDATE.md',L/'inputs/author-candidate.md');shutil.copyfile(A/'DORMANT-SOL-FORMAL-PLAN.md',L/'inputs/author-formal-plan.md')
for f in sp['source_files']:shutil.copyfile(A/'sources'/f,L/'inputs/sources'/f)
for n in ['accepted57-scopes.json','prior39-scopes.json']:shutil.copyfile(V/'inputs'/n,L/'inputs'/n)
save(L/'reservation.json',dict(ids=[mid],rows=[literal],purpose='Independent adversarial qualification; no formal tools'));(L/'reservation.sha256').write_text(sha(L/'reservation.json')+'  reservation.json\n');save(L/'search-budget.json',dict(calls_used=0,queries_used=0,maximum_calls=2,maximum_queries=6,charged_before_call=True))
tt=ast.parse((ROOT/'prepare-covariance-planar-reviews-r506.py').read_text());common=next(ast.literal_eval(x.value) for x in tt.body if isinstance(x,ast.Assign) and any(isinstance(y,ast.Name) and y.id=='COMMON' for y in x.targets))
for a,b in [('Use ONLY GPT-6.1 Sol, HIGH reasoning, DEFAULT speed.','Use ONLY Claude Opus 5.5, high effort; GPT subagents are barred for now.'),('Campaign57/60',f'Campaign{cur}/80'),('Credit0,57/60 unchanged',f'Credit0,{cur}/80 unchanged'),('conditional dormant Sol formal brief','conditional dormant formal brief'),('Use and announce/read PDF skill /home/mj-kang/.codex/plugins/cache/openai-primary-runtime/pdf/26.1103.10131/skills/pdf/SKILL.md. ','Render PDF pages with pdftoppm and extract text with pdftotext by subprocess under your runner. ')]:
 assert common.count(a)==1,a;common=common.replace(a,b)
detail=f'''TARGET: independent adversarial qualification of MathDB {mid}. {sp['what']}

Campaign background. Many full proofs were excluded after a deeper check found a generic route or a reduction, including short routes through lemmas in references the source cited only for a special case, complete reductions to classical theory the author had not noticed, and literal statements with a one-page proof from a source lemma. An explicit counterexample was declined by the user as coefficient tuning. Result 58 passed this kind of review. Your job is to try hard to exclude this one, and to report honestly if you cannot.

TOOLS. You are Claude Opus 5.5. Your web search is WebSearch; load it through ToolSearch if deferred and use standard mode. Run every local command through your own runner as the common text says, invoked as timeout 140 python3 -I -B with the runner path, and do not use your own file-reading or web-fetching tools on lane files, with one exception: you may use Read to view PNG pages you rendered yourself. Do not pipe runner output through other commands outside the runner. Let every true exit code stand. Save each native search response as the very next tool call, and do not end your turn between a search and its save. Read charge_search.py and source_get_guard.py to see how they are invoked before using them.

READ FIRST. inherited-denials.json is over 300 KB and TASK.txt is long. Straight after the two mandatory commands, read both COMPLETELY in contiguous chunks of at most 15000 characters and record the ranges.

PROOF. Reconstruct the proof or a precise gap yourself before opening inputs/author-candidate.md. The mechanism above is disclosed; what you must reconstruct is the argument. Then audit the author against your reconstruction.

THE ADVERSARIAL QUESTIONS. Answer each concretely:
{sp['questions']}
Finally, spot-check the family comparison using inputs/accepted57-scopes.json and inputs/prior39-scopes.json.

If you find an applicable theorem or a complete routine reduction, recommend exclusion and give the bridge. If you cannot after a real attempt, say so, and say what the bounded search did and did not cover.

SIGNIFICANCE. Campaign policy gives zero credit to routine corollaries, routine adaptations, wording, domain or endpoint corrections, known results and parameter instances, and shortness alone is not an exclusion. Give the strongest case on each side. End with one recommendation: CREDITABLE SUBJECT TO LEAN AND PAPER, PARK, or EXCLUDE AS ROUTINE OR CORRECTION, with reasons. Root alone adjudicates.

FORMAL. Do not run Lean. Assess inputs/author-formal-plan.md and say what the literal Lean endpoint should be.

Author proposal is not acceptance. Credit 0; campaign {cur}/80 unchanged.
'''
task=common.format(lane=L,id=mid,peers=', '.join(sp['peers']))+'\nTARGET-SPECIFIC QUALIFICATION\n'+detail
(L/'TASK.txt').write_text(task);ff=[q for q in L.iterdir() if q.is_file() and q.name!='search-budget.json']+[q for q in (L/'inputs').rglob('*') if q.is_file()];save(L/'frozen-inputs.json',{str(q):sha(q) for q in ff})
rdy=dict(utc=now,lane=str(L),mathdb_id=mid,task_sha256=sha(L/'TASK.txt'),frozen_bindings=len(ff),model='claude-opus-5-5',effort='high',accepted_new=cur,target_new=80,credit=0,protected_peers=sp['peers'],latest_denials=str(denpath))
save(ROOT/f'qualification-{mid}-ready.json',rdy);save(ROOT/f'selection-routing-qualification-{mid}.json',dict(ids=[mid],sources=[literal['source_url']],lane=str(L),task_sha256=rdy['task_sha256'],metadata_only=True))
print(json.dumps({k:rdy[k] for k in ['lane','task_sha256','frozen_bindings']}))
