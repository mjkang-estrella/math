from pathlib import Path
import json,hashlib,re,sys
R=Path(sys.argv[1]);D=R.parent/'expanded-corpus-r178'
before=json.loads((R/'inputs-before.json').read_text());after={p:hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in before}
(R/'inputs-after.json').write_text(json.dumps(after,indent=2));assert before==after
src=(R/'replay/Interpolation.lean').read_text();scan=[]
for name in ['Interpolation.lean','Audit.lean']:
 for i,line in enumerate((R/'replay'/name).read_text().splitlines(),1):
  if re.search(r'\b(sorry|admit|axiom|unsafe|partial|implemented_by|extern|native_decide)\b|_unsafe_rec',line):scan.append({'file':name,'line':i,'text':line})
# Audit strings that name forbidden metadata are expected; theorem source must be clean.
assert not [x for x in scan if x['file']=='Interpolation.lean']
assert (R/'replay/Interpolation.lean').read_bytes()==(D/'lean/Interpolation.lean').read_bytes()
manifest=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/lake-manifest.json')
packages=json.loads(manifest.read_text());mathlib=[p for p in packages['packages'] if p['name']=='mathlib'][0]
assert mathlib['rev']=='d13f23b723b8a846827a245b89c10fc7d3f11612'
raw=(D/'raw/360905.jsonl').read_bytes();assert hashlib.sha256(raw).hexdigest()=='cf3072564d7631d411e42f3d16ceb44ee52e7a169e0bb1897e5b0ce730e496ad'
# Cross-check the normalized corpus line, without writing to its lane.
rec=json.loads((D/'results.json').read_text())['360905'];p=Path(rec['provenance']['chunk'])
with p.open('rb') as f:
 for i,line in enumerate(f,1):
  if i==151:corpus_line=line;break
assert corpus_line.rstrip(b'\n')==raw.rstrip(b'\n')
statuses={p.stem:p.read_text().strip() for p in (R/'logs').glob('*.receipt')}
peaks={p.stem:max([int(s) for s in p.read_text().splitlines() if s.isdigit()] or [0]) for p in (R/'logs').glob('*.watch')}
ver={'all_input_hashes_unchanged':before==after,'hashed_input_count':len(before),'extracted_source_matches':True,'packet_sha256':after[str(D/'Lean-packet.zip')],'candidate_sha256':after[str(D/'CANDIDATE.md')],'source_sha256':hashlib.sha256(src.encode()).hexdigest(),'raw_sha256':hashlib.sha256(raw).hexdigest(),'corpus_line_151_matches_raw':True,'mathlib_revision':mathlib['rev'],'package_manifest_sha256':hashlib.sha256(manifest.read_bytes()).hexdigest(),'source_scan':scan,'process_exits':statuses,'sampled_peak_group_RSS_KiB':peaks,'pair_order5_completed':False,'pair_order5_status':'exit 137 at process cap; no completed order-5 pair-check claim','heavy_concurrency':1,'allowed_axioms':['propext','Classical.choice','Quot.sound']}
(R/'verification.json').write_text(json.dumps(ver,indent=2));print(json.dumps(ver,indent=2))
review={'mathdb_id':360905,'role':'independent adversarial and formal-fidelity reviewer','recommendation':'HOLD','credit':0,'root_decides':True,'gates':{'A':{'verdict':'PASS','reason':'Original conjecture and v1 match literal endpoint; full journal-version comparison tracked in D.'},'B':{'verdict':'PASS','reason':'Independent general argument; all labeled graphs/orientations through n=6 and pair/set witnesses through n=4 pass.'},'C':{'verdict':'PASS','reason':'Fresh strict rebuild, leanchecker Interpolation, 38-declaration audit and allowed axiom closure pass.'},'D':{'verdict':'FAIL','reason':'Required primary-body comparisons and citing-work coverage incomplete; no prior general proof found.'},'E':{'verdict':'QUALIFIED_PASS','reason':'Forced-head step overcomes a real stalled-flip obstruction; eligibility conditional on source-level routine-adaptation comparison.'}},'missing_evidence':[{'item':'Original ordinary-domination interpolation proof','source':'Chartrand–VanderJagt–Yue, Congr. Numer. 119 (1996), 51–63','required':'Compare proof moves, validity obstruction and stalled-case lemma against Interpolation.lean:36-68.'},{'item':'Full published source version','source':'Anderson–Dravec–Johnston–Kuenzel, DAM 382 (2026), 48–59, DOI 10.1016/j.dam.2025.11.031','required':'Inspect full Conjecture 3.1 context and machinery against the sole arXiv v1.'},{'item':'Bounded citing-work coverage','required':'Use an accessible route other than the denied OpenAlex endpoint and inspect potentially resolving primary items.'}],'access_limits':['OpenAlex HTTP 429, no retry','CiteSeer multipartite PDF HTTP 404','Crossref, Semantic Scholar, arXiv search API and ScienceDirect not requested pursuant to brief','No full 1996 ordinary-domination article or 2026 Anderson journal PDF obtained'],'proof_registry':{'lean_pool_head':'01db1d7049cf9668bda1e9e106875ee1278b43e6','current_tree_verified':True,'candidate_files':10,'github_repository_queries':3},'artifacts':{'report':'REVIEW.md','verification':'verification.json','input_hashes_before':'inputs-before.json','input_hashes_after':'inputs-after.json','scripts':'scripts/','logs':'logs/','registry':'registry.json'},'independent_checks':{'n6_admissible_graphs':25418,'n6_valid_orientations':5545708,'spectrum_gaps':0,'pair_order4_checks':4248,'pair_order4_safe_witnesses':7488,'pair_order5':'capped exit 137; not claimed'},'hashes':{'candidate':ver['candidate_sha256'],'packet':ver['packet_sha256'],'lean_source':ver['source_sha256']}}
(R/'review.json').write_text(json.dumps(review,indent=2,ensure_ascii=False)+'\n')
