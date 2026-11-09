import pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).resolve().parents[1]
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert (L/'inputs-before.sha256').read_bytes()==(L/'inputs-after.sha256').read_bytes()
assert 'META local=23 flagged=[]' in (L/'logs/Audit.strict.log').read_text()
assert (L/'logs/replay.log').read_text().splitlines()==['Definitions PASS','Witness PASS','Audit PASS']
D=L.parent/'expanded-corpus-r158'
r=json.loads((D/'results.json').read_text())
(L/'logs/results-reviewed.json').write_text(json.dumps(r,indent=2)+'\n')
review={
 'schema_version':1,'mathdb_id':369421,'review_date_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'role':'independent adversarial and formal-fidelity review; not acceptance',
 'overall_recommendation':'PROCEED TO ACCEPTANCE PACKAGING','accepted':False,'credit_awarded':0,
 'gates':{
  'A':{'verdict':'PASS','reason':'Exact universal Cartesian-product conjecture and source conventions match; witness lies at (3,5).','references':['downloads/source-pdf/text.txt:69-93','downloads/source-pdf/text.txt:370-391','packet/Definitions.lean:6-25']},
  'B':{'verdict':'PASS','reason':'Own dual check of 105 pairs; 30 edges and 75 nonedges; 15 counts all 3; Lean coordinate literal agrees.','references':['scripts/check.py','pair-check.json','logs/check.log'],'neighbor_certificates':[[3,3],[3,4]],'neighbor_heuristics':{'cases':[[4,4],[3,6]],'result':'INCONCLUSIVE; not nonexistence proofs'}},
  'C':{'verdict':'PASS','reason':'Own safe extraction, all three strict builds and explicit-module leanchecker replays succeeded; literal endpoint and minimum bridge faithful.','modules':['Definitions','Witness','Audit'],'endpoint':'Toroidal.mathdb_369421 : ¬ Toroidal.Conjecture1','local_declarations':23,'flagged_metadata':0,'axioms':['propext','Classical.choice','Quot.sound'],'references':['scripts/extract.py','scripts/replay.sh','logs/replay.log','logs/Audit.strict.log']},
  'D':{'verdict':'QUALIFIED_PASS','reason':'No target result located in bounded primary-source and live registry screen. Positive accepted-paper linkage, but accepted manuscript unread. Generic SMT search is established prior methodology.','qualifications':['Exact accepted-body retention unverified: staff-only manuscript embargoed until 2099.','Bounded searches and incomplete citation indexing cannot establish absolute priority.','2019 overlapping-author positional SMT tool already searches arbitrary input graphs; see REVIEW.md D.6.'],'additional_primary_findings':['HAL hal-05800339 proves Q4 requires 4 and gives bounds on Q5-Q8, not a C3 square C5 result.','2019 computational census covers connected graphs through 9 vertices, not this 15-vertex graph.'],'openalex':{'source':'W4414421767','citing_query_count':0,'coverage_caveat':'Known 2026 chessboard citation missing.'},'registries':{'openai_math_head':'4eaee87548250b2682affda7d05d947c05554bae','omega_head':'c96824c9d53dc7f8498b7888f9552e29c742f211','screen':'Complete preprints, D5, Problems subtree path/topic screen; not whole-body review.'}},
  'E':{'verdict':'QUALIFIED_PASS','reason':'Complete explicit-conjecture refutation; no direct subsuming theorem or printed target recipe identified. Root must judge significance with generic-SMT methodological proximity disclosed.','root_decision_required':True}
 },
 'input_integrity':{'files':176,'all_unchanged':True,'before_manifest':'inputs-before.sha256','after_manifest':'inputs-after.sha256','manifest_sha256':h(L/'inputs-before.sha256'),'packet_sha256':'9f16ff5afa9a23b693443c0916507a8103bef5f23e431ca6c39e8cb4e7318200','primary_pdf_sha256':h(L/'downloads/source-pdf/body')},
 'resources':{'wrapper':'scripts/capped.sh','rss_limit_bytes':6*1024**3,'cpu_seconds':120,'wall_seconds':140,'cpus':[0,1],'malloc_arena_max':2,'lean_memory_flag':'-M3500','python_isolated':True,'one_heavy_process_at_a_time':True,'background_jobs_at_handback':0},
 'lean_version':'4.34.1','mathlib_pin':'d13f23b723b8a846827a245b89c10fc7d3f11612','upstream_oleans_trusted':True,
 'remaining_acceptance_work':['Root adjudicates substantive credit and retention qualifications.','Root prepares and reviews campaign acceptance manuscript/package.'],
 'report':'REVIEW.md'
}
(L/'review.json').write_text(json.dumps(review,indent=2)+'\n')
# Generate line-reference extracts for auditing without depending on mutable rendering.
with (L/'logs/source-scan.log').open('w') as f:
 import re
 for p in sorted((L/'packet').glob('*.lean')):
  for i,line in enumerate(p.read_text().splitlines(),1):
   if re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|extern|implemented_by|run_cmd)\b',line):f.write(f'{p.name}:{i}:{line}\n')
print(json.dumps({'recommendation':review['overall_recommendation'],'gates':{k:v['verdict'] for k,v in review['gates'].items()},'inputs_unchanged':True}))
