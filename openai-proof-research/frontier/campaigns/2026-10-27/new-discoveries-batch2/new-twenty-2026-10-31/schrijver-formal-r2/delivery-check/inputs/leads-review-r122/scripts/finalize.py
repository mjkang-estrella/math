from pathlib import Path
import json,hashlib,datetime
lane=Path.cwd();src=lane.parent/'expanded-corpus-r122'
before=json.loads((lane/'inputs-before.json').read_text())
after={str(p.relative_to(src)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(src.rglob('*')) if p.is_file()}
(lane/'inputs-after.json').write_text(json.dumps(after,indent=2))
integrity=dict(files_before=len(before),files_after=len(after),unchanged=before==after,changed=[k for k in set(before)|set(after) if before.get(k)!=after.get(k)],manifest_before_sha256=hashlib.sha256((lane/'inputs-before.json').read_bytes()).hexdigest(),manifest_after_sha256=hashlib.sha256((lane/'inputs-after.json').read_bytes()).hexdigest())
(lane/'outputs/input-integrity.json').write_text(json.dumps(integrity,indent=2))
assert integrity['unchanged'],integrity
rows={}
for p in sorted((lane/'logs').glob('graphs-k*.log')):
    for line in p.read_text().splitlines():
        try:r=json.loads(line)
        except ValueError:continue
        if 'diameter' in r:rows[r['n'],r['k']]=r
(lane/'outputs/graph-combined.json').write_text(json.dumps(list(rows.values()),indent=2))
checks=json.loads((lane/'outputs/certificate-checks.json').read_text())
assert len(checks)==7 and all(r['all_orbits_covered'] for r in checks)
review={
 'lane':'leads-review-r122','reviewer_role':'independent advisory reviewer; root decides','date_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'accepted_credit':0,'self_accepted':False,
 'input_integrity':integrity,'input_hash_files':['inputs-before.json','inputs-after.json'],
 'leads':{
  '352905':{'recommendation':'HOLD','recomputation':{'verified':True,'b':24,'legs':[600,24,1],'vertices':626,'partition':{'6':1,'5':124},'coefficient_factored':'-2499 * 4^122','small_spiders_checked':11,'small_spider_vertex_bound':8,'semantic_check':'proper colorings converted exactly from monomial basis to elementary basis','evidence':'outputs/spider-review.json'},'prior_art':{'journal_body_cleared':False,'exact_prior_refutation_found':False,'worldwide_novelty_claim':False,'openalex_journal_citing_works':4,'recent_bodies_not_cleared':['2610.03464','2610.39481']},'significance':'Potential genuine conjecture refutation via composite-(b+1) coefficient support; arithmetic uses source method and root must adjudicate strict routine-bridge objection. Shortness alone does not establish ineligibility.','remaining_gates':['journal-body comparison','latest relevant bodies','significance ruling','current proof-registry body clearance','literal CSF Lean development']},
  '352827':{'recommendation':'HOLD','recomputation':{'verified':True,'requested_diameters':[{'n':n,'k':k,'diameter':rows[n,k]['diameter']} for n,k in [(14,6),(15,6),(16,7),(17,7),(18,8),(19,8),(22,10),(23,10)]],'independent_r3_counterexamples':[{'k':12,'r':3,'diameters':[8,6],'vertices':[819,3185]},{'k':13,'r':3,'diameters':[9,7],'vertices':[1015,4200]}],'certificates_checked':checks,'table_coverage':'k 2..6 finite ranges and first diameter-2 tail instance; k7 n15..24; n25 timed out and n26 over enumeration cap','full_coverage':'outputs/graph-combined.json'},'source_error':{'theorem':'arXiv v2 Theorem 6','location':'page 19','error':'substituting j-i = k-floor(3k/4)-1 gives k+i+1-j = floor(3k/4)+2, not floor(3k/4)','v1_has_this_theorem':False,'sg14_6_distance5_pair':[[1,3,5,7,9,12],[1,3,6,8,10,12]],'distance_lower_proof':'disjoint closed radius-2 balls with 17 and 13 vertices','original_k10_route_credit':0,'printed_7_minus_computed_6':1},'prior_art':{'journal_body_cleared':False,'exact_prior_refutation_found':False,'worldwide_novelty_claim':False,'openalex_journal_citing_works':1},'significance':'Original r2 route is a source-internal correction, but k12,r3 and k13,r3 counterexamples independently violate Conjecture2 without using Theorem6. Prefer k12,r3 for any later formalization.','remaining_gates':['journal conjecture scope','bounded prior-art completion','current proof-registry body clearance','literal graph-distance Lean certificate bridge']}},
 'resource_policy':{'cpus':[0,1],'cpu_seconds':120,'wall_seconds':140,'kill_fallback_seconds':2,'address_space_bytes':6*1024**3,'malloc_arena_max':2,'python_isolated':True,'all_writes_lane_local':True,'exceptions':['initial read-only shell commands were not wrapped','brief numerical overlap after k6 yielded while k8..16 ran'],'timeouts':['k7 cumulative table run','k7 n25 isolated run']},
 'prohibited_actions':{'child_agents':False,'lean':False,'git':False,'uploads':False,'external_messages':False,'browser_tabs':False,'shared_ledger_edits':False},
 'registries':{'openai_head':'4eaee87548250b2682affda7d05d947c05554bae','omega_head':'b715a9e2e5f439f86a18f5ed9511efbe75c6061d','omega_tree_truncated':True,'omega_tree_entries':56432,'complete_current_body_clearance':False},
 'reports':['REVIEW.md','review.json'],'note':'Recommendations only. No Lean endpoint, acceptance, or novelty clearance is claimed.'}
(lane/'review.json').write_text(json.dumps(review,indent=2))
manifest={str(p.relative_to(lane)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(lane.rglob('*')) if p.is_file() and p.name!='manifest-review.json' and not str(p.relative_to(lane)).startswith('logs/finalize')}
(lane/'manifest-review.json').write_text(json.dumps(manifest,indent=2))
print(json.dumps(dict(integrity=integrity,certificates=len(checks),graph_instances=len(rows),recommendations={k:v['recommendation'] for k,v in review['leads'].items()}),indent=2))
