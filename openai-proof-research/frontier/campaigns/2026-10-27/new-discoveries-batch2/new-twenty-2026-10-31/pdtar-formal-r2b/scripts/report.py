"""Generate handback metadata only after a successful complete extracted replay."""
import hashlib,json,pathlib,re,time
D=pathlib.Path(__file__).resolve().parents[1]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((D/'manifest.json').read_text());s=json.loads((D/'replay-state.json').read_text())
assert s['next']==29 and len(s['steps'])==29
E=D/'replay/extracted'
before=json.loads((D/'frozen-before.json').read_text())
after={n:sha(D/'PDTAR'/n) for n in before}
assert before==after
for n,h in before.items():
 assert sha(E/'PDTAR'/n)==h
 assert sha(D.parent/'pdtar-formal-r1/PDTAR'/n)==h
(D/'frozen-after.json').write_text(json.dumps(after,indent=2)+'\n')
audit=(E/'logs/audit.log').read_text()
assert 'AUDIT_TOTAL 159; violations 0' in audit
names=re.findall(r'^DECL (\S+) kind=(\S+)',audit,re.M)
assert len(names)==159 and len({n for n,k in names})==159
kinds={k:sum(1 for n,j in names if j==k) for n,k in names}
modules=[]
for n in m['modules']:
 p=D/'PDTAR'/f'{n}.lean'
 assert sha(p)==m['files'][str(p.relative_to(D))]
 assert sha(E/'PDTAR'/p.name)==sha(p)
 modules.append({'module':'PDTAR.'+n,'path':str(p.relative_to(D)),'sha256':sha(p),'lines':len(p.read_text().splitlines()),'frozen':p.name in before,'strict_compile':True,'leanchecker':True})
receipts=[json.loads(p.read_text()) for p in (E/'logs').glob('*.receipt.json')]
assert len(receipts)==29 and all(r['cap_reason'] is None for r in receipts)
reads=['pdtar-formal-r1/SUMMARY.md','pdtar-formal-r1/results.json','pdtar-formal-r1/STATEMENT-CORRESPONDENCE.md','pdtar-proof-r1/PROOF.md','pdtar-proof-r1/LEAN-PLAN.md','pdtar-review-r1/REVIEW.md','pdtar-proof-r1/sources/r119-cached/2406.05509-CFH24TARarxiv.tex']
result={'lane':'pdtar-formal-r2b','mathdb_id':353203,'status':'REDUCTION_CLOSED_AWAITING_ROOT_REVIEW','self_accepted':False,'credit_claimed':0,'endpoint':{'name':'PDTAR.reductionRemaining','type':'PDTAR.ReductionRemaining','unconditional':True,'extra_hypotheses':[],'full_mathdb_endpoint_closed_by_this_lane':False},'proof_route':'Complete Hamming-walk isometry replacement; co-singleton coordinate basis; affine reconstruction; upward-family flip normalization; literal-round graph transport. No cube interval classification assumed.','remaining_props':[],'discharged_specifications':['PDTAR.ReductionHammingRemaining by PDTAR.reductionHammingRemaining'],'modules':modules,'total_lean_lines':sum(x['lines'] for x in modules),'new_modules':7,'new_lean_lines':sum(x['lines'] for x in modules if not x['frozen']),'frozen_base':{'archive_sha256':'39ebb60a1e30c558cc2a978dc423a27d3969006bbf21904a788f97a17b4b9b69','before':before,'after':after,'identical':True,'sibling_original_sources_unchanged':True},'toolchain':{'lean':'4.34.1','mathlib_revision_as_supplied':m['mathlib_revision'],'pins':m['pins'],'cache_read_only':True},'validation':{'fresh_extraction':'replay/extracted','steps_completed':29,'steps_total':29,'strict_compile_modules':13,'leanchecker_modules':13,'audit_total':159,'audit_kinds':kinds,'audit_violations':0,'audit_checks':['all module-origin declarations including generated/private','unsafe','partial','_unsafe_rec','implemented_by','extern','transitive axioms'],'allowed_axioms':['propext','Classical.choice','Quot.sound'],'negative_controls':['degree strictly greater than base order rejected by omega','false cube toggle equality rejected as False'],'peak_sampled_process_rss_bytes':max(r['sampled_process_rss_peak_bytes'] for r in receipts),'max_step_wall_seconds':max(r['wall_seconds'] for r in receipts),'rss_sampling_seconds':0.05,'unsampled_transients_excluded':False,'logs':'replay/extracted/logs','historical_attempts':['logs','replay-attempt1','replay-attempt1-state.json'],'resource_limits':'At most 2 CPUs; CPU 120 s; wall 140 s; sampled RSS 6 GiB; AS 16 GiB; MALLOC_ARENA_MAX=2; -j1 -M3500; serial'},'artifacts':{n:{'path':n,'sha256':sha(D/n)} for n in ['pdtar-source.zip','manifest.json','replay-state.json','replay/extracted/logs/audit.log','SUMMARY.md','REPRODUCE.md']},'source_reading_hashes':{n:sha(D.parent/n) for n in reads},'task_wording_correction':'Degree can equal the base order away from the full set (e.g. the 2-sets for K3). The proof uses only the valid bound and attainment at the full set.','next_step':'Root independently reviews and combines with r2a; no reduction sub-lemma remains open.','external_actions':False,'child_agents':False,'git_operations':False,'shared_ledger_edits':False,'background_jobs_remaining':False,'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())}
(D/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'modules':len(modules),'audit_total':159,'zip_sha256':sha(D/'pdtar-source.zip')}))
