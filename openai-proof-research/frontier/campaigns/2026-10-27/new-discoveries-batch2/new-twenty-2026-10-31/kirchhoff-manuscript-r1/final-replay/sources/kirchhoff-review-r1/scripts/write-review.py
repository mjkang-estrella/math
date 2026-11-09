from pathlib import Path
import json,datetime,hashlib,os
D=Path(__file__).resolve().parents[1]
r={'349441':{
 'reviewer_role':'independent adversarial review sub-agent','reviewed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'overall_verdict':'HOLD','recommendation':'Do not accept or award campaign credit until novelty gaps are cleared. Retain the spectral refutation as a substantive candidate.',
 'credit':0,
 'gates':{
  'A':{'verdict':'QUALIFIED_PASS','root_ruling_supported':True,'physical_all_pairs_defined':False,'both_source_algebraic_readings_refuted':True,'every_repaired_physical_reading_refuted':False,'authors_computed_spectral':'Strong inference from exact replication, not recovered implementation.','MP_data_contradiction':{'minimum_order':5,'graph':'K4 plus pendant vertex','R1':'33856/4317','R0':'17/2'},'source_objects_checked':['(3.8)','Definition 4.1','Lemma 4.2 (4.3)','Definition 4.5','Lemma 4.6','n <= 8 computational paragraph','Conjecture 4.13','MathDB raw 349441','all requested Lean definitions']},
  'B':{'verdict':'PASS','independent_exact_code':True,'all_Penrose_and_group_equations_checked_for_witnesses':True,'values':{'MP':{'-1':'21930927/278132','0':'370/3','1':'515538204/7137235'},'spectral':{'-1':'1096887/11036','0':'370/3','1':'1696684/14035'}},'minimum_MP_order':5,'minimum_spectral_order':{'global_lower_bound':9,'global_upper_bound':11,'tested_clique_pendant_family_minimum':11,'global_minimum_proved':False},'exhaustive_connected_5_to_8':json.loads((D/'outputs/exhaustive-summary.json').read_text())},
  'C':{'verdict':'PASS','fresh_safe_extraction':True,'strict_four_module_rebuild':True,'leanchecker_four_modules':True,'declarations_audited_candidate':176,'declarations_including_reviewer_restatement':179,'full_type_and_opaque_body_AST_logged':True,'unsafe_partial_found':False,'axioms':['propext','Classical.choice','Quot.sound'],'own_restatement':'fresh/formal/ReviewerRestatement.lean','negative_control_caveat':'Supplied failures include missing decidability and stuck reduction; reviewer separately proved negations of the altered certificate conditions in ReviewerControls.lean.','initial_checker_infrastructure_failure':'PATH omitted lean; all checkers successfully rerun after fixing review runner.'},
  'D':{'verdict':'HOLD','verified_prior_refutation_found':False,'novelty_cleared':False,'journal_body_verified':True,'later_advection_author_body_screened':True,'citing_van_Gennip_Budd_body_screened':True,'Chaos_body_screened':'partial only','Miranda_2026_thesis_body_screened':False,'complete_current_registry_screen':False,'registry_route':'/commits/HEAD only','heads':{k:json.loads((D/f'outputs/{k}-head.json').read_text())['sha'] for k in ['openai','omega']},'access_denials_retried':False},
  'E':{'verdict':'QUALIFIED_PASS','conditional_on':'Novelty clearance at gate D','spectral_failure_beyond_authors_tested_range':True,'MP_only_correction_credit':0,'single_result_only':True,'reason':'Spectral ordering fails independently of the incorrect MP similarity identity, after the full reported finite range passes. No unconditional not-known verdict is justified.'}
 },
 'objections':[
  {'severity':'blocking','issue':'Incomplete current-registry semantic coverage; Omega head advanced during review. HEAD changed paths cannot clear the whole registry.'},
  {'severity':'blocking','issue':'2026 Miranda thesis unread; Chaos and author-wide later/citing coverage incomplete.'},
  {'severity':'qualification','issue':'Physical all-pairs definition is ill-posed; only the two source algebraic readings are resolved.'},
  {'severity':'qualification','issue':'Spectral minimum globally lies in [9,11]; witness minimum 11 established only for tested pendant-clique family.'},
  {'severity':'resolved_for_review','issue':'Supplied negative-control failures were not meaningful semantic checks; independent kernel-checked proofs of the false conditions were added.'},
  {'severity':'documentation_correction','issue':'A Prolegomenon is by Yves van Gennip and Jeremy Budd, not Mugnolo.'}
 ],
 'next_actions':['Read Miranda 2026 thesis and remaining relevant citing works lawfully.','Resolve a permitted complete-current-registry coverage method with root.','Keep spectral and MP readings separate and count at most one result.','Do not claim global spectral minimality or physical equivalence.'],
 'integrity':json.loads((D/'receipts/verification-summary.json').read_text()),
 'artifacts':{'report':'REVIEW.md','exact_witness':'outputs/witness-exact.json','minimal_MP':'outputs/minimal-MP-certificate.json','scripts':'scripts/','logs':'logs/','receipts':'receipts/'},
 'background_jobs_remaining':False
}}
(D/'review.json').write_text(json.dumps(r,indent=2)+'\n')
