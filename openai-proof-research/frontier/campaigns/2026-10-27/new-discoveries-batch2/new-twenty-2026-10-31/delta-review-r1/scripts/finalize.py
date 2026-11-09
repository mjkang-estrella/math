import json,pathlib,hashlib
P=pathlib.Path(__file__).resolve().parents[1]
r=json.loads((P/'recomputation.json').read_text())
before=(P/'inputs-before.sha256').read_bytes();after=(P/'inputs-after.sha256').read_bytes();assert before==after
review={
 'schema_version':1,'mathdb_id':352253,'review_type':'INDEPENDENT_ADVERSARIAL_REVIEW_NOT_ACCEPTANCE','date_utc':'2026-11-04','overall':'PROCEED','credit':0,'root_decides':True,
 'gates':{
 'A':{'verdict':'QUALIFIED_PASS','finding':'Candidate survives faithful illustrated chain semantics, including edge-injective vertex coincidences. Discovery incidence bridge is inadequate and must be replaced.','references':['../expanded-corpus-r153/sources/delta-journal.txt:194-204','../expanded-corpus-r153/sources/delta-journal.txt:1140-1144','../expanded-corpus-r153/sources/delta-journal.txt:1550-1573','scripts/recompute.py:143-187']},
 'B':{'verdict':'PASS','finding':'No printed Figure 14 gadget in initial Gprime; source does not supply the pure-minimum doubled-input bridge. Printed c/g gadgets appear temporarily after expansion; seven-move shorter witness avoids a commuting inverse detour.','references':['../expanded-corpus-r153/sources/delta-journal.txt:1296-1468','../expanded-corpus-r153/sources/delta-journal.txt:1525-1573','scripts/recompute.py:79-133']},
 'C':{'verdict':'PASS','finding':'Independent complete DAG and legal traces verified; all 25 labelled minima are chain-free and nonminimal.','references':['scripts/recompute.py:5-58','scripts/recompute.py:143-179','recomputation.json','logs/recompute.log']},
 'D':{'verdict':'QUALIFIED_PASS','finding':'No prior resolution located. Two OpenAlex citing works, author listings and relevant later primary texts checked; live registry heads and path screening checked. Not universal novelty clearance. Toroidal citing paper full body not inspected; registry screening is path-level.','references':['logs/inspect.log','logs/fetch-review.log','logs/fetch-review2.log','logs/fetch-review3.log','logs/fetch-review4.log','logs/web-search.json']},
 'E':{'verdict':'QUALIFIED_PASS','finding':'Recommend formalisation as more than a printed-gadget bridge; significance remains root decision. Partial Lean recompiles but no literal endpoint exists; replace chain theorem bridge and certify closure DAG.','references':['../expanded-corpus-r153/scripts/delta.py:43-69','../expanded-corpus-r153/lean/Delta153.lean:48-73','../expanded-corpus-r153/lean/Soundness.lean:3-27','../expanded-corpus-r153/lean/PureCheck.lean:6','logs/lean-delta.log','logs/lean-soundness.log']}
 },
 'independent_results':{k:r[k] for k in ['states','arcs','orders','min_order','minimum_states','faithful_chain_Gprime','faithful_chain_free_minima','figure14_matches','seven_move_witness','initial_hypotheses']},
 'critical_objection':{'type':'incorrect_general_chain_incidence_bridge','location':'../expanded-corpus-r153/lean/Delta153.lean:63-69','example':'An internal double attachment can coincide with a triangle apex, producing an internal triple connection.','repaired_ordinary_check':'scripts/recompute.py:143-187','candidate_still_survives':True},
 'lean':{'version':'4.34.1','mathlib_pin':'d13f23b723b8a846827a245b89c10fc7d3f11612','recompiled_modules':['Delta153','Soundness'],'reported_axioms':['propext','Quot.sound'],'full_transitive_audit':False,'literal_endpoint_complete':False,'leanchecker_invoked':False,'unproved_attempt_retried':False,'next_steps':['Define source chain with edge-injective vertex identifications and prove short local absence obstruction.','Prove generic closed finite-state certificate soundness for PureReach.','Kernel-check 2328-state, 9846-arc closure in bounded chunks.','Certify doubled-cubic witness, initial pure path and wellformedness bridges.','Assemble exact conjecture negation and perform complete axiom audit and clean extracted replay.'],'estimated_effort':'Moderate: 1-3 focused working days; not an established resource bound.'},
 'registry_heads':{'openai_math':'4eaee87548250b2682affda7d05d947c05554bae','omega':'8e15c484cf5786fe69fef0627fd84a63cfeb5942'},
 'input_integrity':{'scope':'All files under expanded-corpus-r153','before_manifest':'inputs-before.sha256','after_manifest':'inputs-after.sha256','unchanged':True,'manifest_sha256':hashlib.sha256(before).hexdigest(),'diff_log':'logs/input-hash-diff.log','download_receipts':'downloads/request-*/receipt.json'},
 'resources':{'wrapper':'scripts/cap.sh','rss_limit_KiB':6291456,'cpus':[0,1],'cpu_seconds':120,'wall_seconds':140,'MALLOC_ARENA_MAX':2,'python_isolated':True,'lean_memory_flag':'-M3500','one_heavy_process_at_a_time':True,'background_jobs_remaining':False},
 'conduct':{'child_agents':0,'writes_only_in_review_lane':True,'discovery_scripts_executed':False,'git_used':False,'browser_tabs':False,'publication_upload_or_external_messages':False,'forbidden_services_queried':False,'access_denial_retries':0,'tls_verification_disabled':False},
 'deliverables':['REVIEW.md','review.json','recomputation.json','scripts/','logs/','downloads/','inputs-before.sha256','inputs-after.sha256']
}
(P/'review.json').write_text(json.dumps(review,indent=2)+'\n')
assert set(review['gates'])==set('ABCDE')
assert r['faithful_chain_free_minima']==25 and r['faithful_chain_Gprime'] is None
for k in ['lean-delta.log','lean-soundness.log','recompute.log']:
 assert 'resource_exit=0' in (P/'logs'/k).read_text()
print('Validated review.json, independent results, successful capped runs, and unchanged input manifests.')
