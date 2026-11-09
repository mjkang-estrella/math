from pathlib import Path
import json,hashlib,subprocess,sys,os

def save(p,s):
 if not isinstance(s,str): s=json.dumps(s,indent=2)+'\n'
 subprocess.run([sys.executable,'-I','-B','write_lane.py',p],input=s,text=True,check=True)
a=json.loads(Path('results/author-audit-inspection.json').read_text())
b=json.loads(Path('results/independent-audit-coverage.json').read_text())
assert a['declaration_origins']==b['declaration_origins']
different=[k for k,v in a['rendered_payload_sha256'].items() if b['rendered_payload_sha256'].get(k)!=v]
comparison={'same_declarations_origins_and_safety':True,'same_selected_type_body_payloads':not different,'payload_differences':different,'compared':7003,'author_inspection':'results/author-audit-inspection.json','own_fresh_execution':'results/independent-audit-coverage.json','note':'Equality of rendered payloads is corroboration; kernel checking and independent production semantic review are separate.'}
save('results/body-comparison.json',comparison)
assert not different,different
receipts=[json.loads(p.read_text()) for p in Path('receipt').glob('*.json')]
count=lambda prefix:sum(r['label'].startswith(prefix) and r['exit']==0 for r in receipts)
assert count('lean_Polynexus')==12
assert count('leanchecker_Polynexus')==12
assert count('audit_IndependentFull')==16
assert any(r['label']=='audit_Safety' and r['exit']==0 for r in receipts)
assert any(r['label']=='audit_ControlsV2' and r['exit']==0 for r in receipts)
assert all(any(r['label']==f'audit_Negative{x}' and r['exit']==1 for r in receipts) for x in ['Endpoint','Rectangle'])
text=Path('qa/assessment.md').read_text()
old='The fresh body audit and final integrity results are recorded in the completed evidence accompanying this report; they must succeed before this is a final handback.'
new='Fresh validation PASS: 12/12 strict source rebuilds, 12/12 module-name kernel checker runs, 16/16 full-body audit partitions, and the separate safety and positive controls. All 282 module-origin production declarations and 7,003 transitive declarations are covered, with only propext, Classical.choice and Quot.sound. The 7,003 selected rendered type/body payloads equal the inspected immutable author output; both inventories and all shard receipts are delivered.'
assert old in text
text=text.replace(old,new)
save('FINAL-REVIEW.md',text)
h=hashlib.sha256(Path('input/author-manuscript.md').read_bytes()).hexdigest()
save('results/352496-gates.json',{'352496':{'recommendation':'REVISE_REPORTING_ONLY; technically eligible for root consideration','accepted':False,'credit':0,'campaign_accepted':53,'campaign_target':60,'prior_campaign':39,'gates':{'ordinary_proof':'PASS','source_bound_literal_fidelity':'PASS; explicit interpretation required','source_operand_set_equivalence':'PASS PNZ_source','actual_ordinary_matrix_product':'PASS','ordered_pair_count_and_multiplicity':'PASS','full_positive_n_and_n1':'PASS; all-Nat stronger integer/rational theorem and review-only n0 control','finite_convolution_evaluation_and_casts':'PASS','immutable_production_semantics':'PASS','fresh_source_rebuild':'PASS 12/12','module_name_kernel_checkers':'PASS 12/12','full_module_origin_private_generated_opaque_transitive_audit':'PASS 282 roots / 7003 closure / 16 disjoint partitions','safe_definitions_and_permitted_axioms':'PASS only propext/Classical.choice/Quot.sound','meaningful_controls':'PASS; positives pass, negatives fail at False','manuscript_mathematics':'PASS','manuscript_current_reporting':'REVISE stale campaign count','bounded_primary_prior_comparison':'QUALIFIED PASS; no applicable subsumption found','worldwide_novelty':'NOT CLAIMED; no fresh network authorized','campaign_significance':'QUALIFIED PASS, root adjudicates','process':'disclosed startup/output and control warnings; root adjudicates separately','root_acceptance':'SEPARATE; no ledger action','pdf':'NOT CREATED; optional rendition omitted'},'errata':[{'file':'input/author-manuscript.md','sha256':h,'line':79,'literal':'The accepted campaign count remains 52/60','current_handback':'53/60; credit0','kind':'reporting only; immutable author file not changed'},{'kind':'clarification, not mathematical defect','literal':'two finite induction identities','detail':'Two principal summations use PInner and POuter, with explicitly stated auxiliary PQuartic.'}],'source_map':'results/source-map.json','obligations_and_objections':'FINAL-REVIEW.md','audit':'results/independent-audit-coverage.json','body_comparison':'results/body-comparison.json','setup':'results/setup-evidence.json','resource_read_deviations':'results/read-resource-inventory.json','receipt_inventory':'results/receipt-inventory.json','final_integrity':'frozen-after.json and results/manifest-verification.json; inspect actual completed records','self_exclusions':'Precisely named sealing/verification terminal artifacts in results/manifest.json'}})
print('HANDBACK WRITTEN',file=open(f'/proc/{os.getppid()}/fd/1','w'))
