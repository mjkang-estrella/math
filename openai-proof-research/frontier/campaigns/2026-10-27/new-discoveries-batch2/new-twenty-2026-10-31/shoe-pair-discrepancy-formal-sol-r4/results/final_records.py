from pathlib import Path
import json,hashlib,subprocess
h=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,d):
    text=d if isinstance(d,str) else json.dumps(d,indent=2,sort_keys=True)
    subprocess.run(['python3','-I','-B','write_lane.py',p],input=text,text=True,check=True)
plan=json.loads(Path('results/PRODUCTION-PLAN.json').read_text())
receipts=[]
for p in sorted(Path('receipt').glob('*.json')):
    d=json.loads(p.read_text()); assert d['group_members_left']==[]
    receipts.append({'path':str(p),'sha256':h(p),'label':d['label'],'exit':d['exit'],
        'log':str(Path(d['log']).relative_to(Path.cwd())), 'log_sha256':h(d['log'])})
for m in plan['order']:
    assert any(r['label']=='lean_'+m and r['exit']==0 for r in receipts)
    assert any(r['label']=='leanchecker_'+m and r['exit']==0 for r in receipts)
    assert any(r['label']=='fresh_strict_'+m and r['exit']==0 for r in receipts)
    assert any(r['label']=='fresh_checker_'+m and r['exit']==0 for r in receipts)
unchanged={m:h(Path('src',m+'.lean'))==h(Path('inputs/baseline-src',m+'.lean')) for m in json.loads(Path('BASELINE-ORDER.json').read_text())['order']}
assert all(unchanged.values())
a=json.loads(Path('audit/final-reachable-report.json').read_text())
assert a['axioms']==['Classical.choice','Quot.sound','propext'] and not a['unsafe']
artifacts={}
for m in plan['order']:
    artifacts[m]={str(p):h(p) for p in [Path('src',m+'.lean'),Path('build',m+'.olean'),Path('replay/src',m+'.lean'),Path('replay/build',m+'.olean')]}
old=json.loads(Path('inputs/previous/results/CHECKPOINT.json').read_text())
state={'mathdb_id':324571,'status':'CHECKED_IMPLEMENTATION_READY_FOR_INDEPENDENT_FINAL_REVIEW_NOT_SELF_ACCEPTED',
 'technical_pass_self_assigned':False,'credit':0,'accepted':False,'campaign':'55/60 beyond39prior',
 'nat_endpoint':'Shoe.source_strict_universal_supremum',
 'countable_endpoint':'Shoe.countable_color_strict_universal_supremum',
 'paid':['20 cold baseline builds from empty build, baseline source hashes unchanged',
 'injective chronological predicates, first time and winner transport',
 'actual iid product measure and PMF coding transport',
 'actual normalized conditional pair measure transport',
 'measurable actual winner pushforward transport with explicit fallback',
 'generic probability normalization, a.s. termination and fallback independence',
 'PMF transport for conditional and winner laws',
 'subset-supremum TV equality and countable endpoint consuming Nat bound',
 'finite zero extension and outside-range zero masses',
 '28 strict+checker modules, 23 core/3 control/2 named-audit',
 '259 actual production-origin roots incl private/generated and 29367 complete reachable nodes',
 '11 exact endpoint closures, trio-only axiom union, no unsafe flags',
 '28-module fresh source-only empty-build strict+checker replay; postchecker hash equality',
 'isolated positive strict+checker0 and semantic mutation negative1',
 'updated five-page PDF, pages1-5 directly visually inspected'],
 'unpaid':['Independent final literal/source-to-Lean and mathematical proof review',
 'Independent final body-audit and manuscript review',
 'Root adjudication of source/prior/significance/process limits and acceptance/credit'],
 'baseline_unchanged':unchanged,'module_classifications':plan['classifications'],
 'module_artifact_hashes':artifacts,'completed_receipts':receipts,
 'audit':'audit/final-reachable-report.json','replay':'results/REPLAY.json',
 'paper':'output/pdf/shoe-discrepancy-completion.pdf','paper_sha256':h('output/pdf/shoe-discrepancy-completion.pdf'),
 'visual_qa':{'pages':[1,2,3,4,5],'method':'direct view_image of every rendered page','defects_observed':[]},
 'prior_limits':old['prior_limits'], 'inherited_deviations':old['deviations'],
 'continuation_deviations':['Bulk copied receipt metadata read and preserved by runner, not every entry personally displayed.',
 'Final-source Section4 TV page personally displayed late after compilation; its complete body was machine-read in mandatory input log before cold builds, and original-source TV and independent source review were displayed before builds. No claim of full personal prebuild display.',
 'Failed new strict attempts retained, including deprecated names, API arguments, missing typeclass and syntactic set rewrites; no unchanged failed retry or cap increase.'],
 'process_scope':'Per-group immutable runner caps plus sampled RSS and exact exits; empty remaining-group lists on completed receipts. Display helper has its separate explicit self-cap exception. No global cgroup assertion.',
 'first_commands':'User-specified bootstrap.py . then verify_frozen.py before',
 'frozen_after':'standalone verifier executed after these records; final result is frozen-after.json',
 'source_scope':'Own copied inputs and pinned upstream API only; no protected peer inspection, network, git, install, child agents or numerical/solver work.'}
write('results/CHECKPOINT.json',state)
write('results/324571.json',{k:v for k,v in state.items() if k not in ['completed_receipts','module_artifact_hashes']})
write('results/FAILURES.json',{'inherited':old['deviations'],'failed_audit_inputs':'inputs/failed-audit','current_nonzero_receipts':[r for r in receipts if r['exit']!=0],'expected_control_failure':'receipt/1794122374383738334_isolated-negative-coding.json','limits':state['process_scope'],'continuation_deviations':state['continuation_deviations']})
sm=json.loads(Path('inputs/previous/results/SOURCE-MAP.json').read_text())
sm['literal']='inputs/original/original/author/literal324571.jsonl'
sm['original']='inputs/original/original/author/sources/shoes.txt Sections2,4,9.1,9.2 Conjecture4eq30'
sm['final']='inputs/original/original/author/sources/shoes-final.txt Sections2,4,9.1,9.2 Conjecture4eq19'
sm['countable_transport']={'chronology':'ShoeRelabel.hasMatch_relabel_iff/firstMatch_relabel_iff/firstLength_relabel/winner_relabel_of_terminates',
 'iid':'ShoeColorMeasure.colorSampleMeasure_map',
 'winner':'ShoeColorWinner.colorWinner_measure_transport',
 'conditioning':'ShoeColorConditional.color_pair_equality_transport/colorConditionalMeasure_transport',
 'TV':'ShoeColorEndpoint.colorTV_coding/colorDiscrepancy_coding',
 'endpoint':'ShoeColorEndpoint.countable_color_strict_universal_supremum consumes sourceDiscrepancy_bound',
 'finite':'ShoeColorEndpoint.finite_zeroExtension_discrepancy + ShoeColorControls.finite_zeroExtension_outside',
 'normalization':'ShoeColorNormalization.color_ae_terminates/colorConditionalMeasure_probability/color_fallback_ae',
 'PMF':'ShoeColorPMF.colorConditional_toPMF_transport/colorWinner_toPMF_transport'}
sm['unpaid']=state['unpaid']; write('results/SOURCE-MAP.json',sm)
write('SUMMARY.md','''# Actual disk state - MathDB 324571

Checked countable-color endpoint: `Shoe.countable_color_strict_universal_supremum`, consuming the checked Nat bound through proved iid, conditioning, chronological-winner and subset-TV transport. Finite zero extension, normalization, a.s. fallback and PMF transport are checked.

All 28 production proof/control/named-audit modules passed strict Lean and leanchecker, then a fresh source-only empty-build strict+checker replay. Postchecker source hashes agree. Baseline20 sources are unchanged. The repaired audit completed259 production-origin roots and29367 reachable nodes, with11 exact endpoint closures, only propext/Classical.choice/Quot.sound, and no unsafe flags. Original three -6 audit failures remain in immutable copied inputs.

Five-page updated PDF: `output/pdf/shoe-discrepancy-completion.pdf`; all five rendered pages directly visually inspected. Isolated positive control strict+checker0, mutated negative exit1. Full receipts, failures, artifact hashes, module classification and scope limits are in results/CHECKPOINT.json. Bulk receipt metadata were machine-read; final-source TV page personal display occurred late, explicitly retained as a process limitation.

No self-assigned technical PASS, acceptance or credit. Campaign55/60 beyond39. Unpaid: independent final source/proof/deep-body/manuscript review and root adjudication/acceptance. Galbraith-Holmes2012 body404/unread and bounded prior-art limits persist. Frozen-after and terminal SHA manifest close this packet separately.
''')
print('FINAL_RECORDS',len(receipts),'completed receipts;28 checked modules; unpaid independent review/root adjudication')
