import json,re,hashlib
from pathlib import Path
r=Path(__file__).resolve().parents[1]
before=(r/'hashes-before.txt').read_bytes(); after=(r/'hashes-after.txt').read_bytes()
assert before==after
receipts=[]
for p in sorted((r/'logs').glob('*.receipt')):
    vals={k:int(v) for k,v in re.findall(r'(exit|peak_rss_kib)=(\d+)',p.read_text())}
    receipts.append({'file':str(p.relative_to(r)),**vals})
assert max(x['peak_rss_kib'] for x in receipts)<6291456
compile_mods=['MiddleBase','MiddleSmall','MiddleWitness','MiddleFinal','MiddleAudit']
for m in compile_mods:
    for tag in ['compile-','check-']:
        rr=[x for x in receipts if x['file'].endswith(tag+m+'.receipt')]
        assert len(rr)==1 and rr[0]['exit']==0,(tag,m,rr)
for m in ['NegativeValue','NegativeAdjacency','NegativeConnected']:
    p=next((r/'logs').glob('*-negative-'+m+'.out'))
    assert 'proved that the proposition' in p.read_text() and 'is false' in p.read_text()
assert [x for x in receipts if x['file'].endswith('independent-lean-conventions.receipt')][0]['exit']==0
assert [x for x in receipts if x['file'].endswith('check-Sanity-conventions.receipt')][0]['exit']==0
out={
'mathdb_id':355217,'review_type':'INDEPENDENT_FORMAL_FIDELITY_NOT_ACCEPTANCE',
'reviewer':'Codex review lane; no child agents','completed_utc':'2026-11-04T00:04Z',
'packet':{'path':'../middle-formal-r1/middle-source.zip','sha256':'5a3e8ac8153651c55942d8f1288b50dd0c578b089c02d01c353b750b2c5bb62b','extracted_members_unchanged':True},
'verdicts':{
'A':{'verdict':'PASS','reason':'Literal graph, domination, complement conventions, attained IsLeast minima and separate connected negations match authorized scope. No vacuity or missing-minimum bridge.','references':['extracted/MiddleBase.lean:34-75','extracted/MiddleBase.lean:202-210','extracted/MiddleFinal.lean:4-52','../expanded-corpus-r139/sources/txt-2206.15439.txt:31-75,460-461']},
'B':{'verdict':'PASS','reason':'93 explicit checked exclusions plus proved coverage; generic middle counting; parent-map witnesses; direct connected refutation assembly.','references':['extracted/MiddleSmall.lean:5-413','extracted/MiddleBase.lean:99-194','extracted/MiddleWitness.lean:5-126','extracted/MiddleFinal.lean:10-52']},
'C':{'verdict':'PASS','reason':'Independent isolated Python enumeration agrees with own compiled Lean examples: values 4 and 4 under both conventions; middle order 19 and size 48; false sets rejected.','references':['scripts/sanity.py','sanity.json','Sanity.lean:4-32']},
'D':{'verdict':'PASS','reason':'Bounded strict serial compile and explicit-module leanchecker for five local closure modules; endpoint axiom prints allowed; lexical and metadata audits pass. Root decisive replay not claimed.','references':['scripts/checks.sh','scripts/run.sh','scripts/verify.py','audit-summary.json','extracted/audit.jsonl','Sanity.lean:34-41','logs/']},
'E':{'verdict':'QUALIFIED_PASS','reason':'Finite formal result ready for root consideration; final manuscript must satisfy eight integration conditions, distinguish formal result from family and computation, and retain bounded access and modest significance.','references':['REVIEW.md: E. Manuscript readiness','../expanded-corpus-r139/work355217/PROOF.md:51-73,75-96','../middle-review-r1/REVIEW.md:67-77,117-160,214-261','../middle-root-ruling-r1.json']}
},
'required_lean_fixes':[],
'required_manuscript_fixes':[
'Give connected G8, all 11 edges, exact attained values, witnesses, lower bounds and source statement.',
'Separate complement conventions; no credit for edgeless control or totalized convention-B value.',
'Include equality family a,b >= 1 and matching characterization for connected even order n >= 2, with ordinary proofs and explicit nonformal scope.',
'Label smallest-order uniqueness as exhaustive computation up to isomorphism; document coverage and crosschecks.',
'Record uncredited source errors at K2,2 (middle value 3) and friendship graph (original value n).',
'Keep significance modest; distinguish source ingredients, G8 lower-bound content and bounded priority claims.',
'Report pinned finite formal endpoints, audit, allowed axioms, resource limits and separate root replay.',
'Preserve dated access limits and replace obsolete uncompiled-draft descriptions in final manuscript.'
],
'input_binding':{'before':'hashes-before.txt','after':'hashes-after.txt','files':len(before.splitlines()),'identical':True,'before_manifest_sha256':hashlib.sha256(before).hexdigest(),'after_manifest_sha256':hashlib.sha256(after).hexdigest()},
'formal_check':{'lean_version':'4.34.1','mathlib_revision':'d13f23b723b8a846827a245b89c10fc7d3f11612','strict_compiled_and_leanchecked':compile_mods,'upstream_oleans_read_only':True,'upstream_source_rebuild':False,'root_decisive_replay_claimed':False,'audit':json.loads((r/'audit-summary.json').read_text())},
'semantic_check':{'values_both_conventions':[4,4],'minimum_set_counts':[8,2],'middle_vertices':19,'middle_edges':48,'all_93_small_sets_covered':True,'own_lean_examples':'PASS','initial_sanity_failure':'Missing test-local decidable middle adjacency instance; corrected. Failed log retained.'},
'resources':{'rss_limit_kib':6291456,'peak_sampled_group_rss_kib':max(x['peak_rss_kib'] for x in receipts),'cpu_limit_seconds':120,'wall_limit_seconds':140,'cpus':[0,1],'lean_memory_flag':'-M3500','MALLOC_ARENA_MAX':'2','one_review_heavy_process_at_a_time':True,'receipts':receipts},
'compliance':{'child_agents':False,'git':False,'network':False,'browser_tabs':False,'external_messages':False,'publication_or_upload':False,'shared_ledger_edits':False,'writes_outside_lane':False,'review_background_jobs_left':False},
'self_accepted':False,'credit':0,'decision_owner':'root','recommendation':'No formal-fidelity objection; manuscript conditions and root decisive replay/acceptance remain.'
}
(r/'review.json').write_text(json.dumps(out,indent=2)+'\n')
print('review.json written; 94 immutable inputs unchanged; all expected checks verified')
