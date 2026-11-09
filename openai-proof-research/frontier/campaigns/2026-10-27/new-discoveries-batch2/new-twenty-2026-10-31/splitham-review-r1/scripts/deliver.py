import hashlib,json
from pathlib import Path
p=Path(__file__).resolve().parents[1];src=p.parent/'expanded-corpus-r156'
def sha(x):return hashlib.sha256(x.read_bytes()).hexdigest()
files=['raw/373598.jsonl','results.json','CASE-373598.md','sources/373598.html','sources/373598.txt','outputs/split-search.json']
before={line.split('  ',1)[1].strip():line.split('  ',1)[0] for line in (p/'outputs/inputs-before.sha256').read_text().splitlines()}
after={line.split('  ',1)[1].strip():line.split('  ',1)[0] for line in (p/'outputs/inputs-after.sha256').read_text().splitlines()}
assert before==after
res={'schema_version':1,'mathdb_id':373598,'review_type':'INDEPENDENT_ADVERSARIAL_REVIEW_NOT_ACCEPTANCE','date_utc':'2026-11-04','overall':'HOLD','discovery_count_credit':0,'acceptance_authority':'root only',
'gates':{
'A':{'verdict':'PASS','reason':'Literal Conjecture 6.1 and hypotheses match; connectedness omission immaterial; small-graph connectivity convention not explicit and immaterial; current v1 only.'},
'B':{'verdict':'PASS','reason':'Own reconstruction; 4048 cuts; 15444 forbidden checks; 545918 subset-DP states; exact missing c0-c1 path. Robust fixed-r and infinite-r families proved ordinarily.'},
'C':{'verdict':'FAIL','reason':'Full 2023 companion construction unread after lawful author-route timeouts; no repository or arXiv copy located; later citing bodies unread; live recursive registry downloads incomplete.'},
'D':{'verdict':'QUALIFIED_PASS','reason':'Robust literal refutation survives threshold objection; classical obstruction and routine-augmentation exclusion remain unresolved. Conditional merit only; HOLD.'},
'E':{'verdict':'QUALIFIED_PASS','reason':'Conditional literal Lean route described on paper; no Lean run or theorem. Investment gated on C and root significance decision.'}},
'ordinary_mathematics':{'witness':{'r':5,'side_size':9,'offsets':[0,1,2,3,5],'convention':'independent i adjacent clique k iff (k-i) mod 9 in offsets','order':18,'edges':81,'connectivity':5},'larger_r5':[{'m':10,'offsets':[0,1,2,3,6]},{'m':11,'offsets':[0,1,2,4,7]}],'infinite_family':'Every r>=6, r+4<=m<=2r-2, any r offsets in Z_m; order 2m; intersections>=2r-m>=2. At m=2r-2 excess over bound is 2r-11.','balanced_upper_bound':'Any balanced r-connected induced-star-and-star+edge-free split graph has m<=r(r-1)/2+1; no balanced r4 witness meeting bound; no balanced r5 witness above order22.','not_claimed':['unbounded order at fixed r','no unbalanced r4 counterexample','noncyclic r6 m16 impossibility','global priority','Lean verification']},
'missing_evidence':['Full lawful 2023 Liu–Song–Zhan–Lai construction, concluding remarks/Figure 2 and operations; compare exact hypotheses and short augmentations.','Full relevant later companion-citing works, if needed for subsumption.','Complete current registry screen; present tree downloads truncated by transfer timeouts.','Root substantive novelty/significance adjudication before formalization.'],
'input_integrity':{'unchanged':True,'file_count':len(before),'before_manifest_sha256':sha(p/'outputs/inputs-before.sha256'),'after_manifest_sha256':sha(p/'outputs/inputs-after.sha256'),'comparison':'outputs/input-hash-comparison.txt','selected_inputs':{f:{'before':before[str(src/f)],'after':after[str(src/f)]} for f in files}},
'primary_sources':{'target':'https://arxiv.org/html/2603.12770v1','companion':'https://math.wvu.edu/~hlai2/Pdf/Hong-Jian_Lai_Pdf/318_DM_2023.pdf','target_text_lines':{'definitions':'35-52,71-77','theorem':'98-112','conjecture':'783-786','reference12':'818-819'},'literal_mathdb':'../expanded-corpus-r156/raw/373598.jsonl:1','result_entry':'../expanded-corpus-r156/results.json:588'},
'formal_status':{'lean_run':False,'leanchecker_run':False,'theorem':None,'estimate':'Hundreds of lines, several modules, one to three focused working days; untested.'},
'resources':{'python_isolated':True,'rss_limit_bytes':6*1024**3,'cpu_seconds':120,'wall_seconds':140,'cpus':[0,1],'malloc_arena_max':2,'wrapper':'scripts/capped.pl','lean_flags_if_invoked':'-M3500','heavy_processes_concurrent_max':1},
'artifacts':['REVIEW.md','outputs/independent.json','outputs/robustness.json','outputs/audit.json','outputs/final-audit.json','outputs/web-search-receipt.md','outputs/inputs-before.sha256','outputs/inputs-after.sha256','outputs/review-inputs.sha256','outputs/artifact-hashes.sha256'],
'limitations':'C gate unresolved. E is only desk feasibility, not a formal PASS. No claim of acceptance or worldwide novelty.'}
(p/'review.json').write_text(json.dumps(res,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'overall':res['overall'],'gates':{k:v['verdict'] for k,v in res['gates'].items()},'inputs_unchanged':True,'files_hashed':len(before),'selected_inputs':res['input_integrity']['selected_inputs']},indent=2))
