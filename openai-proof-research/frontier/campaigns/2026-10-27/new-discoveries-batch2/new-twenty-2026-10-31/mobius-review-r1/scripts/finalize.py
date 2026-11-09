from pathlib import Path
import json,hashlib
D=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
r={
 'mathdb_id':339235,'lane':'mobius-review-r1','date_utc':'2026-11-05','overall_recommendation':'HOLD','accepted':False,
 'gates':{
 'A':{'verdict':'QUALIFIED_PASS','reason':'Exact arXiv/MathDB match; only v1 exists; journal index preserves conjecture as 3.14, but independent full journal retrieval failed TLS.','evidence':['downloads/arxiv-v1/text.txt:27-51,453-491','downloads/arxiv-abs/body:180-183','../expanded-corpus-r246/raw/339235.jsonl:1','downloads/journal/receipt.json','downloads/journal-alt/receipt.json']},
 'B':{'verdict':'PASS','reason':'Own exact M12/M8 verification and odd-cycle lower bound; bounded n=8,10 searches unsuccessful, not exhaustive.','evidence':['scripts/verify.py','logs/math-verification.json','scripts/search.py','logs/search.log']},
 'C':{'verdict':'FAIL','reason':'No positive prior duplicate located, but authentic slide body and remaining plausible citing/later-author bodies not cleared.','evidence':['logs/citation-screen.log','logs/registry-screen.log','downloads/slides/visible.txt:1-45','downloads/survey/text.txt:11200-11330','logs/literature-web-final.json'],'prior_refutation_identified':False},
 'D':{'verdict':'QUALIFIED_PASS','reason':'M12 is outside 2022 order-eight arithmetic correction and distinct from full-tree family 354228; no printed witness identified, missing slide comparison prevents full clearance.','evidence':['REVIEW.md','downloads/arxiv-v1/text.txt:453-491','../expanded-corpus-r246/sources/regular-2022.txt:339-368']},
 'E':{'verdict':'PASS','reason':'Independent fresh final-packet strict build, explicit leanchecker Mobius, 19-declaration axiom audit; full universal negation in general ladder-family minimum-equality encoding.','evidence':['scripts/extract.py','scripts/replay.sh','logs/extract.log','logs/build.log','logs/checker.log','logs/audit.log','replay/fresh/Mobius.lean:6-50'],'missing_bridge':None,'limitations':'No arbitrary SimpleGraph API, global all-n simplicity theorem, or formal exact lower bound three; none needed for family-based negation at certified n=6.'}},
 'required_for_clearance':['Authentic full 2020 workshop slide body, including ladder claims and figures, from an allowed public/authorized source.','Verified full journal edition and correction/withdrawal history; compare conjecture 3.14 and graph definition.','Documented content/scope and chronology checks of remaining plausible citing constructions and later Lau-Shiu papers; root adjudication of substantive-credit exclusions.'],
 'packet':{'selected':'proof-packet-full.zip','sha256':'ffa01d95d108d91cc5f90638a1ef46fd9f76ac2cc743487a2c0b9644e2f7a2ea','older_packet_sha256':'2713eb3f36167f8fecbfee72cf59e102b565caedf5388a7100888821d0e5797c'},
 'replay':{'lean':'4.34.1','build_exit_code':0,'leanchecker_exit_code':0,'audit_exit_code':0,'explicit_checker_module':'Mobius','audited_declarations':19,'axioms':['propext','Classical.choice','Quot.sound'],'mathlib_required':False,'trust':'Installed Lean kernel/checker and prebuilt Init dependencies; no upstream source rebuild.'},
 'registry':{'lean_pool_head':'01db1d7049cf9668bda1e9e106875ee1278b43e6','tree_truncated':False,'actual_config':'LeanPool/projects.yml','repository_queries':4,'repository_query_counts':[0,0,0,0],'openalex_work':'W2802677295','openalex_cited_by_count':32,'citing_filter_records':31,'sequencing':'After discovery; does not cure disclosed discovery-lane sequencing failure.'},
 'integrity':{'bound_input_files':240,'before_manifest':'inputs-before.sha256','after_manifest':'inputs-after.sha256','before_manifest_sha256':sha(D/'inputs-before.sha256'),'after_manifest_sha256':sha(D/'inputs-after.sha256'),'unchanged':(D/'inputs-before.sha256').read_bytes()==(D/'inputs-after.sha256').read_bytes()},
 'resources':{'driver':'scripts/cap.sh','cpus':[0,1],'rss_limit_mib':6144,'cpu_limit_seconds':120,'wall_limit_seconds':140,'lean_memory_option':'-M3500','MALLOC_ARENA_MAX':2,'lane_local_temp_and_cache':True},
 'report':'REVIEW.md'
}
assert r['integrity']['unchanged'];(D/'review.json').write_text(json.dumps(r,indent=2)+'\n')
print('review.json written; all 240 input hashes unchanged')
