import pathlib,json,hashlib,datetime
r=pathlib.Path(__file__).resolve().parents[1]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
a=r/'inputs.before.sha256';b=r/'inputs.after.sha256'
assert a.read_bytes()==b.read_bytes()
checks=json.loads((r/'logs/check-final.json').read_text())
receipts=[]
for p in sorted((r/'http').glob('*/receipt.json')):
 j=json.loads(p.read_text());body=p.parent/'body'
 if j.get('sha256'): assert sha(body)==j['sha256']
 receipts.append({'receipt':str(p.relative_to(r)),'url':j['url'],'status':j.get('status'),'error':j.get('error'),'body_sha256':sha(body) if body.exists() else None})
out={
 'schema_version':1,'review_lane':'slownim-review-r1','review_type':'independent adversarial pre-Lean review','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'mathdb_ids':[360653,361128],'overall_recommendation':'HOLD','acceptance_decision':False,'credit_claimed':0,'maximum_recommended_credit':1,'preferred_record':360653,'duplicate_record':361128,
 'gates':{
 'A':{'verdict':'QUALIFIED_PASS','finding':'Exact arXiv conjecture and rules verified in both sole versions; fresh sources match cached TeX. DAM version unread.'},
 'B':{'verdict':'PASS','finding':'Independent legal-move/payoff search, both certificates, adversarial completion tree, and all-parameter block proof verified.'},
 'C':{'verdict':'QUALIFIED_PASS','finding':'Live author lists, bounded searches, pinned Lean Pool and gn-lean screened. OpenAlex citing-work screen blocked by 429; no retry.'},
 'D':{'verdict':'QUALIFIED_PASS','finding':'Genuine literal refutation, recommend eligible subject to novelty and root exclusion adjudication; not self-accepted.'},
 'E':{'verdict':'QUALIFIED_PASS','finding':'Finite literal Lean route feasible with legality, termination and Nash bridges. Draft incomplete and uncompiled; no Lean invoked.'}},
 'hold_requirements':[
 'Obtain adequate citing-work/erratum screen for both targets through authorized available evidence, without retrying denied hosts.',
 'Determine DAM version-of-record conjecture status, or record root adjudication that 360653 may proceed despite this publication-status gap.'
 ],
 'packaging_corrections':[
 'Remove unqualified smallest-counterexample claim: (2,4,4) gives payoff improvement with smaller entry sum.',
 'Correct nim_certificate.py docstring: opponent multiple-free positions do occur in the convention-free deviation tree.',
 'Exclude n=1 from the finite-game formulation; include n>=2 and l>=2.',
 'Do not require arbitrary tie-breaks for fidelity: source fixes rightmost. Relational strengthening needs an invariance bridge.',
 'Complete legal strategies, total-play/fuel independence, admissibility, payoff, Nash definition, Conjecture Prop and explicit negation bridge; positivity of l is missing in draft.'
 ],
 'independent_computation':{'script':'scripts/check.py','log':'logs/check-final.json','family_pairs':checks['family_checks'],'searches':checks['search'],'robust_C':9,'robust_payoff':checks['robust']['payoff'],'robust_terminal_pairs':checks['robust']['all_terminal_length_loser_pairs']},
 'input_integrity':{'before_manifest':a.name,'after_manifest':b.name,'before_sha256':sha(a),'after_sha256':sha(b),'unchanged':True,'verification_log':'logs/input-verification.log','candidate_sha256':'108c9239e48594895cdc0b943abf4334cf9e1006a63de5702a174ffad8cb15bd'},
 'registry_heads':{'lean_pool':'01db1d7049cf9668bda1e9e106875ee1278b43e6','gn_lean':'73bb87b16da8c053fd07e0d4dc43732b74335a3b'},
 'network':{'receipt_count':len(receipts),'receipts':receipts,'github_repository_queries':2,'denial_observed':'api.openalex.org HTTP 429; subsequent queued request locally blocked','forbidden_services_not_contacted':['Crossref','Semantic Scholar','arXiv search API','ScienceDirect'],'tls_verification_disabled':False},
 'resources':{'python_isolated':True,'cpu_affinity':[0,1],'cpu_seconds':120,'wall_seconds':140,'rss_kib':6291456,'MALLOC_ARENA_MAX':2,'heavy_processes_concurrent_max':1,'lean_invocations':0,'children_spawned':0},
 'report':'REVIEW.md','replay_driver':'replay.sh'
}
(r/'review.json').write_text(json.dumps(out,indent=2)+'\n')
print('review.json written; input manifests identical; HTTP body hashes verified; gates A-E present')
