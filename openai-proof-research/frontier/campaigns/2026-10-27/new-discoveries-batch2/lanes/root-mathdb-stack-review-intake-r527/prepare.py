import pathlib
P=pathlib.Path(__file__).resolve().parent
s=(P/'frozen/root-mathdb-candidate-intake-r525/verify.py').read_text()
s=s.replace("I=F/'root-mathdb-breadth-intake-r523'","I=F/'root-mathdb-candidate-intake-r525'")
a=s.index('SPEC=');b=s.index('\ndef j(',a)
s=s[:a]+"SPEC=[('sol-mathdb-primary-qualified-breadth-r524',4814,'3584ab2e1b672cd2764aa74eff1f3732efffe280dddf03e00670f5e08d4b0fde','root-mathdb-breadth-intake-r523/reserved-ids.json','corpus_chunk','corpus_line','statement_sha256')]"+s[b:]
s=s.replace("exact(L/'root-mathdb-breadth-intake-r523',j(I/'manifest.json'))","exact(L/'root-mathdb-candidate-intake-r525',j(I/'manifest.json'))")
s=s.replace('len(cov)==4183','len(cov)==4233').replace('len(cov)==4133','len(cov)==4183')
s=s.replace("proposals=j(F/name/'proposals.json');assert len(proposals)==2 and {p['mathdb_id'] for p in proposals}=={365437,366370}","assert j(F/name/'proposals.json')==[]")
s=s.replace("d['statement']","d['literal_statement']").replace("d['accepted_credit']","d['credit']")
a=s.index(" active=[r for r in j(I/'active-breadth-reservations.json')");b=s.index(" (P/'DECISION.md').write_text(",a)
s=s[:a]+''' active=[r for r in j(I/'active-breadth-reservations.json') if r['lane']!='sol-mathdb-primary-qualified-breadth-r524']
 assert len(active)==1 and active[0]['lane']=='claude-mathdb-primary-qualified-breadth-r504'
 active[0]['other_active_reservations']=[];active[0]['active_hypothesis_ids']=[366370,365437,365439]
 write('active-breadth-reservations.json',active)
 (P/'routing-queue.jsonl').write_bytes((I/'routing-queue.jsonl').read_bytes())
 hypotheses=j(I/'hypothesis-queue.json')
 for q in hypotheses:
  if q['mathdb_id']==365437:q['status']='assigned_source_first_independent_review';q['lane']='sol-mathdb-stack-fiber-preliminary-review-r528'
 write('hypothesis-queue.json',hypotheses);write('candidate-briefs.json',j(I/'candidate-briefs.json'))
'''+s[b:]
a=s.index(" (P/'DECISION.md').write_text(");b=s.index(' files=[]',a)
s=s[:a]+" (P/'DECISION.md').write_text("+repr('''# Root r527 reconciliation and stack review assignment

Reconcile r524:fifty disjoint literal reviews,zero proposals. Latest coverage4,233; child used assigned older4,133 baseline.368923 is reported source-theorem refutation from selected proof,not a complete dependency audit. Five target records selected across four arXivv1HTML bodies; no whole-body,successor,registry clearance. Finite information-state diagnostic at excluded threshold is not a counterexample. Preserve parser failure and pre-verification metadata/unassigned-row display deviation. Counts9additional/39total/next40 unchanged.

Assign separate Sol r528 source-first independent review of365437/365439 as one stack-fiber family. Producer r522 reports n5second-largest5 rather than4 and n8tie64 defeating uniqueness. Exact stack reading/vincular adjacency, whole-source internal claims and actual published journal wording are critical. Journal DOI10.1016/j.disc.2025.114834 metadata alone does not authenticate conjecture survival. No Lean/manuscript or new-credit claim. Producer source/checkers retained as data; root does not run mathematical code.

Sol r526 ordinal-ball review continues separately. Claude r504 remains rate-limited/reserved unreviewed. Both Sol slots now carry bounded candidate reviews; return the next freed useful slot to breadth unless an eligible small result justifies a distinct follow-up. Protected candidates and existing adjudications unchanged. Routing6000rows remains metadata only; integrity never proves mathematical/novelty acceptance.
''')+")\n"+s[b:]
s=s.replace('assert len(seen)==100','assert len(seen)==50')
s=s.replace("'coverage':4183,'new_literal_reviews':50","'coverage':4233,'new_literal_reviews':50")
(P/'verify.py').write_text(s);print('prepared')
