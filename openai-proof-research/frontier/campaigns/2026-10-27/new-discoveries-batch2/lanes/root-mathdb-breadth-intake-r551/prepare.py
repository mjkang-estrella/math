import pathlib
P=pathlib.Path(__file__).resolve().parent
s=(P/'frozen/root-mathdb-breadth-intake-r549/verify.py').read_text()
s=s.replace('root-mathdb-breadth-intake-r547','root-mathdb-breadth-intake-r549').replace('root-mathdb-breadth-intake-r545/reserved-ids.json','root-mathdb-breadth-intake-r547/reserved-ids.json')
s=s.replace('sol-mathdb-primary-qualified-breadth-r546','sol-mathdb-primary-qualified-breadth-r548').replace('sol-mathdb-primary-qualified-breadth-r550','sol-mathdb-primary-qualified-breadth-r552')
s=s.replace("7094,'09005f5ec127fe96cd8618d4dc180b350152f2f0d84058f81b0fbd9b351b5a90'","5160,'f952cb8679fbdc2236252820f000c43215e0299a2ad70dc7cd69ffe5cf376612'")
s=s.replace("'corpus_chunk','corpus_line','statement_sha256'","'chunk','line','statement_sha256'").replace("d['statement_utf8']","d['statement']").replace("d['credit']","d['accepted_credit']")
s=s.replace('4683','4733').replace('4633','4683')
start=s.index(" (P/'DECISION.md').write_text(");end=s.index('\n files=[]',start)
decision='''# Root r551 reconciliation

Reconciled r548: fifty disjoint reported literal reviews, 26 PARK, 21 HOLD and three existing-proof/theorem objections. Zero proposals or credit. Cumulative literal coverage is 4,733; no complete technical or novelty corpus claim.

Primary passages for 387816, 387874, 388000 and selected successor material were inspected. Hayman reports 6.79 proved and 7.22 solved; Ortel's short argument appears in the inspected successor introduction. Gaussian comparison applies under centeredness, with p=infinity and Psi(x)=x as reported. Gaussian proof sections and Krushkal's proof remain unread. Preserve all source, dependency and noncentered-wording limits; no root mathematical audit or checker execution.

The prebinding administrative-script-reading deviation and truncated context output remain disclosed. No new access failures. Registry and full dependency gates remain HOLD. Root checks only files, corpus hashes and assignments, without upstream verifier execution. Existing adjudications and parked routes remain unchanged.

Sol r550 continues. Reserve fifty fresh disjoint records for Sol r552. Claude r504 remains rate-limited; its fifty IDs are reserved and unreviewed. Counts remain 9 additional / 39 total / next 40.
'''
s=s[:start]+" (P/'DECISION.md').write_text("+repr(decision)+")"+s[end:]
(P/'verify.py').write_text(s)
