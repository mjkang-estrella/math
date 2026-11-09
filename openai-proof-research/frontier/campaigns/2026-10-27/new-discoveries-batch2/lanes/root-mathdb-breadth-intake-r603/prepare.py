import pathlib
P=pathlib.Path(__file__).resolve().parent
s=(P/'frozen/root-mathdb-breadth-intake-r601/verify.py').read_text()
s=s.replace('root-mathdb-breadth-intake-r599','root-mathdb-breadth-intake-r601').replace('root-mathdb-banzhaf-retirement-intake-r503/reserved-ids-r504.json','root-mathdb-breadth-intake-r597/reserved-ids.json')
s=s.replace('claude-mathdb-primary-qualified-breadth-r504','sol-mathdb-primary-qualified-breadth-r598').replace('claude-mathdb-primary-qualified-breadth-r602','sol-mathdb-primary-qualified-breadth-r604')
s=s.replace("8592,'9c4e9834a36905625e27d63c1c9ef6e739beb5765d5746a6d75841772bf21a16'","4116,'a1d70513442c13c243bb6589e7a466c078c4b3a5c188be765f35e05671681b0e'")
s=s.replace("'corpus_chunk','corpus_line','statement_utf8_sha256'","'chunk','line','statement_sha256'")
s=s.replace("check(pathlib.Path(e['original']),e)","check(pathlib.Path(e['path']),e)").replace("d[ck]==str(p.relative_to(C))","d[ck]==str(p)")
s=s.replace(" cov['383181']['reported_statement_incomplete']=True\n cov['383181']['source_restoration_required']=True\n",'')
s=s.replace('5983','6033').replace('5933','5983')
start=s.index(" (P/'DECISION.md').write_text(");end=s.index('\n files=[]',start)
decision='''# Root r603 reconciliation

Reconciled r598: fifty disjoint literal record reviews, zero proposals or credit. Cumulative coverage is 6,033 record reviews, not complete-statement or whole-corpus technical coverage. Preserve 24 restoration/wording flags, 26 apparent-self-containment assessments, earlier 383181 incomplete flag and all prior judgments.

324902 is source-refuted by exactly the replication counterexample family in arXiv1301.6983v1; selected definitions/Lemma 6 read, not whole dependency chain. 321700 ideal-element/generator and equigeneration scope unresolved. 325693 marginal product identities do not yet force block multiplicities; no independence proof/counterexample. No closest-successor/whole-body/current-registry clearance.

Preserve early unassigned-record structural display (not assessed/counted), truncated-output rereads and wrong failures filename corrected after binding. Three primary HTML fetches succeeded, parked routes untouched. Root performs administrative integrity/corpus reconciliation only, no upstream/math checkers.

Sol r600 continues. Fresh disjoint assignments: Claude r602 from root r601, Sol r604 from this intake. Claude's resumed r504 batch is reconciled, no longer reserved or rate-limited. Current abstract-based retirements remain evidence-limited. Generic request headers only, no personal identifiers. No user input pending. Adjudications/access stops unchanged; counts remain 9 additional / 39 total / next 40.
'''
s=s[:start]+" (P/'DECISION.md').write_text("+repr(decision)+")"+s[end:]
(P/'verify.py').write_text(s)
print('prepared')
