import pathlib
P=pathlib.Path(__file__).resolve().parent
s=(P/'frozen/root-mathdb-breadth-intake-r591/verify.py').read_text()
s=s.replace('root-mathdb-breadth-intake-r589','root-mathdb-breadth-intake-r591').replace('root-mathdb-breadth-intake-r587/reserved-ids.json','root-mathdb-breadth-intake-r589/reserved-ids.json')
s=s.replace('sol-mathdb-primary-qualified-breadth-r588','sol-mathdb-primary-qualified-breadth-r590').replace('sol-mathdb-primary-qualified-breadth-r592','sol-mathdb-primary-qualified-breadth-r594')
s=s.replace("6547,'d7d18cd63916b1d5d1636aa41514ae9569e2df8f818a56faab477dbc8cfd2f8f'","7268,'486763e97eeb74cf7b1a336630cc211f784cfe1def3c1da6a05ab056ff87e77d'")
s=s.replace("d['literal_statement']==r['statement']","d['statement']==r['statement']")
s=s.replace('5733','5783').replace('5683','5733')
start=s.index(" (P/'DECISION.md').write_text(");end=s.index('\n files=[]',start)
decision='''# Root r593 reconciliation

Reconciled r590: fifty disjoint literal record reviews, zero proposals or credit. Cumulative coverage is 5,783 record reviews, not complete-statement or whole-corpus technical coverage. Preserve every scope/restoration flag and selected-source limit.

Seven primary passages (six talks/five reports) inspected. No whole-report, successor-proof-body, full dependency or current-registry audit. Reports already announce polynomial planar morph, compatible-family lattice count, solved two-variable autoregression and Poisson-equivalence counterexamples. Map recurrence differs from requested bijection. AAK thresholds/algorithm are source results; 400382/400383 finite error-floor calculation is a wording/domain objection only. No discovery investment or scientific acceptance.

Ten lawful EMS fetches and one search batch; blocked routes remained parked. Root performs administrative integrity/corpus reconciliation only, never upstream or mathematical checkers. Adjudications unchanged.

Sol r592 continues. Fifty fresh disjoint records reserved for Sol r594. Claude r504 remains rate-limited with fifty reserved unreviewed IDs. No user input pending. Counts remain 9 additional / 39 total / next 40.
'''
s=s[:start]+" (P/'DECISION.md').write_text("+repr(decision)+")"+s[end:]
(P/'verify.py').write_text(s)
print('prepared')
