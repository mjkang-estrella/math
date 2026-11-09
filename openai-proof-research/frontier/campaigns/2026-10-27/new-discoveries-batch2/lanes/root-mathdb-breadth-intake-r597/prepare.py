import pathlib
P=pathlib.Path(__file__).resolve().parent
s=(P/'frozen/root-mathdb-breadth-intake-r595/verify.py').read_text()
s=s.replace('root-mathdb-breadth-intake-r593','root-mathdb-breadth-intake-r595').replace('root-mathdb-breadth-intake-r591/reserved-ids.json','root-mathdb-breadth-intake-r593/reserved-ids.json')
s=s.replace('sol-mathdb-primary-qualified-breadth-r592','sol-mathdb-primary-qualified-breadth-r594').replace('sol-mathdb-primary-qualified-breadth-r596','sol-mathdb-primary-qualified-breadth-r598')
s=s.replace("4027,'0cfbb20618cca7a80132f2ac1e909d3c9f9e0c7111a4a15d1505115fde95e0de'","3952,'e19789ee362f3267eac85ff59313959bc0ab499370882a6bdd61915b27065c8d'")
s=s.replace("d['literal_statement']==r['statement']","d['statement']==r['statement']")
s=s.replace('5833','5883').replace('5783','5833')
start=s.index(" (P/'DECISION.md').write_text(");end=s.index('\n files=[]',start)
decision='''# Root r597 reconciliation

Reconciled r594: fifty disjoint literal record reviews, zero proposals or credit. Cumulative coverage is 5,883 record reviews, not complete-statement or whole-corpus technical coverage. Preserve 12 self-contained literal assessments/38 scope-dependent judgments and all prior flags.

Six selected primary passages read. Walk cardinality equality is source-known while a natural bijection remains missing. Arrangement characteristic polynomials, QSP recursive synthesis/algorithms and nonlinear full-line inverse are already source results. Conjugate-sign defect is wording only; fare-zone packing observation routine; light tournaments still need a global mechanism. No successor-proof-body, full dependency or current-registry clearance.

Retain bound source/provenance and parked routes, no new credit. Root performs administrative integrity/corpus reconciliation only, never upstream or mathematical checkers. Adjudications unchanged.

Sol r596 continues. Fifty fresh disjoint records reserved for Sol r598. Claude r504 remains rate-limited with fifty reserved unreviewed IDs. No user input pending. Counts remain 9 additional / 39 total / next 40.
'''
s=s[:start]+" (P/'DECISION.md').write_text("+repr(decision)+")"+s[end:]
(P/'verify.py').write_text(s)
print('prepared')
