import pathlib,json
P=pathlib.Path(__file__).resolve().parent
s=(P/'frozen/root-mathdb-breadth-intake-r579/verify.py').read_text()
s=s.replace('root-mathdb-breadth-intake-r577','root-mathdb-breadth-intake-r579').replace('root-mathdb-breadth-intake-r575/reserved-ids.json','root-mathdb-breadth-intake-r579/reserved-ids.json')
s=s.replace('sol-mathdb-primary-qualified-breadth-r580','sol-mathdb-primary-qualified-breadth-r582').replace('sol-mathdb-primary-qualified-breadth-r576','sol-mathdb-primary-qualified-breadth-r580')
s=s.replace("5653,'818170acc33e4ad45e72340e97665a13a8dbb842082f37618b3e42572c8603ac'","3979,'f295558703311a4e12f460db698592d3153ea0dc11966207fe6ce8a872994d73'")
s=s.replace("'chunk','line','statement_sha256'","'chunk','line','statement_utf8_sha256'")
s=s.replace('5433','5483').replace('5383','5433')
start=s.index(" (P/'DECISION.md').write_text(");end=s.index('\n files=[]',start)
decision='''# Root r581 reconciliation

Reconciled r580: fifty disjoint reported literal record reviews, zero proposals or credit. Cumulative coverage is 5,483 record reviews, not complete-statement or whole-corpus technical coverage. Preserve per-row scope flags and all prior incomplete/restoration judgments.

Ten rows explicitly need primary quantifier/domain/definition restoration. Selected source/proof sections for 391133 establish only limsup g=M² and liminf g>=L²; convergence has two unproved dependencies. External cited Ramsey bodies and optimization were not independently audited. 391007 finite digit matching changes with the integer-bit-first convention; failed fractional convention is retained, no universal recurrence inferred. Remaining primary/successor bodies unreviewed. Registry and scientific acceptance HOLD.

Preserve prebinding title/header display and failed digit-index interpretation; truncated record display replaced after binding. Root performs administrative integrity/corpus reconciliation only, no mathematics or upstream checker execution. Adjudications and access stops unchanged.

Sol r578 continues. Fifty fresh disjoint records reserved for Sol r582. Claude r504 remains rate-limited with fifty reserved unreviewed IDs. No user input pending. Counts remain 9 additional / 39 total / next 40.
'''
s=s[:start]+" (P/'DECISION.md').write_text("+repr(decision)+")"+s[end:]
(P/'verify.py').write_text(s)
print('prepared')
