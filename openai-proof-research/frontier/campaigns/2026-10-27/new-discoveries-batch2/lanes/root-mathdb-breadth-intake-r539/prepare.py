import pathlib
P=pathlib.Path(__file__).resolve().parent
s=(P/'frozen/root-mathdb-breadth-intake-r537/verify.py').read_text()
s=s.replace('root-mathdb-breadth-intake-r535','root-mathdb-breadth-intake-r537').replace('root-mathdb-breadth-intake-r533/reserved-ids.json','root-mathdb-breadth-intake-r535/reserved-ids.json')
s=s.replace('sol-mathdb-primary-qualified-breadth-r534','sol-mathdb-primary-qualified-breadth-r536').replace('sol-mathdb-primary-qualified-breadth-r538','sol-mathdb-primary-qualified-breadth-r540')
s=s.replace("6137,'68b159a465ef247e70ba4e72fe59b77e0b50350503a629326454d8afb43e521d'","5791,'a3ba8c61f5d4bce5717caea0bcc949b745cb010b31b955b6bb901e87bb63e7cd'")
s=s.replace("'corpus_chunk','line','statement_sha256'","'corpus_chunk','corpus_line_1based','statement_utf8_sha256'").replace("d['accepted_credit']","d['credit']")
s=s.replace('4383','4433').replace('4333','4383')
start=s.index(" (P/'DECISION.md').write_text(");end=s.index('\n files=[]',start)
decision='''# Root r539 reconciliation

Reconciled r536: fifty disjoint reported literal reviews, zero proposals or credit. Cumulative literal coverage is 4,433; no claim of complete technical or novelty coverage. Eleven records received selected passage review or text search across seven retained primary bodies. No complete-body, dependency or successor clearance.

374553 and 375220 are withheld from discovery investment on explicit public theorem statements, without upgrading unaudited dependencies to proof clearance. The 375555 kernel route is reported as a routine source adaptation. The 375989 finite word-factor deficit is expressly not a refutation; source/version and all-length gaps survive. The 376201 finite simplex comparisons do not settle arbitrary anticodes. Other routes retain their individual HOLDs and objections.

Root performed only administrative/file/corpus reconciliation, no mathematical checker or upstream verifier execution. Preserve display truncations and stopped routes. No access failures reported. Registry and novelty remain HOLD. Carry all existing adjudications unchanged.

Sol r538 continues. Reserve fifty fresh disjoint records for Sol r540. Claude r504 remains rate-limited, its fifty IDs reserved and unreviewed. Counts remain 9 additional / 39 total / next 40.
'''
s=s[:start]+" (P/'DECISION.md').write_text("+repr(decision)+")"+s[end:]
(P/'verify.py').write_text(s)
