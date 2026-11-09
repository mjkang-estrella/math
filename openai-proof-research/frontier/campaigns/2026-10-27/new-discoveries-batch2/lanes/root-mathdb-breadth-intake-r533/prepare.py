import pathlib
P=pathlib.Path(__file__).resolve().parent
s=(P/'frozen/root-mathdb-breadth-intake-r523/verify.py').read_text()
s=s.replace('root-mathdb-breadth-intake-r519','root-mathdb-stack-park-intake-r531').replace('sol-mathdb-primary-qualified-breadth-r520','sol-mathdb-primary-qualified-breadth-r530')
s=s.replace("5455,'f4c909bbfb12a0e7244327c78601ed93280c05589c6992ad7c8f034d00b09b65'","5681,'8509e65d65c7b49c5bc6fd002fadaab8fd32d1d6796d52831b29ac7be26d4b46'")
s=s.replace('root-mathdb-stack-park-intake-r531/reserved-ids-r520.json','root-mathdb-ordinal-exclusion-intake-r529/reserved-ids.json').replace("'corpus_chunk'","'corpus_path'")
s=s.replace("d['statement']","d['statement_utf8']").replace("d['accepted_credit']","d['credit']")
s=s.replace('4083','4233').replace('4133','4283').replace('sol-mathdb-primary-qualified-breadth-r524','sol-mathdb-primary-qualified-breadth-r534')
start=s.index(" (P/'DECISION.md').write_text(")
end=s.index('\n files=[]',start)
decision='''# Root r533 reconciliation

Reconciled fifty disjoint reported literal reviews from r530. Cumulative literal coverage is 4,283, not complete technical or novelty coverage of MathDB. Zero proposals and no discovery credit.

Record 369592 is reported source-known: the source already supplies the target counterexample. Its construction and associated argument were inspected by the delegate; the numerical spectral inequality was not independently certified. Retain that evidence limit. Forty-nine rows remain HOLD. Eight records received selected primary passages from six sources; no whole-body or complete dependency clearance. The finite Diophantine search is diagnostic only.

Preserve the missing extraction dependency failure and source/successor/registry gaps. Carry prior adjudications unchanged, including 366370 substantive exclusion and the 365437/365439 stack-fiber family PARK pending journal/prior qualification. No mathematical checker or upstream verifier was executed by root.

Claude r504 remains rate-limited and unreviewed. Sol r532 continues; reserve fifty fresh disjoint IDs for Sol r534. Counts remain 9 additional / 39 total / next 40.
'''
s=s[:start]+" (P/'DECISION.md').write_text("+repr(decision)+")"+s[end:]
(P/'verify.py').write_text(s)
