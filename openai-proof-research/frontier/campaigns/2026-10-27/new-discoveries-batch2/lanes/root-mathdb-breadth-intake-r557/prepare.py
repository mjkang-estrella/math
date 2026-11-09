import pathlib
P=pathlib.Path(__file__).resolve().parent
s=(P/'frozen/root-mathdb-breadth-intake-r555/verify.py').read_text()
s=s.replace('root-mathdb-breadth-intake-r553','root-mathdb-breadth-intake-r555').replace('root-mathdb-breadth-intake-r551/reserved-ids.json','root-mathdb-breadth-intake-r553/reserved-ids.json')
s=s.replace('sol-mathdb-primary-qualified-breadth-r552','sol-mathdb-primary-qualified-breadth-r554').replace('sol-mathdb-primary-qualified-breadth-r556','sol-mathdb-primary-qualified-breadth-r558')
s=s.replace("5305,'f068999c804ece01d226ff078c395afef0e8aae26fbc6bdc7e27805b50d9fa06'","6099,'83316b778460487bbc4429b0b887e5e8b900b0de7cb4c3020a8ca732dcd884f0'")
s=s.replace("'chunk','line','statement_sha256'","'corpus_chunk','corpus_line','statement_utf8_sha256'")
s=s.replace('4833','4883').replace('4783','4833')
start=s.index(" (P/'DECISION.md').write_text(");end=s.index('\n files=[]',start)
decision='''# Root r557 reconciliation

Reconciled r554: fifty disjoint reported literal reviews, zero proposals or credit. Latest cumulative literal coverage is 4,883; no full technical corpus or novelty claim. Five selected primary records plus the Postnikov successor theorem/local proof were inspected; no whole-body or complete dependency audit.

k602 is reported to reduce to classical focal-tangent algebra, with a rational diagnostic and no discovery nomination. Postnikov 394356 has an exact public theorem. APN retains an unproved parameter gap. Other source-theorem reports retain conservative evidence levels; source, dependency, successor and current-registry gaps remain HOLD.

Preserve extraction and negative-fixture failures and deviations in the frozen packet. Root performs only administrative/file/corpus reconciliation, no mathematical checker or upstream verifier execution. Existing adjudications and parked routes remain unchanged.

Sol r556 continues. Reserve fifty fresh disjoint records for Sol r558. Claude r504 remains rate-limited with fifty IDs reserved/unreviewed. Counts remain 9 additional / 39 total / next 40.
'''
s=s[:start]+" (P/'DECISION.md').write_text("+repr(decision)+")"+s[end:]
(P/'verify.py').write_text(s)
