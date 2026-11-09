import pathlib
P=pathlib.Path(__file__).resolve().parent
s=(P/'frozen/root-mathdb-breadth-intake-r539/verify.py').read_text()
s=s.replace('root-mathdb-breadth-intake-r537','root-mathdb-breadth-intake-r539').replace('root-mathdb-breadth-intake-r535/reserved-ids.json','root-mathdb-breadth-intake-r537/reserved-ids.json')
s=s.replace('sol-mathdb-primary-qualified-breadth-r536','sol-mathdb-primary-qualified-breadth-r538').replace('sol-mathdb-primary-qualified-breadth-r540','sol-mathdb-primary-qualified-breadth-r542')
s=s.replace("5791,'a3ba8c61f5d4bce5717caea0bcc949b745cb010b31b955b6bb901e87bb63e7cd'","6093,'6b01fd4b7be188dd453caa6c80441dd497493e8329bc45339aa05d6bd1b4c119'")
s=s.replace("'corpus_chunk','corpus_line_1based','statement_utf8_sha256'","'corpus_chunk','line','statement_sha256'").replace("d['credit']","d['accepted_credit']")
s=s.replace('4433','4483').replace('4383','4433')
start=s.index(" (P/'DECISION.md').write_text(");end=s.index('\n files=[]',start)
decision='''# Root r541 reconciliation

Reconciled r538: fifty disjoint reported literal reviews, forty-five HOLDs, five public-source exclusions, zero proposals. Cumulative literal coverage is 4,483, not full technical or novelty coverage. Six selected records inspected in eight primary/successor HTML bodies; no whole-body, dependency or registry clearance.

Reported source exclusions: 376377 Hoffman-Singleton counterexample; 376634 Fekete aperture theorem; 377820 strongly MDS code existence; 378061 Hom-complex connectivity subsumption; 378394 Chung discrepancy refutation. Preserve each row's evidence limits. In particular 378061 retains an exact-primary-version gap and a finite-simple-graph scope bridge; full dependency audits remain absent. Root does not upgrade these to independently audited mathematical conclusions. The public graph certificate is uncredited and was not executed by root.

Preserve the failed bs4 extraction and subsequent missing-file search. Current registry and novelty remain HOLD. Carry existing adjudications unchanged. Root performs only file, corpus and assignment reconciliation, no upstream verifier or mathematical execution.

Sol r540 continues. Reserve fifty fresh disjoint records for Sol r542. Claude r504 remains rate-limited with its fifty IDs reserved/unreviewed. Counts remain 9 additional / 39 total / next 40.
'''
s=s[:start]+" (P/'DECISION.md').write_text("+repr(decision)+")"+s[end:]
(P/'verify.py').write_text(s)
