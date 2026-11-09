import pathlib
P=pathlib.Path(__file__).resolve().parent
s=(P/'frozen/root-mathdb-breadth-intake-r535/verify.py').read_text()
s=s.replace('root-mathdb-breadth-intake-r533','root-mathdb-breadth-intake-r535').replace('root-mathdb-stack-park-intake-r531/reserved-ids.json','root-mathdb-breadth-intake-r533/reserved-ids.json')
s=s.replace('sol-mathdb-primary-qualified-breadth-r532','sol-mathdb-primary-qualified-breadth-r534').replace('sol-mathdb-primary-qualified-breadth-r536','sol-mathdb-primary-qualified-breadth-r538')
s=s.replace("6926,'e3151c814c12cb1f7a227f4248f2146d16c7d41580a03d70eeff88b842f7caef'","6137,'68b159a465ef247e70ba4e72fe59b77e0b50350503a629326454d8afb43e521d'")
s=s.replace("'corpus_chunk','corpus_line_1based','statement_utf8_sha256'","'corpus_chunk','line','statement_sha256'").replace("d['credit']","d['accepted_credit']")
s=s.replace('4333','4383').replace('4283','4333')
start=s.index(" (P/'DECISION.md').write_text(");end=s.index('\n files=[]',start)
decision='''# Root r537 reconciliation

Reconciled r534: fifty disjoint reported literal reviews, zero proposals. Cumulative literal coverage is 4,383, not complete technical or novelty coverage of MathDB. All fifty dispositions remain HOLD_NO_FULL_SCOPE_ROUTE.

Four selected primary passages and one cited predecessor proof were inspected by the delegate; no complete source-body, dependency, successor or registry clearance. Local proved parameter cases and source/domain corrections earn no credit. The finite atom screening through cutoff 12 supplies no universal proof. Root did not execute mathematical checks or any upstream verifier.

Preserve stopped routes, corrections and process deviations in the frozen child packet. Current registry and scientific acceptance remain HOLD. Existing adjudications, including ordinal exclusion and stack-fiber PARK, remain unchanged.

Sol r536 continues. Reserve fifty fresh disjoint records for Sol r538. Claude r504 remains rate-limited; its fifty IDs remain unreviewed and reserved. Counts remain 9 additional / 39 total / next 40.
'''
s=s[:start]+" (P/'DECISION.md').write_text("+repr(decision)+")"+s[end:]
(P/'verify.py').write_text(s)
