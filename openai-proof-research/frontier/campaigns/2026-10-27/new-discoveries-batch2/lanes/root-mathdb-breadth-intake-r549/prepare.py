import pathlib
P=pathlib.Path(__file__).resolve().parent
s=(P/'frozen/root-mathdb-breadth-intake-r547/verify.py').read_text()
s=s.replace('root-mathdb-breadth-intake-r545','root-mathdb-breadth-intake-r547').replace('root-mathdb-breadth-intake-r543/reserved-ids.json','root-mathdb-breadth-intake-r545/reserved-ids.json')
s=s.replace('sol-mathdb-primary-qualified-breadth-r544','sol-mathdb-primary-qualified-breadth-r546').replace('sol-mathdb-primary-qualified-breadth-r548','sol-mathdb-primary-qualified-breadth-r550')
s=s.replace("3815,'5ecb612ffc61085fd15fe771eadb28c3095b0bcb3ca43795194d5654534804e6'","7094,'09005f5ec127fe96cd8618d4dc180b350152f2f0d84058f81b0fbd9b351b5a90'")
s=s.replace("'chunk','line','statement_sha256'","'corpus_chunk','corpus_line','statement_sha256'").replace("d['statement']","d['statement_utf8']").replace("d['accepted_credit']","d['credit']")
s=s.replace('4633','4683').replace('4583','4633')
start=s.index(" (P/'DECISION.md').write_text(");end=s.index('\n files=[]',start)
decision='''# Root r549 reconciliation

Reconciled r546: fifty disjoint reported literal reviews, zero proposals or credit. Cumulative literal coverage is 4,683, not full technical or novelty coverage of MathDB. Seven primary snapshots, selected passages and two local proof readings; no full-body/dependency or registry clearance.

Reported source results stop investment for represented-matroid perturbation 338008 and Morita-algebra derived equivalence 381390. Matrix-A2 384503 retains original AIM context HOLD despite a successor defeating the usual linear interpretation. Groupoid329126 has an existential/universal separation mismatch; no wording credit. Root preserves these scope and dependency limits and runs no mathematical checker or upstream verifier.

Preserve missing-bs4 and premature derivative-read failures and the prebinding exposure of an upstream embedded summary. Later hash checks do not repair the timing deviation. Registry, successor and definition gaps remain HOLD. Existing adjudications and parked routes including OEIS403 remain unchanged.

Sol r548 continues. Reserve fifty new disjoint records for Sol r550. Claude r504 remains rate-limited with fifty unreviewed reserved IDs. Counts remain 9 additional / 39 total / next 40.
'''
s=s[:start]+" (P/'DECISION.md').write_text("+repr(decision)+")"+s[end:]
(P/'verify.py').write_text(s)
