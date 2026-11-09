import pathlib
P=pathlib.Path(__file__).resolve().parent
s=(P/'frozen/root-mathdb-breadth-intake-r563/verify.py').read_text()
s=s.replace('root-mathdb-breadth-intake-r561','root-mathdb-breadth-intake-r563').replace('root-mathdb-breadth-intake-r559/reserved-ids.json','root-mathdb-breadth-intake-r561/reserved-ids.json')
s=s.replace('sol-mathdb-primary-qualified-breadth-r560','sol-mathdb-primary-qualified-breadth-r562').replace('sol-mathdb-primary-qualified-breadth-r564','sol-mathdb-primary-qualified-breadth-r566')
s=s.replace("5288,'eb5ff7a56d42491d0c3ef73ad2b73b9620d0277cab7eb7f18f13cacab4b9a291'","4769,'04e9bcc69ed35050f03ac910587ee0e4f5a9d4d58a2c7703ed9e10513414c070'")
s=s.replace("'corpus_chunk','corpus_line','statement_sha256'","'corpus_chunk','corpus_line','statement_utf8_sha256'").replace("d['literal_statement']","d['statement']")
s=s.replace('5033','5083').replace('4983','5033')
start=s.index(" (P/'DECISION.md').write_text(");end=s.index('\n files=[]',start)
decision='''# Root r565 reconciliation

Reconciled r562: fifty disjoint reported literal reviews, zero proposals or credit. Latest cumulative literal coverage is 5,083, not complete technical or novelty coverage. Four assigned IDs received selected primary reading and two successors received selected proof/question reading. No complete dependency audit or registry clearance.

335328 capacity-two juggling is explicitly proved by the reported successor2402.09903v2 Example3.7 and is ineligible. The equitable quotient route is a standard matrix-norm/Gelfand adaptation with a reported later proof whose institutional body fetch failed. Finite overpartition checks give neither counterexample nor uniform proof. Preserve all scope and evidence limits; root executes no mathematical checker or upstream verifier.

Retain prebinding inventory-header display, the failed non-PDF response not retained or hashed, and context truncation followed by scoped rereading. Integrity verification does not repair those deviations. Source, prior, registry and scientific acceptance gates remain HOLD. Existing adjudications and parked routes unchanged.

Sol r564 continues. Reserve fifty fresh disjoint records for Sol r566. Claude r504 remains rate-limited with fifty IDs reserved/unreviewed. Counts remain 9 additional / 39 total / next 40.
'''
s=s[:start]+" (P/'DECISION.md').write_text("+repr(decision)+")"+s[end:]
(P/'verify.py').write_text(s)
