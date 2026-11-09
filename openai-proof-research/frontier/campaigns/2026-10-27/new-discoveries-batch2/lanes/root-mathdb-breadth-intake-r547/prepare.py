import pathlib
P=pathlib.Path(__file__).resolve().parent
s=(P/'frozen/root-mathdb-breadth-intake-r545/verify.py').read_text()
s=s.replace('root-mathdb-breadth-intake-r543','root-mathdb-breadth-intake-r545').replace('root-mathdb-breadth-intake-r541/reserved-ids.json','root-mathdb-breadth-intake-r543/reserved-ids.json')
s=s.replace('sol-mathdb-primary-qualified-breadth-r542','sol-mathdb-primary-qualified-breadth-r544').replace('sol-mathdb-primary-qualified-breadth-r546','sol-mathdb-primary-qualified-breadth-r548')
s=s.replace("7090,'10352ac68933ee58478bdc7611d2fb22ee6a9683582959454613fe4f726a6378'","3815,'5ecb612ffc61085fd15fe771eadb28c3095b0bcb3ca43795194d5654534804e6'")
s=s.replace("'corpus_chunk','corpus_line','statement_sha256'","'chunk','line','statement_sha256'").replace("d['statement_utf8']","d['statement']").replace("d['credit']","d['accepted_credit']")
s=s.replace('4583','4633').replace('4533','4583')
start=s.index(" (P/'DECISION.md').write_text(");end=s.index('\n files=[]',start)
decision='''# Root r547 reconciliation

Reconciled r544: fifty disjoint reported literal reviews, zero proposals or credit. Latest cumulative literal coverage is 4,633; no complete technical corpus or novelty claim. Three selected primary passages were read from verified immutable snapshots. No whole-body, complete local proof, successor or dependency audit.

395938 is reported as a theorem explicitly stated in Benzi's OWR37/2009 contribution, sufficient to stop discovery investment without a proof audit. 398787 retains the distinction between integral generation and a rank-sized integral basis, plus unread successors. 400959 has a suggested routine finite-linear-programming route but no implementation or eligible outcome. Other rows retain individual HOLDs and source evidence limits.

Preserve the initial checker failure, corrected duplicate-self reservation logic, guessed missing pathname and metadata reuse-order deviation. Root runs only administrative/file/corpus checks, no upstream verifier or mathematical code. All adjudications remain unchanged. Registry and novelty stay HOLD. OEIS A274199/internal 403 remains parked.

Sol r546 continues. Reserve fifty fresh disjoint records for Sol r548. Claude r504 remains rate-limited; its fifty IDs remain reserved/unreviewed. Counts remain 9 additional / 39 total / next 40.
'''
s=s[:start]+" (P/'DECISION.md').write_text("+repr(decision)+")"+s[end:]
(P/'verify.py').write_text(s)
