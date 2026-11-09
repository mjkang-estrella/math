import pathlib
P=pathlib.Path(__file__).resolve().parent
s=(P/'frozen/root-mathdb-breadth-intake-r543/verify.py').read_text()
s=s.replace('root-mathdb-breadth-intake-r541','root-mathdb-breadth-intake-r543').replace('root-mathdb-breadth-intake-r539/reserved-ids.json','root-mathdb-breadth-intake-r541/reserved-ids.json')
s=s.replace('sol-mathdb-primary-qualified-breadth-r540','sol-mathdb-primary-qualified-breadth-r542').replace('sol-mathdb-primary-qualified-breadth-r544','sol-mathdb-primary-qualified-breadth-r546')
s=s.replace("7150,'1f14a9a7100b076c9741b30b7d1c474e7cfe7e7681ad60cbdb97914c220f2b44'","7090,'10352ac68933ee58478bdc7611d2fb22ee6a9683582959454613fe4f726a6378'")
s=s.replace("'corpus_chunk','corpus_line_1based','statement_utf8_sha256'","'corpus_chunk','corpus_line','statement_sha256'").replace("d['statement']","d['statement_utf8']")
s=s.replace('4533','4583').replace('4483','4533')
start=s.index(" (P/'DECISION.md').write_text(");end=s.index('\n files=[]',start)
decision='''# Root r545 reconciliation

Reconciled r542: fifty disjoint reported literal reviews, zero proposals or credit. Cumulative literal coverage is 4,583, not complete MathDB technical or novelty coverage. Nine successful HTML snapshots were retained with selected passage coverage and one decisive successor construction; no complete dependency audit.

382487 is reported publicly refuted: source v2 withdraws the conjecture, and Hou-Hu arXiv2606.06208v1 Section 3 already supplies the same radius-two binary family and proof. Its 22-edge instance is uncredited. 382024 is reported to match its cited theorem. Preserve local-body evidence limits; root did not execute mathematical checks or upstream verifier code.

OEIS returned 403 and was stopped; keep this route parked without retry. Remaining source, successor, registry and novelty gaps remain HOLD. Existing adjudications and counts remain unchanged. Root checks administrative/file/corpus integrity and assignment disjointness only.

Sol r544 continues. Reserve fifty fresh disjoint records for Sol r546. Claude r504 remains rate-limited with fifty IDs reserved and unreviewed. Counts remain 9 additional / 39 total / next 40.
'''
s=s[:start]+" (P/'DECISION.md').write_text("+repr(decision)+")"+s[end:]
(P/'verify.py').write_text(s)
