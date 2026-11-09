import pathlib
P=pathlib.Path(__file__).resolve().parent
s=(P/'frozen/root-mathdb-breadth-intake-r561/verify.py').read_text()
s=s.replace('root-mathdb-breadth-intake-r559','root-mathdb-breadth-intake-r561').replace('root-mathdb-breadth-intake-r557/reserved-ids.json','root-mathdb-breadth-intake-r559/reserved-ids.json')
s=s.replace('sol-mathdb-primary-qualified-breadth-r558','sol-mathdb-primary-qualified-breadth-r560').replace('sol-mathdb-primary-qualified-breadth-r562','sol-mathdb-primary-qualified-breadth-r564')
s=s.replace("4751,'2c4e38544488400189ea60b7183d7f821087441325bdb5ca7ab3d1891c8e90c3'","5288,'eb5ff7a56d42491d0c3ef73ad2b73b9620d0277cab7eb7f18f13cacab4b9a291'")
s=s.replace("'corpus_chunk','corpus_line','statement_utf8_sha256'","'corpus_chunk','corpus_line','statement_sha256'").replace("d['statement']","d['literal_statement']")
s=s.replace('4983','5033').replace('4933','4983')
start=s.index(" (P/'DECISION.md').write_text(");end=s.index('\n files=[]',start)
decision='''# Root r563 reconciliation

Reconciled r560: fifty disjoint reported literal reviews, zero proposals or credit. Latest cumulative literal coverage is 5,033; no complete technical or novelty corpus claim. Two primary question passages, one source-internal local proof and two successor local theorem bodies inspected. No whole-body or complete dependency audit.

328279 is refuted in its own source; its odd-order theorem already covers the reproduced small witness. 333786 is reported subsumed by1911.12459v1 Theorem1 specialized to a chain. 334590 has an exact finite-rank plactic identity theorem in1906.03991v2. Original plactic-question HTML was unavailable; tropical-identity and representation dependencies were not fully replayed. Preserve these scope and proof-coverage limits; no root mathematical checker or upstream verifier execution.

Retain three HTML404s and extraction dependency failure with conversion limits. Source/prior/registry and scientific acceptance gates remain HOLD. Existing adjudications and parked routes unchanged.

Sol r562 continues. Reserve fifty fresh disjoint records for Sol r564. Claude r504 remains rate-limited with fifty IDs reserved/unreviewed. Counts remain 9 additional / 39 total / next 40.
'''
s=s[:start]+" (P/'DECISION.md').write_text("+repr(decision)+")"+s[end:]
(P/'verify.py').write_text(s)
