import pathlib
P=pathlib.Path(__file__).resolve().parent
s=(P/'frozen/root-mathdb-breadth-intake-r567/verify.py').read_text()
s=s.replace('root-mathdb-breadth-intake-r565','root-mathdb-breadth-intake-r567').replace('root-mathdb-breadth-intake-r563/reserved-ids.json','root-mathdb-breadth-intake-r565/reserved-ids.json')
s=s.replace('sol-mathdb-primary-qualified-breadth-r564','sol-mathdb-primary-qualified-breadth-r566').replace('sol-mathdb-primary-qualified-breadth-r568','sol-mathdb-primary-qualified-breadth-r570')
s=s.replace("4736,'a5920c9f1582950d305069f22bf1917778e9c0f5e82692dc774ff1a9f46fadd2'","4139,'c9bdf2e872aa3110b83f34e638b57132f4fb30556353fd959e3d06c942115291'")
s=s.replace("'corpus_chunk','corpus_line','statement_sha256'","'corpus_chunk','corpus_line','statement_utf8_sha256'").replace("d['literal_statement']","d['statement']")
s=s.replace('5133','5183').replace('5083','5133')
s=s.replace("'new_complete_mathematical_statements':49,",'').replace("'incomplete_statement_ids':[344924]","'carried_incomplete_statement_ids':[344924]")
s='\n'.join(line for line in s.split('\n') if not line.startswith(" cov['344924'].update("))
start=s.index(" (P/'DECISION.md').write_text(");end=s.index('\n files=[]',start)
decision='''# Root r569 reconciliation

Reconciled r566: fifty disjoint reported literal record reviews, zero proposals or credit. Latest cumulative record coverage is5,183. This is not a count of completely qualified mathematical statements: prior344924 remains flagged for ellipsized source restoration, unchanged.

Three selected primary IDs and one successor were inspected. Reported source coverage stops investment for349116 volume formula (successor Theorem5.11),357365 determinant conjecture (proved later in its source),354537 scaled identity (direct source Theorem4.3 substitution). 356255 is wording-only. Preserve selected-passage/dependency limits; registry and scientific acceptance remain HOLD. Root executes no mathematical checker or upstream verifier.

Retain pre-validation queue-metadata display and truncated locator/context output deviations. No access stops bypassed. Existing adjudications and parked routes unchanged.

Sol r568 continues. Reserve fifty fresh disjoint records for Sol r570. Claude r504 remains rate-limited with fifty IDs reserved/unreviewed. Counts remain9 additional/39 total/next40.
'''
s=s[:start]+" (P/'DECISION.md').write_text("+repr(decision)+")"+s[end:]
(P/'verify.py').write_text(s)
