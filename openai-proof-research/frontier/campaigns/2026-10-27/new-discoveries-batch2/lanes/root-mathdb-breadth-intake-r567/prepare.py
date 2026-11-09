import pathlib
P=pathlib.Path(__file__).resolve().parent
s=(P/'frozen/root-mathdb-breadth-intake-r565/verify.py').read_text()
s=s.replace('root-mathdb-breadth-intake-r563','root-mathdb-breadth-intake-r565').replace('root-mathdb-breadth-intake-r561/reserved-ids.json','root-mathdb-breadth-intake-r563/reserved-ids.json')
s=s.replace('sol-mathdb-primary-qualified-breadth-r562','sol-mathdb-primary-qualified-breadth-r564').replace('sol-mathdb-primary-qualified-breadth-r566','sol-mathdb-primary-qualified-breadth-r568')
s=s.replace("4769,'04e9bcc69ed35050f03ac910587ee0e4f5a9d4d58a2c7703ed9e10513414c070'","4736,'a5920c9f1582950d305069f22bf1917778e9c0f5e82692dc774ff1a9f46fadd2'")
s=s.replace("'corpus_chunk','corpus_line','statement_utf8_sha256'","'corpus_chunk','corpus_line','statement_sha256'").replace("d['statement']","d['literal_statement']")
s=s.replace('5083','5133').replace('5033','5083')
s=s.replace(" write('coverage-delta.json',cov)"," cov['344924'].update({'complete_mathematical_statement_reviewed':False,'upstream_statement_ellipsized':True,'source_restoration_required':True,'evidence_limit':'Literal record bytes reviewed; mathematical scope incomplete due to upstream ellipsization. Not a complete statement review.'})\n write('coverage-delta.json',cov)")
s=s.replace("'new_literal_reviews':50,","'new_literal_record_reviews':50,'new_complete_mathematical_statements':49,'incomplete_statement_ids':[344924],")
s=s.replace(" for k,v in old.items():assert cov[k]==v"," for k,v in old.items():assert cov[k]==v\n assert cov['344924']['complete_mathematical_statement_reviewed'] is False and cov['344924']['source_restoration_required'] is True")
start=s.index(" (P/'DECISION.md').write_text(");end=s.index('\n files=[]',start)
decision='''# Root r567 reconciliation

Reconciled r564: fifty disjoint literal record reviews, comprising 49 complete mathematical statements and incomplete record344924. Its upstream ellipsization is explicitly flagged in coverage; source restoration remains required. Latest cumulative record coverage is5,133. Do not call that a count of complete statements or full technical corpus reviews. Zero proposals or credit.

347690 confuses Cartesian and strong products; correcting it earns no credit and the genuine strong-product claim remains unresolved. 348215 has a routine central-symmetry moment route for the corpus recurrence, distinct from the source positive-coefficient conjecture. 344583 retains unexplained KW versus defined KS; no silent repair or parity theorem. Selected primary passages/local proofs only, no complete dependencies or successor/registry clearance.

Preserve extraction failure and procedural deviations. Root performs only administrative/file/corpus reconciliation, no mathematical or upstream-verifier execution. Existing adjudications and parked routes unchanged. Scientific acceptance remains HOLD.

Sol r566 continues. Reserve fifty fresh disjoint records for Sol r568. Claude r504 remains rate-limited with fifty IDs reserved/unreviewed. Counts remain9 additional/39 total/next40.
'''
s=s[:start]+" (P/'DECISION.md').write_text("+repr(decision)+")"+s[end:]
(P/'verify.py').write_text(s)
