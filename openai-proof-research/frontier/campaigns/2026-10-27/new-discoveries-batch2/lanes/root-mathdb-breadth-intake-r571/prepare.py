import pathlib,json
P=pathlib.Path(__file__).resolve().parent
s=(P/'frozen/root-mathdb-breadth-intake-r569/verify.py').read_text()
s=s.replace('root-mathdb-breadth-intake-r567','root-mathdb-breadth-intake-r569').replace('root-mathdb-breadth-intake-r565/reserved-ids.json','root-mathdb-breadth-intake-r567/reserved-ids.json')
s=s.replace('sol-mathdb-primary-qualified-breadth-r566','sol-mathdb-primary-qualified-breadth-r568').replace('sol-mathdb-primary-qualified-breadth-r570','sol-mathdb-primary-qualified-breadth-r572')
s=s.replace("4139,'c9bdf2e872aa3110b83f34e638b57132f4fb30556353fd959e3d06c942115291'","4782,'75bb161f9521724c89ecc97dd2e1abf24f16356337c3e8946ee3263d20d55f9c'")
s=s.replace("'corpus_chunk','corpus_line'","'chunk','line'").replace('5183','5233').replace('5133','5183')
start=s.index(" (P/'DECISION.md').write_text(")
end=s.index('\n files=[]',start)
decision='''# Root r571 reconciliation

Reconciled r568: fifty disjoint reported literal record reviews, zero proposals or credit. Latest cumulative coverage is 5,233 record reviews. This is not a complete-statement or full-corpus technical coverage claim. Prior incomplete record 344924 remains unchanged. Preserve each new row's conservative complete_self_contained_statement assessment: twenty-four rows have definition/source/scope HOLDs, including missing target equation 363745, ill-defined provability 363956, thin-definition discrepancy 362626 and region/quantifier mismatch 364280.

Selected passages for six records across five primary HTML sources were read; no whole-body, full-dependency or successor audit was completed. Source-internal statements and definition discrepancies blocked the proposed easy routes. Root performs only administrative integrity and corpus reconciliation, not mathematical checks. Registry and scientific acceptance remain HOLD.

Preserve parser failure, corrected omission of frozen_inputs, and prebinding structural-header inspection deviations. No access stops bypassed. All prior adjudications remain unchanged.

Sol r570 continues; fifty fresh disjoint records are reserved for Sol r572. Claude r504 remains rate-limited, fifty IDs reserved and unreviewed. No user input pending. Counts remain 9 additional / 39 total / next 40.
'''
s=s[:start]+" (P/'DECISION.md').write_text("+repr(decision)+")"+s[end:]
needle=" write('coverage-delta.json',cov)"
s=s.replace(needle," for name,ds in data.items():\n  for d in ds:\n   if 'complete_self_contained_statement' in d:cov[str(d['mathdb_id'])]['reported_complete_self_contained_statement']=d['complete_self_contained_statement']\n"+needle)
(P/'verify.py').write_text(s)
ds=json.loads((P/'frozen/sol-mathdb-primary-qualified-breadth-r568/dispositions.json').read_text())
print('prepared; completeness judgments:',[(d['mathdb_id'],d.get('complete_self_contained_statement')) for d in ds if d.get('complete_self_contained_statement') is False])
