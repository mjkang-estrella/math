import pathlib
P=pathlib.Path(__file__).resolve().parent
s=(P/'frozen/root-mathdb-breadth-intake-r589/verify.py').read_text()
s=s.replace('root-mathdb-breadth-intake-r587','root-mathdb-breadth-intake-r589').replace('root-mathdb-breadth-intake-r585/reserved-ids.json','root-mathdb-breadth-intake-r587/reserved-ids.json')
s=s.replace('sol-mathdb-primary-qualified-breadth-r586','sol-mathdb-primary-qualified-breadth-r588').replace('sol-mathdb-primary-qualified-breadth-r590','sol-mathdb-primary-qualified-breadth-r592')
s=s.replace("4718,'03df7f8234efb955c21fd20a1f781e7d9fafac6532f192825b36a18dfc26ea81'","6547,'d7d18cd63916b1d5d1636aa41514ae9569e2df8f818a56faab477dbc8cfd2f8f'")
s=s.replace("d['statement']==r['statement']","d['literal_statement']==r['statement']").replace("assert d['credit']==0","assert d['accepted_credit']==0")
s=s.replace('5683','5733').replace('5633','5683')
start=s.index(" (P/'DECISION.md').write_text(");end=s.index('\n files=[]',start)
decision='''# Root r591 reconciliation

Reconciled r588: fifty disjoint literal record reviews, zero proposals or credit. Cumulative coverage is 5,733 record reviews, not complete-statement or whole-corpus technical coverage. Preserve all scope/restoration flags and source evidence limits.

Four primary passages, one related passage and one selected successor proof section read; no whole-report/full dependency audit. 396990 norm-control has a direct public successor estimate (arXiv 1211.2974v1 section 3.3 Proposition 3.3(ii)); no new credit. Finite partitions do not establish general subspace attainment, rectangle costs lack matching lower bound, and the cone-aperture shortcut is partial/routine. Registry and scientific acceptance HOLD.

Nine lawful public fetches succeeded; retained metadata-timing deviation and inherited stopped routes. Root performs administrative integrity/corpus reconciliation only, never upstream or mathematical checkers. All adjudications unchanged.

Sol r590 continues. Fifty fresh disjoint records reserved for Sol r592. Claude r504 remains rate-limited with fifty reserved unreviewed IDs. No user input pending. Counts remain 9 additional / 39 total / next 40.
'''
s=s[:start]+" (P/'DECISION.md').write_text("+repr(decision)+")"+s[end:]
(P/'verify.py').write_text(s)
print('prepared')
