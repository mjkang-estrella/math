import pathlib
P=pathlib.Path(__file__).resolve().parent
s=(P/'frozen/root-mathdb-breadth-intake-r585/verify.py').read_text()
s=s.replace('root-mathdb-breadth-intake-r583','root-mathdb-breadth-intake-r585').replace('root-mathdb-breadth-intake-r581/reserved-ids.json','root-mathdb-breadth-intake-r583/reserved-ids.json')
s=s.replace('sol-mathdb-primary-qualified-breadth-r582','sol-mathdb-primary-qualified-breadth-r584').replace('sol-mathdb-primary-qualified-breadth-r586','sol-mathdb-primary-qualified-breadth-r588')
s=s.replace("5907,'d077313174c43142103f85b9a1f1da98e4ad6f660b08adfe9eb9bd43a4b6f50d'","4987,'7fa8cf949b48337348279e9de2fa029369b8c7edb2e795eb3e92ada5491d7d11'")
s=s.replace("d['exact_statement_utf8']==r['statement']","d['statement_utf8']==r['statement']")
s=s.replace('5583','5633').replace('5533','5583')
start=s.index(" (P/'DECISION.md').write_text(");end=s.index('\n files=[]',start)
decision='''# Root r587 reconciliation

Reconciled r584: fifty disjoint literal record reviews, zero proposals or credit. Cumulative coverage is 5,633 record reviews, not complete-statement or whole-corpus technical coverage. Preserve all per-row scope/restoration judgments.

Three selected primary passages: 393676 asks algorithmic parity decision, not universal equality; 394297 bound/optimality already established; 394405 explicitly records directional nonuniqueness with isotropy needed for uniqueness. No cited original proof, whole report, closest-successor or full-dependency audit. Bounded rational expansion/parity illustrations do not establish new full-scope results. Current registry and scientific acceptance HOLD.

Preserve failed binding diagnostic print and corrected run after hashes persisted. Six lawful EMS fetches succeeded, stopped routes not retried. Root performs administrative integrity/corpus reconciliation only, no upstream/math checker execution.

Fresh disjoint fifty-record assignments: Sol r586 uses root r585; Sol r588 uses this intake. Claude r504 remains rate-limited with fifty reserved unreviewed IDs. No user input pending. Adjudications/access stops unchanged; counts remain 9 additional / 39 total / next 40.
'''
s=s[:start]+" (P/'DECISION.md').write_text("+repr(decision)+")"+s[end:]
(P/'verify.py').write_text(s)
print('prepared')
