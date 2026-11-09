import pathlib,json
P=pathlib.Path(__file__).resolve().parent
s=(P/'frozen/root-mathdb-breadth-intake-r571/verify.py').read_text()
s=s.replace('root-mathdb-breadth-intake-r569','root-mathdb-breadth-intake-r571').replace('root-mathdb-breadth-intake-r567/reserved-ids.json','root-mathdb-breadth-intake-r569/reserved-ids.json')
s=s.replace('sol-mathdb-primary-qualified-breadth-r568','sol-mathdb-primary-qualified-breadth-r570').replace('sol-mathdb-primary-qualified-breadth-r572','sol-mathdb-primary-qualified-breadth-r574')
s=s.replace("4782,'75bb161f9521724c89ecc97dd2e1abf24f16356337c3e8946ee3263d20d55f9c'","4255,'16d3370e2188a9cbfa7ec4ad32414cecb1763e422318372f702c027b9670bc03'")
s=s.replace('5233','5283').replace('5183','5233')
start=s.index(" (P/'DECISION.md').write_text(");end=s.index('\n files=[]',start)
decision='''# Root r573 reconciliation

Reconciled r570: fifty disjoint reported literal record reviews, zero proposals or credit. Cumulative coverage is 5,283 record reviews, not complete-statement or whole-corpus technical coverage. All existing source-restoration and scope flags remain unchanged.

Four selected primary passages inspected; no complete successor or dependency audit. Reported 372243 route is a routine path-Laplacian energy bound after the source Neumann condition. 365041 has only a sufficiently-large-n source resolution; all-n scope remains unqualified. 372522's claimed proof retains an unjustified numerator replacement and no identity refutation is claimed. 370182 lacks an all-n recurrence bridge. Preserve these gaps: root performs administrative integrity/corpus reconciliation only, not mathematical verification.

Preserve duplicate-self reservation helper failure and failed bs4 extraction, both corrected and recorded. Four permitted arXiv HTML fetches succeeded; no access stops bypassed. Current adjudications and protected targets remain unchanged.

Sol r572 continues; fifty fresh disjoint records reserved for Sol r574. Claude r504 remains rate-limited with fifty reserved unreviewed IDs. No user input pending. Counts remain 9 additional / 39 total / next 40.
'''
s=s[:start]+" (P/'DECISION.md').write_text("+repr(decision)+")"+s[end:]
(P/'verify.py').write_text(s)
ds=json.loads((P/'frozen/sol-mathdb-primary-qualified-breadth-r570/dispositions.json').read_text())
print('prepared; disposition field names:',sorted(ds[0]))
