import pathlib
P=pathlib.Path(__file__).resolve().parent
s=(P/'frozen/root-mathdb-breadth-intake-r583/verify.py').read_text()
s=s.replace('root-mathdb-breadth-intake-r581','root-mathdb-breadth-intake-r583').replace('root-mathdb-breadth-intake-r577/reserved-ids.json','root-mathdb-breadth-intake-r581/reserved-ids.json')
s=s.replace('sol-mathdb-primary-qualified-breadth-r578','sol-mathdb-primary-qualified-breadth-r582').replace('sol-mathdb-primary-qualified-breadth-r584','sol-mathdb-primary-qualified-breadth-r586')
s=s.replace("4689,'c7cac78c8714de04f43672ccfa02a1eb57c4235f6f48649b70f02a05d1f3380c'","5907,'d077313174c43142103f85b9a1f1da98e4ad6f660b08adfe9eb9bd43a4b6f50d'")
s=s.replace("d['statement']==r['statement']","d['exact_statement_utf8']==r['statement']").replace("assert d['accepted_credit']==0","assert d['scope_flags']['accepted_credit']==0")
s=s.replace('5533','5583').replace('5483','5533')
start=s.index(" (P/'DECISION.md').write_text(");end=s.index('\n files=[]',start)
decision='''# Root r585 reconciliation

Reconciled r582: fifty disjoint literal record reviews, zero proposals or credit. Cumulative coverage is 5,583 record reviews, not complete-statement or whole-corpus technical coverage. Preserve every per-row scope flag and earlier restoration limitation.

Three selected primary passages and two successor proof sections read, no complete dependency audit. Intended Fano formula is a public theorem for n>=7; omitted small-n wording does not earn credit. AdaBoost source already reports negative maximum-margin behavior; cited construction and rational margins do not independently establish attraction or general convergence. Bernoulli finite-n minimax remains HOLD. No scientific acceptance or novelty clearance.

Retain failed disjointness check, directory diagnostic and corrected derivative-name collision. Source fetches succeeded, no access stops bypassed. Root checks administrative integrity/corpus reconciliation only, never upstream/math checkers.

Sol r584 handback arrived and awaits next reconciliation. Fifty fresh disjoint records reserved for Sol r586. Claude r504 remains rate-limited with fifty reserved unreviewed IDs. No user input pending. Adjudications unchanged; counts remain 9 additional / 39 total / next 40.
'''
s=s[:start]+" (P/'DECISION.md').write_text("+repr(decision)+")"+s[end:]
(P/'verify.py').write_text(s)
print('prepared')
