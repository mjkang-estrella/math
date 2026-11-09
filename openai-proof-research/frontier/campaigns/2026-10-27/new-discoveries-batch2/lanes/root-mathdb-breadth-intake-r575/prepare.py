import pathlib,json
P=pathlib.Path(__file__).resolve().parent
s=(P/'frozen/root-mathdb-breadth-intake-r573/verify.py').read_text()
s=s.replace('root-mathdb-breadth-intake-r571','root-mathdb-breadth-intake-r573').replace('root-mathdb-breadth-intake-r569/reserved-ids.json','root-mathdb-breadth-intake-r571/reserved-ids.json')
s=s.replace('sol-mathdb-primary-qualified-breadth-r570','sol-mathdb-primary-qualified-breadth-r572').replace('sol-mathdb-primary-qualified-breadth-r574','sol-mathdb-primary-qualified-breadth-r576')
s=s.replace("4255,'16d3370e2188a9cbfa7ec4ad32414cecb1763e422318372f702c027b9670bc03'","5538,'8ed0994f689ae0c2eb0cb8593a5cc36a935eaeb923bd3644394dea7a3a29c740'")
s=s.replace('5283','5333').replace('5233','5283')
start=s.index(" (P/'DECISION.md').write_text(");end=s.index('\n files=[]',start)
decision='''# Root r575 reconciliation

Reconciled r572: fifty disjoint reported literal record reviews, zero proposals or credit. Cumulative coverage is 5,333 record reviews, not complete-statement or whole-corpus technical coverage. Thirty new conservative non-self-contained flags are preserved, alongside all prior flags including ellipsized 344924.

Selected primary passages for eight records across seven unversioned arXiv HTML bodies were inspected by the worker; version alignment, journal comparison, successors and full dependencies remain unqualified. 374620 is reported proved as source Theorem 3, so no new outcome. 373234 conflates a uniform-witness conjecture with a refuted VC-dimension bound; sufficiently-large-n conditions matter. Ordinary reciprocity for 374965 gives only the diagonal, not the whole bivariate identity. Source-known endpoint/chain cases and wording defects earn no credit. Root performs administrative integrity/corpus reconciliation only.

Preserve prebinding header exposure, corrected path and draft coloring error, truncated-output rereads, and the initial verifier failure from an absent excluded receipt placeholder. No upstream checker executed; no access stops bypassed. Current adjudications and protected targets remain unchanged.

Sol r574 continues; fifty fresh disjoint records reserved for Sol r576. Claude r504 remains rate-limited, fifty IDs reserved and unreviewed. No user input pending. Counts remain 9 additional / 39 total / next 40.
'''
s=s[:start]+" (P/'DECISION.md').write_text("+repr(decision)+")"+s[end:]
(P/'verify.py').write_text(s)
ds=json.loads((P/'frozen/sol-mathdb-primary-qualified-breadth-r572/dispositions.json').read_text())
print('prepared; fields:',sorted(ds[0]));print('non-self-contained:',sum(d.get('complete_self_contained_statement') is False for d in ds))
