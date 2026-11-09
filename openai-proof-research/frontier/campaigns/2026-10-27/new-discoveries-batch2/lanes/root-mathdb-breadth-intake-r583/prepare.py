import pathlib
P=pathlib.Path(__file__).resolve().parent
s=(P/'frozen/root-mathdb-breadth-intake-r581/verify.py').read_text()
s=s.replace("I=F/'root-mathdb-breadth-intake-r579'","I=F/'root-mathdb-breadth-intake-r581'")
s=s.replace("exact(L/'root-mathdb-breadth-intake-r579'","exact(L/'root-mathdb-breadth-intake-r581'")
s=s.replace('root-mathdb-breadth-intake-r579/reserved-ids.json','root-mathdb-breadth-intake-r577/reserved-ids.json')
s=s.replace('sol-mathdb-primary-qualified-breadth-r580','sol-mathdb-primary-qualified-breadth-r578').replace('sol-mathdb-primary-qualified-breadth-r582','sol-mathdb-primary-qualified-breadth-r584')
s=s.replace("3979,'f295558703311a4e12f460db698592d3153ea0dc11966207fe6ce8a872994d73'","4689,'c7cac78c8714de04f43672ccfa02a1eb57c4235f6f48649b70f02a05d1f3380c'")
s=s.replace("'chunk','line','statement_utf8_sha256'","'corpus_chunk','corpus_line','statement_utf8_sha256'")
s=s.replace('5483','5533').replace('5433','5483')
start=s.index(" (P/'DECISION.md').write_text(");end=s.index('\n files=[]',start)
decision='''# Root r583 reconciliation

Reconciled r578: fifty disjoint reported literal record reviews, zero proposals or credit. Cumulative coverage is 5,533 record reviews, not complete mathematical statement or whole-corpus technical coverage. All scope/restoration judgments preserved; twenty-two rows explicitly need definitions/conventions restored.

388670 reported excluded by exact universal planar queue-number theorem (arXiv 1904.04791v5 Theorem 1, selected Section 4/4.1 proof passages). No full dependency replay or whole-paper clearance claimed. 390733/390411 prior leads remain HOLD because successor bodies were inaccessible. No new scientific acceptance or novelty clearance.

Preserve failed coloring HTML fetch, author certificate failure, Christensen-Hovey timeout and failed missing-text reads. Preserve derivative-binding persistence timing deviation and unassigned null-statement sentinel 413524 display: sentinel was not assessed or counted. No routes bypassed. Root performs administrative integrity/corpus reconciliation only; no upstream or mathematical checker execution.

Sol r582 continues. Fifty fresh disjoint records reserved for Sol r584. Claude r504 remains rate-limited with fifty reserved unreviewed IDs. No user input pending. All adjudications/access stops unchanged; counts remain 9 additional / 39 total / next 40.
'''
s=s[:start]+" (P/'DECISION.md').write_text("+repr(decision)+")"+s[end:]
(P/'verify.py').write_text(s)
print('prepared')
