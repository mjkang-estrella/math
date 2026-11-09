import pathlib
P=pathlib.Path(__file__).resolve().parent
s=(P/'frozen/root-mathdb-breadth-intake-r587/verify.py').read_text()
s=s.replace('root-mathdb-breadth-intake-r585','root-mathdb-breadth-intake-r587').replace('root-mathdb-breadth-intake-r583/reserved-ids.json','root-mathdb-breadth-intake-r585/reserved-ids.json')
s=s.replace('sol-mathdb-primary-qualified-breadth-r584','sol-mathdb-primary-qualified-breadth-r586').replace('sol-mathdb-primary-qualified-breadth-r588','sol-mathdb-primary-qualified-breadth-r590')
s=s.replace("4987,'7fa8cf949b48337348279e9de2fa029369b8c7edb2e795eb3e92ada5491d7d11'","4718,'03df7f8234efb955c21fd20a1f781e7d9fafac6532f192825b36a18dfc26ea81'")
s=s.replace("d['statement_utf8']==r['statement']","d['statement']==r['statement']").replace("assert d['scope_flags']['accepted_credit']==0","assert d['credit']==0")
s=s.replace('5633','5683').replace('5583','5633')
start=s.index(" (P/'DECISION.md').write_text(");end=s.index('\n files=[]',start)
decision='''# Root r589 reconciliation

Reconciled r586: fifty disjoint literal record reviews, zero proposals or credit. Cumulative coverage is 5,683 record reviews, not complete-statement or whole-corpus technical coverage. Preserve every scope flag and earlier restoration limitation.

Two primary question passages read: 394644 fair duel and 394645 hp-convolution, both with source results already present. Fair-duel improvement is source-reported, cited full proofs unread. hp three-space definitions/coefficient integrals/coarsening lemma are source results, extended preprint unread. 394477 selected public threshold theorem proof sections cover fixed r>=2 and F containing an edge, without full dependency audit. Small illustrations and wording/classical routes earn no credit. Registry/scientific acceptance HOLD.

Both assigned/current intake validations were reported; root independently reconciles exact assignment and latest coverage. Root runs no upstream or mathematical checker. All access stops and adjudications unchanged.

Sol r588 continues. Fifty fresh disjoint records reserved for Sol r590. Claude r504 remains rate-limited with fifty reserved unreviewed IDs. No user input pending. Counts remain 9 additional / 39 total / next 40.
'''
s=s[:start]+" (P/'DECISION.md').write_text("+repr(decision)+")"+s[end:]
(P/'verify.py').write_text(s)
print('prepared')
