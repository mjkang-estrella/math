import pathlib
P=pathlib.Path(__file__).resolve().parent
s=(P/'frozen/root-mathdb-breadth-intake-r541/verify.py').read_text()
s=s.replace('root-mathdb-breadth-intake-r539','root-mathdb-breadth-intake-r541').replace('root-mathdb-breadth-intake-r537/reserved-ids.json','root-mathdb-breadth-intake-r539/reserved-ids.json')
s=s.replace('sol-mathdb-primary-qualified-breadth-r538','sol-mathdb-primary-qualified-breadth-r540').replace('sol-mathdb-primary-qualified-breadth-r542','sol-mathdb-primary-qualified-breadth-r544')
s=s.replace("6093,'6b01fd4b7be188dd453caa6c80441dd497493e8329bc45339aa05d6bd1b4c119'","7150,'1f14a9a7100b076c9741b30b7d1c474e7cfe7e7681ad60cbdb97914c220f2b44'")
s=s.replace("'corpus_chunk','line','statement_sha256'","'corpus_chunk','corpus_line_1based','statement_utf8_sha256'").replace("d['accepted_credit']","d['credit']")
s=s.replace('4483','4533').replace('4433','4483')
start=s.index(" (P/'DECISION.md').write_text(");end=s.index('\n files=[]',start)
decision='''# Root r543 reconciliation

Reconciled r540: fifty disjoint reported literal reviews, zero proposals or credit. Latest cumulative literal coverage is 4,533. The producer's prospective total uses its older assignment baseline; this reconciliation uses the latest disjoint union. No full technical or novelty corpus claim.

Six records received selected primary-passage review across nine retained bodies. No complete-body or dependency/registry clearance. Reported public-source coverage includes 381349 tensor polynomial bound, 381193 Saks-West obstruction, and 380400 period refutation. The Saks-West drawing was not reconstructed; the period computation reproduces a public example using a standard degree bound. 381505 changes source definitions and its K4 example addresses wording only. 381264 extrapolates finite data; 381458 retains unread closest-prior bodies. All evidence limits are preserved.

Preserve the failed extraction and truncated displays. Root executes no mathematical check or upstream verifier. Carry existing adjudications unchanged; scientific acceptance and registry/novelty remain HOLD.

Sol r542 continues. Reserve fifty fresh disjoint records for Sol r544. Claude r504 remains rate-limited with fifty unreviewed reserved IDs. Counts remain 9 additional / 39 total / next 40.
'''
s=s[:start]+" (P/'DECISION.md').write_text("+repr(decision)+")"+s[end:]
(P/'verify.py').write_text(s)
