import pathlib
P=pathlib.Path(__file__).resolve().parent
s=(P/'frozen/root-mathdb-breadth-intake-r553/verify.py').read_text()
s=s.replace('root-mathdb-breadth-intake-r551','root-mathdb-breadth-intake-r553').replace('root-mathdb-breadth-intake-r549/reserved-ids.json','root-mathdb-breadth-intake-r551/reserved-ids.json')
s=s.replace('sol-mathdb-primary-qualified-breadth-r550','sol-mathdb-primary-qualified-breadth-r552').replace('sol-mathdb-primary-qualified-breadth-r554','sol-mathdb-primary-qualified-breadth-r556')
s=s.replace("5414,'4d4a81a0c2fc3ec43c95c07b5c40f427a78417fe36d533697d118f37b8b533bd'","5305,'f068999c804ece01d226ff078c395afef0e8aae26fbc6bdc7e27805b50d9fa06'")
s=s.replace("'corpus_chunk','corpus_line','statement_utf8_sha256'","'chunk','line','statement_sha256'").replace('d[ck]==str(p.relative_to(C))','d[ck]==str(p)')
s=s.replace('4783','4833').replace('4733','4783')
start=s.index(" (P/'DECISION.md').write_text(");end=s.index('\n files=[]',start)
decision='''# Root r555 reconciliation

Reconciled r552: fifty disjoint reported literal reviews, 32 PARK, 17 HOLD, one known-counterexample exclusion, zero proposals or credit. Latest cumulative literal coverage is 4,833; no complete technical or novelty corpus claim.

Four selected primary statements for 328935,338643,355557,355559 were inspected in three bodies. No whole-body, full dependency, closest-successor or registry clearance. The 561 Carmichael counterexample to 373376 is classical and uncredited. Finite Fishburn enumeration and Grassmann cardinality comparisons provide no all-parameter proof or novelty. Root did not execute mathematical checks or upstream verifier code.

Preserve failures and timing/truncation deviations in the frozen packet. No new external access failures; inherited parked routes unchanged. Existing adjudications remain unchanged. Registry, source/prior and scientific acceptance gates remain HOLD.

Sol r554 continues. Reserve fifty fresh disjoint records for Sol r556. Claude r504 remains rate-limited; its fifty IDs remain unreviewed and reserved. Counts remain 9 additional / 39 total / next 40.
'''
s=s[:start]+" (P/'DECISION.md').write_text("+repr(decision)+")"+s[end:]
(P/'verify.py').write_text(s)
