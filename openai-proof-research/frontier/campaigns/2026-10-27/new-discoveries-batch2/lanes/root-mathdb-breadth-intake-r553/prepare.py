import pathlib
P=pathlib.Path(__file__).resolve().parent
s=(P/'frozen/root-mathdb-breadth-intake-r551/verify.py').read_text()
s=s.replace('root-mathdb-breadth-intake-r549','root-mathdb-breadth-intake-r551').replace('root-mathdb-breadth-intake-r547/reserved-ids.json','root-mathdb-breadth-intake-r549/reserved-ids.json')
s=s.replace('sol-mathdb-primary-qualified-breadth-r548','sol-mathdb-primary-qualified-breadth-r550').replace('sol-mathdb-primary-qualified-breadth-r552','sol-mathdb-primary-qualified-breadth-r554')
s=s.replace("5160,'f952cb8679fbdc2236252820f000c43215e0299a2ad70dc7cd69ffe5cf376612'","5414,'4d4a81a0c2fc3ec43c95c07b5c40f427a78417fe36d533697d118f37b8b533bd'")
s=s.replace("'chunk','line','statement_sha256'","'corpus_chunk','corpus_line','statement_utf8_sha256'").replace('d[ck]==str(p)','d[ck]==str(p.relative_to(C))')
s=s.replace('4733','4783').replace('4683','4733')
start=s.index(" (P/'DECISION.md').write_text(");end=s.index('\n files=[]',start)
decision='''# Root r553 reconciliation

Reconciled r550: fifty disjoint reported literal reviews, zero proposals or credit. Latest cumulative literal coverage is 4,783; this is not full technical or novelty coverage. Four selected primary passages and adjacent definitions/results inspected; no whole-source, successor-body or dependency audit.

The seven exclusion labels comprise one classical, one not-a-theorem target, and five reported-known objections. Preserve reported-known evidence status rather than upgrading unaudited proof bodies. Remaining dispositions retain construction, definition, prior, source-scope, complexity and depth gaps. No mathematical sweep or new certificate was performed by the delegate. Root executes no mathematical checker or upstream verifier.

No access failures reported. Retain stopped routes and process deviations in the frozen packet. Current registry and mathematical/novelty acceptance remain HOLD. Existing adjudications and parked routes remain unchanged.

Sol r552 continues. Reserve fifty fresh disjoint records for Sol r554. Claude r504 remains rate-limited with fifty IDs reserved/unreviewed. Counts remain 9 additional / 39 total / next 40.
'''
s=s[:start]+" (P/'DECISION.md').write_text("+repr(decision)+")"+s[end:]
(P/'verify.py').write_text(s)
