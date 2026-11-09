import pathlib
P=pathlib.Path(__file__).resolve().parent
s=(P/'frozen/root-mathdb-breadth-intake-r559/verify.py').read_text()
s=s.replace('root-mathdb-breadth-intake-r557','root-mathdb-breadth-intake-r559').replace('root-mathdb-breadth-intake-r555/reserved-ids.json','root-mathdb-breadth-intake-r557/reserved-ids.json')
s=s.replace('sol-mathdb-primary-qualified-breadth-r556','sol-mathdb-primary-qualified-breadth-r558').replace('sol-mathdb-primary-qualified-breadth-r560','sol-mathdb-primary-qualified-breadth-r562')
s=s.replace("5617,'151882554362af38a267af3d8e36c2351bfe5e5e82065fd1647f5d4387cd26d2'","4751,'2c4e38544488400189ea60b7183d7f821087441325bdb5ca7ab3d1891c8e90c3'")
s=s.replace("'chunk','line','statement_sha256'","'corpus_chunk','corpus_line','statement_utf8_sha256'")
s=s.replace('4933','4983').replace('4883','4933')
start=s.index(" (P/'DECISION.md').write_text(");end=s.index('\n files=[]',start)
decision='''# Root r561 reconciliation

Reconciled r558: fifty disjoint reported literal reviews, zero proposals or credit. Latest cumulative literal coverage is 4,983, not complete technical or novelty coverage. Three assigned rows received selected primary/successor reading; the closest Wecken successor's extracted body was read, without a full proof dependency audit.

325582 is reported covered by Izhakian-Merlet Theorem3.7, with concluding and preceding rank-case proof passages read. 322130 has a short route with a serious routine-adaptation objection and was not promoted. 325518 finite tests yield no counterexample or all-real bound. Preserve source, proof and prior evidence limits; registry and broad prior gates remain HOLD.

Retain the early frozen-inventory-header display deviation and stopped routes. No HTTP/helper failure reported. Root performs only administrative/file/corpus reconciliation, no mathematical or upstream-verifier execution. Existing adjudications and parked routes unchanged.

Sol r560 continues. Reserve fifty fresh disjoint records for Sol r562. Claude r504 remains rate-limited; its fifty IDs are reserved/unreviewed. Counts remain 9 additional / 39 total / next 40.
'''
s=s[:start]+" (P/'DECISION.md').write_text("+repr(decision)+")"+s[end:]
(P/'verify.py').write_text(s)
