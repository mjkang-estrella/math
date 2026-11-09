import pathlib
P=pathlib.Path(__file__).resolve().parent
s=(P/'frozen/root-mathdb-breadth-intake-r511/verify.py').read_text()
s=s.replace("I=F/'root-mathdb-breadth-intake-r509'","I=F/'root-mathdb-breadth-intake-r511'")
s=s.replace("N='sol-mathdb-primary-qualified-breadth-r508'","N='sol-mathdb-primary-qualified-breadth-r510'")
s=s.replace("'size':3936,'sha256':'37713b1e05dad5511d032caf8527ecb4b4fa3fd094c7b746e6cc60feb54fccac'","'size':5407,'sha256':'ee0ce6303866de991af6cff4e357d03a37028c1821b89b71182439feb4193039'")
s=s.replace("['initial-bindings.json','flat-bindings.json']","['flat-bindings.json','source-bindings.json','derivative-bindings.json']")
s=s.replace("exact(L/'root-mathdb-breadth-intake-r509',j(I/'manifest.json'))","exact(L/'root-mathdb-breadth-intake-r511',j(I/'manifest.json'))")
s=s.replace('3833','3883').replace('3783','3833')
s=s.replace("F/'root-mathdb-banzhaf-retirement-intake-r503/reserved-ids-r508.json'","F/'root-mathdb-breadth-intake-r509/reserved-ids.json'")
s=s.replace("d['ID']","d['mathdb_id']").replace("d['chunk']","d['corpus_chunk']").replace("d['line']","d['corpus_line']").replace("d['literal']","d['statement']")
s=s.replace("r['lane']!='sol-mathdb-primary-qualified-breadth-r508'","r['lane']!='sol-mathdb-primary-qualified-breadth-r510'")
s=s.replace("sol-mathdb-primary-qualified-breadth-r512","sol-mathdb-primary-qualified-breadth-r514")
start=s.index(" (P/'DECISION.md').write_text(");end=s.index(' files=[]',start)
s=s[:start]+" (P/'DECISION.md').write_text("+repr('''# Root r513 reconciliation

Reconcile r510: fifty disjoint literal reviews, six reported eligibility exclusions and forty-four HOLDs, zero proposals/credit. Latest coverage becomes 3,883; the child used its older assigned baseline 3,783, so its prospective 3,833 total is superseded by root reconciliation. Five primary bodies read selectively; no whole-body or dependency/registry clearance.

Preserve reported exclusions 349350,405562,405620,405623,405641 from selected public primary passages and 369423 from the actual public proof embedded in the immutable corpus, not its status. Jaco manuscript/dependency body remains unread. Public Pate arithmetic (504,12288,24,512) is merely an old-certificate diagnostic, not an independently audited tensor proof or a discovery. Other public-result leads remain held. Initial metadata-before-binding deviation remains disclosed.

Claude r504 remains rate-limited with fifty unreviewed reserved IDs. Sol r512 continues. Reserve next disjoint fifty for Sol r514. Preserve adjudications and counts 9 additional /39 total /next40. Root performs administrative/hash/corpus reconciliation only, not mathematical solving or upstream verifier execution. Integrity PASS does not establish scientific acceptance.
''')+")\n"+s[end:]
(P/'verify.py').write_text(s);print('prepared')
