import pathlib
P=pathlib.Path(__file__).resolve().parent
s=(P/'frozen/root-mathdb-breadth-intake-r509/verify.py').read_text()
s=s.replace("I=F/'root-mathdb-banzhaf-retirement-intake-r503'","I=F/'root-mathdb-breadth-intake-r509'")
s=s.replace("N='sol-mathdb-primary-qualified-breadth-r506'","N='sol-mathdb-primary-qualified-breadth-r508'")
s=s.replace("'size':6221,'sha256':'9146b3842984a173cf2f85be45070002e974cff2feae416afc16084b997b3853'","'size':3936,'sha256':'37713b1e05dad5511d032caf8527ecb4b4fa3fd094c7b746e6cc60feb54fccac'")
s=s.replace("['initial-bindings.json','flat-bindings.json','corpus-bindings.json','source-bindings.json','derivative-bindings.json']","['initial-bindings.json','flat-bindings.json']")
s=s.replace("exact(L/'root-mathdb-banzhaf-retirement-intake-r503',j(I/'manifest.json'))","exact(L/'root-mathdb-breadth-intake-r509',j(I/'manifest.json'))")
s=s.replace('3783','3833').replace('3733','3783')
s=s.replace("j(I/'reserved-ids-r506.json')","j(F/'root-mathdb-banzhaf-retirement-intake-r503/reserved-ids-r508.json')")
s=s.replace("d['mathdb_id']","d['ID']").replace("d['corpus_chunk']","d['chunk']").replace("d['corpus_line']","d['line']").replace("d['statement']","d['literal']")
s=s.replace("other=[j(I/'reserved-ids-r504.json'),j(I/'reserved-ids-r508.json')]","other=[r for r in j(I/'active-breadth-reservations.json') if r['lane']!='sol-mathdb-primary-qualified-breadth-r508']")
s=s.replace("sol-mathdb-primary-qualified-breadth-r510","sol-mathdb-primary-qualified-breadth-r512")
start=s.index(" (P/'DECISION.md').write_text(");end=s.index(' files=[]',start)
s=s[:start]+''' (P/'DECISION.md').write_text('''+repr('''# Root r511 reconciliation

Reconcile r508: exactly fifty new literal reviews, zero proposals and no credit. Coverage becomes 3,833 reported literal reviews; this is not full primary/proof/novelty coverage. Preserve three source-stated full-target exclusions (383495,392481,405217); 383344 remains HOLD_PUBLIC_PROOF because Eulerian convention and partial proof coverage are insufficient. Other rows remain HOLD/PARK. Four primary bodies inspected (two complete extracted local mathematical bodies, two partial); finite diagnostics are not proofs. Font/extraction warnings and truncated displays remain disclosed.

Claude r504 remains rate-limited with fifty unreviewed reserved IDs. Sol r510 continues. New Sol r512 receives the next disjoint fifty. Existing r509 adjudications carry unchanged; no scientific upgrades or root mathematics. Counts stay 9 additional /39 total /next40. Root verifies immutable inputs, assignment, literal/canonical hashes and exact file membership only. No upstream verifier execution, MathDB requests or shared scientific changes.
''')+''')
'''+s[end:]
(P/'verify.py').write_text(s)
print('prepared verifier')
