import pathlib
P=pathlib.Path(__file__).resolve().parent
s=(P/'frozen/root-mathdb-breadth-intake-r513/verify.py').read_text()
s=s.replace("I=F/'root-mathdb-breadth-intake-r511'","I=F/'root-mathdb-breadth-intake-r513'").replace("N='sol-mathdb-primary-qualified-breadth-r510'","N='sol-mathdb-primary-qualified-breadth-r512'")
s=s.replace("'size':5407,'sha256':'ee0ce6303866de991af6cff4e357d03a37028c1821b89b71182439feb4193039'","'size':6290,'sha256':'0327d9d877fa2a982823c6c6e33245c4e7afaf07184d1fe43c555977381b5e0f'")
s=s.replace("['flat-bindings.json','source-bindings.json','derivative-bindings.json']","['flat-bindings.json']")
s=s.replace("exact(L/'root-mathdb-breadth-intake-r511',j(I/'manifest.json'))","exact(L/'root-mathdb-breadth-intake-r513',j(I/'manifest.json'))")
s=s.replace('3883','3933').replace('3833','3883')
s=s.replace("F/'root-mathdb-breadth-intake-r509/reserved-ids.json'","F/'root-mathdb-breadth-intake-r511/reserved-ids.json'")
s=s.replace("d['corpus_chunk']","d['corpus_path']").replace("d['corpus_line']","d['line']").replace("d['statement_utf8_sha256']","d['statement_sha256']").replace("d['accepted_credit']","d['discovery_credit']")
s=s.replace("r['lane']!='sol-mathdb-primary-qualified-breadth-r510'","r['lane']!='sol-mathdb-primary-qualified-breadth-r512'").replace("sol-mathdb-primary-qualified-breadth-r514","sol-mathdb-primary-qualified-breadth-r516")
start=s.index(" (P/'DECISION.md').write_text(");end=s.index(' files=[]',start)
s=s[:start]+" (P/'DECISION.md').write_text("+repr('''# Root r515 reconciliation

Reconcile r512: fifty disjoint literal reviews, eight selected primary-passage rows, zero proposals/credit. Latest coverage becomes 3,933 reported literal reviews. Child's older 3,833 assignment baseline is superseded by cumulative root reconciliation. No whole-body, dependency or current-registry clearance.

Preserve source-known/routine exclusions 357226 and 357065, endpoint/convention exclusions 357683 and 356681, and other technical HOLDs. Published enumeration diagnostics do not create discovery credit. Preserve two corrected helper failures, extraction/access limits, and pre-binding display of two unrelated corpus records; successful later hashing does not cure timing deviations.

Claude r504 remains rate-limited with fifty unreviewed reserved records. Sol r514 continues. Reserve next disjoint fifty for Sol r516. Existing adjudications and counts 9 additional /39 total /next40 remain unchanged. Root performs administrative/file/corpus reconciliation only. Integrity PASS is not mathematical or novelty acceptance.
''')+")\n"+s[end:]
(P/'verify.py').write_text(s);print('prepared')
