import pathlib
P=pathlib.Path(__file__).resolve().parent
s=(P/'frozen/root-mathdb-breadth-intake-r515/verify.py').read_text()
a=s.index('def routing_pool():');b=s.index('def validate():',a)
s=s[:a]+"def routing_pool():\n return [json.loads(l) for l in (F/'root-mathdb-breadth-intake-r515/routing-queue.jsonl').open()]\n"+s[b:]
s=s.replace("I=F/'root-mathdb-breadth-intake-r513'","I=F/'root-mathdb-breadth-intake-r515'").replace("N='sol-mathdb-primary-qualified-breadth-r512'","N='sol-mathdb-primary-qualified-breadth-r514'")
s=s.replace("'size':6290,'sha256':'0327d9d877fa2a982823c6c6e33245c4e7afaf07184d1fe43c555977381b5e0f'","'size':6201,'sha256':'26591a6286561bc3025c2d241eaee8f920f7cd334a452b91bf1ea341de243b9e'")
s=s.replace("['flat-bindings.json']","['flat-bindings.json','source-bindings.json','successor-bindings.json','derivative-bindings.json','successor-derivative-bindings.json']")
s=s.replace("exact(L/'root-mathdb-breadth-intake-r513',j(I/'manifest.json'))","exact(L/'root-mathdb-breadth-intake-r515',j(I/'manifest.json'))")
s=s.replace('3933','3983').replace('3883','3933')
s=s.replace("F/'root-mathdb-breadth-intake-r511/reserved-ids.json'","F/'root-mathdb-breadth-intake-r513/reserved-ids.json'")
s=s.replace("d['corpus_path']","d['corpus_chunk']").replace("d['line']","d['corpus_line']").replace("d['statement_sha256']","d['statement_utf8_sha256']").replace("d['discovery_credit']","d['accepted_credit']")
s=s.replace("r['lane']!='sol-mathdb-primary-qualified-breadth-r512'","r['lane']!='sol-mathdb-primary-qualified-breadth-r514'").replace("sol-mathdb-primary-qualified-breadth-r516","sol-mathdb-primary-qualified-breadth-r518")
s=s.replace("write('routing-expansion.json',{'prior_rows':4000,'added_rows':2000,'total_rows':6000,'criterion':'Remaining open/full inventory tag records, descending review_priority_score then ascending mathdb_id; automated metadata only','new_technical_reviews':0})","write('routing-provenance.json',{'source':'root-mathdb-breadth-intake-r515/routing-queue.jsonl','rows':6000,'new_technical_reviews':0,'mode':'unchanged metadata routing queue'})")
start=s.index(" (P/'DECISION.md').write_text(");end=s.index(' files=[]',start)
s=s[:start]+" (P/'DECISION.md').write_text("+repr('''# Root r517 reconciliation

Reconcile r514: fifty disjoint literal reviews, forty-seven HOLDs, two wording-only exclusions and one selected-primary public-theorem exclusion. Zero proposals/credit. Latest coverage is 3,983 reported literal reviews, not complete technical corpus coverage. Child used its assigned older 3,883 baseline; cumulative root reconciliation supersedes its prospective total.

358439 reported subsumed by arXiv2305.10828v3 Theorem1 with maximum modulus, strengthened by 2310.07926v6; selected assembly proof and successor passages only, no full dependency audit. 357943 omits minimum-arc hypothesis; 358938 conflates balance and counting conventions. These repairs earn no discovery credit. 359377 positive-edge extremal question remains held. Preserve failed bs4 extraction, repaired truncated statement displays and pre-binding administrative/provenance inspection deviation. Six HTML bodies across four targets were read selectively; no whole-body or registry clearance.

Carry verified 6,000-row r515 routing pool unchanged as metadata only. Claude r504 rate-limited/unreviewed reservation remains. Sol r516 continues; new Sol r518 receives next disjoint fifty. Existing adjudications/counts unchanged at 9 additional /39 total /next40. Root performs administrative/hash/corpus reconciliation only; no upstream verifier or mathematical checker execution. Integrity is not mathematics/novelty acceptance.
''')+")\n"+s[end:]
(P/'verify.py').write_text(s);print('prepared')
