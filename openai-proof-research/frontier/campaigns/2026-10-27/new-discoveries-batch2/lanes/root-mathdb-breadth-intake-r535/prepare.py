import pathlib
P=pathlib.Path(__file__).resolve().parent
s=(P/'frozen/root-mathdb-breadth-intake-r533/verify.py').read_text()
s=s.replace('root-mathdb-stack-park-intake-r531','root-mathdb-breadth-intake-r533').replace('root-mathdb-ordinal-exclusion-intake-r529/reserved-ids.json','root-mathdb-stack-park-intake-r531/reserved-ids.json')
s=s.replace('sol-mathdb-primary-qualified-breadth-r530','sol-mathdb-primary-qualified-breadth-r532').replace('sol-mathdb-primary-qualified-breadth-r534','sol-mathdb-primary-qualified-breadth-r536')
s=s.replace("5681,'8509e65d65c7b49c5bc6fd002fadaab8fd32d1d6796d52831b29ac7be26d4b46'","6926,'e3151c814c12cb1f7a227f4248f2146d16c7d41580a03d70eeff88b842f7caef'")
s=s.replace("'corpus_path','corpus_line'","'corpus_chunk','corpus_line_1based'").replace("d['statement_utf8']","d['statement']")
s=s.replace("for path,e in j(F/name/'flat-bindings.json').items():check(pathlib.Path(path),e)","for e in j(F/name/'flat-bindings.json'):check(pathlib.Path(e['path']),e)")
s=s.replace('4283','4333').replace('4233','4283')
start=s.index(" (P/'DECISION.md').write_text(");end=s.index('\n files=[]',start)
decision='''# Root r535 reconciliation

Reconciled r532: fifty disjoint reported literal reviews, zero proposals. Cumulative literal coverage is 4,333; this is not complete technical or novelty review of MathDB. Six records received selected primary-passage review across four papers. No whole-body or full dependency audit.

372399 and 372400 have explicit source resolutions in Hall arXiv:2601.01211v1 Corollaries 3.24 and 3.22. The delegate read the main proof and stated dependencies, without a full dependency audit. Preserve those evidence limits. The 371527 girth obstruction is retained uncredited as an elementary adaptation; root did not execute its graph checker or independently adjudicate its mathematics. Other source, successor and registry gaps remain HOLD.

Preserve missing BeautifulSoup, truncated-display followups and deleted temporary reading-derivative disclosures. Root performed administrative, file, corpus and assignment reconciliation only, with no upstream verifier execution. Existing adjudications including ordinal 366370 exclusion and stack-fiber 365437/365439 PARK remain unchanged.

Sol r534 continues; reserve fifty new disjoint records for Sol r536. Claude r504 remains rate-limited with its fifty IDs unreviewed and reserved. Counts remain 9 additional / 39 total / next 40.
'''
s=s[:start]+" (P/'DECISION.md').write_text("+repr(decision)+")"+s[end:]
(P/'verify.py').write_text(s)
