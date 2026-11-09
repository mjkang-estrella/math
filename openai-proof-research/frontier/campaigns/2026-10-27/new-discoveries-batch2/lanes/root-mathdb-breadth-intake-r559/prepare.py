import pathlib
P=pathlib.Path(__file__).resolve().parent
s=(P/'frozen/root-mathdb-breadth-intake-r557/verify.py').read_text()
s=s.replace('root-mathdb-breadth-intake-r555','root-mathdb-breadth-intake-r557').replace('root-mathdb-breadth-intake-r553/reserved-ids.json','root-mathdb-breadth-intake-r555/reserved-ids.json')
s=s.replace('sol-mathdb-primary-qualified-breadth-r554','sol-mathdb-primary-qualified-breadth-r556').replace('sol-mathdb-primary-qualified-breadth-r558','sol-mathdb-primary-qualified-breadth-r560')
s=s.replace("6099,'83316b778460487bbc4429b0b887e5e8b900b0de7cb4c3020a8ca732dcd884f0'","5617,'151882554362af38a267af3d8e36c2351bfe5e5e82065fd1647f5d4387cd26d2'")
s=s.replace("'corpus_chunk','corpus_line','statement_utf8_sha256'","'chunk','line','statement_sha256'")
s=s.replace('4883','4933').replace('4833','4883')
start=s.index(" (P/'DECISION.md').write_text(");end=s.index('\n files=[]',start)
decision='''# Root r559 reconciliation

Reconciled r556: fifty disjoint reported literal reviews, 25 PARK and 25 HOLD, zero exclusions, proposals or credit. Latest cumulative literal coverage is 4,933; no full technical or novelty corpus claim.

Three selected primary passages address coin normalization 316964, jumping sequences 317562 and Somos trees 318925. No whole-body, dependency, closest-successor or registry clearance. The initial coin wording-exclusion assessment was corrected: the literal record already restricts to orderly currencies, so the nonproper example is outside scope. Preserve the corrected HOLD, not the rejected exclusion. Coin-system and Somos computations are finite diagnostics only; no all-parameter result follows.

Retain extraction failure, truncated displays and limited historical reading disclosures. No new access failures. Existing adjudications and parked routes unchanged. Root performs only administrative/file/corpus checks; no mathematical or upstream-verifier execution.

Sol r558 continues. Reserve fifty fresh disjoint records for Sol r560. Claude r504 remains rate-limited; its fifty IDs remain reserved/unreviewed. Counts remain 9 additional / 39 total / next 40.
'''
s=s[:start]+" (P/'DECISION.md').write_text("+repr(decision)+")"+s[end:]
(P/'verify.py').write_text(s)
