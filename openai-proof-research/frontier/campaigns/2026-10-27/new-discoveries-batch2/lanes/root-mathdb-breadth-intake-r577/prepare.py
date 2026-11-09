import pathlib,json
P=pathlib.Path(__file__).resolve().parent
s=(P/'frozen/root-mathdb-breadth-intake-r575/verify.py').read_text()
s=s.replace('root-mathdb-breadth-intake-r573','root-mathdb-breadth-intake-r575').replace('root-mathdb-breadth-intake-r571/reserved-ids.json','root-mathdb-breadth-intake-r573/reserved-ids.json')
s=s.replace('sol-mathdb-primary-qualified-breadth-r572','sol-mathdb-primary-qualified-breadth-r574').replace('sol-mathdb-primary-qualified-breadth-r576','sol-mathdb-primary-qualified-breadth-r578')
s=s.replace("5538,'8ed0994f689ae0c2eb0cb8593a5cc36a935eaeb923bd3644394dea7a3a29c740'","6052,'427da103ab022d8abcfc7d8438a14086261b81b3a3f9021f280828fbc05b8c55'")
s=s.replace("'chunk','line','statement_utf8_sha256'","'corpus_chunk','corpus_line','statement_utf8_sha256'")
s=s.replace('5333','5383').replace('5283','5333')
start=s.index(" (P/'DECISION.md').write_text(");end=s.index('\n files=[]',start)
decision='''# Root r577 reconciliation

Reconciled r574: fifty disjoint reported literal record reviews, zero proposals or credit. Cumulative coverage is 5,383 record reviews, not complete-statement or whole-corpus technical coverage. Existing source-restoration and non-self-contained flags remain unchanged.

Six selected primary-passage reviews across eight versioned HTML bodies; no complete dependency or whole-body audit. Reported 381300 v1 Farey coefficient conjecture is defeated by corrected coefficient in v3 Theorem B.2 (local proof read); 381230 is source Theorem 4.7. Neither is new credit. 381404 remains a prior-body HOLD. Alder finite diagnostic is not an all-scope proof. Thirty-five AIM-linked rows retain parked-source HOLD. No primary/prior/registry acceptance is inferred from an integrity receipt.

Preserve the worker's two corrected helper failures and source/notation limits. Root performs only administrative integrity and corpus reconciliation, not mathematical checks or upstream verifier execution. All adjudications and parked routes unchanged.

Sol r576 continues; fifty fresh disjoint records reserved for Sol r578. Claude r504 remains rate-limited with fifty IDs reserved and unreviewed. No user input pending. Counts remain 9 additional / 39 total / next 40.
'''
s=s[:start]+" (P/'DECISION.md').write_text("+repr(decision)+")"+s[end:]
s=s.replace(" write('coverage-delta.json',cov)"," for ds in data.values():\n  for d in ds:\n   for k in ['self_contained','scope_flags']:\n    if k in d:cov[str(d['mathdb_id'])]['reported_'+k]=d[k]\n write('coverage-delta.json',cov)")
(P/'verify.py').write_text(s)
ds=json.loads((P/'frozen/sol-mathdb-primary-qualified-breadth-r574/dispositions.json').read_text())
print('prepared; fields:',sorted(ds[0]))
