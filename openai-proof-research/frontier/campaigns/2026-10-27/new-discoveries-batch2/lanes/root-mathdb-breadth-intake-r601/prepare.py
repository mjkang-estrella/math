import pathlib,json
P=pathlib.Path(__file__).resolve().parent
s=(P/'frozen/root-mathdb-breadth-intake-r599/verify.py').read_text()
s=s[:s.index('def routing_pool():')]+s[s.index('def validate():'):]
s=s.replace('root-mathdb-breadth-intake-r597','root-mathdb-breadth-intake-r599').replace('root-mathdb-breadth-intake-r595/reserved-ids.json','root-mathdb-banzhaf-retirement-intake-r503/reserved-ids-r504.json')
s=s.replace('sol-mathdb-primary-qualified-breadth-r596','claude-mathdb-primary-qualified-breadth-r504').replace('sol-mathdb-primary-qualified-breadth-r600','claude-mathdb-primary-qualified-breadth-r602')
s=s.replace("4296,'d2d6be5567fa5cbd78b4a85b412736cca7f6eb247106508fb333993ab41614df'","8592,'9c4e9834a36905625e27d63c1c9ef6e739beb5765d5746a6d75841772bf21a16'")
s=s.replace("'corpus_path','corpus_line_1based','statement_utf8_sha256'","'corpus_chunk','corpus_line','statement_utf8_sha256'")
s=s.replace("check(pathlib.Path(e['path']),e)","check(pathlib.Path(e['original']),e)")
s=s.replace("d[ck]==str(p)","d[ck]==str(p.relative_to(C))").replace("assert d['accepted_credit']==0","assert d['credit']==0")
s=s.replace('5933','5983').replace('5883','5933')
a=s.index(' route=routing_pool()',s.index('def build():'));b=s.index(' rows=[r for r in route',a)
s=s[:a]+" route=[json.loads(l) for l in (I/'routing-queue.jsonl').open()];assert len(route)==8000\n (P/'routing-queue.jsonl').write_bytes((I/'routing-queue.jsonl').read_bytes())\n"+s[b:]
a=s.index(' route=routing_pool()',s.index('def verify():'));b=s.index(' exact(P,',a)
s=s[:a]+" assert (P/'routing-queue.jsonl').read_bytes()==(I/'routing-queue.jsonl').read_bytes()\n"+s[b:]
start=s.index(" (P/'DECISION.md').write_text(");end=s.index('\n files=[]',start)
decision='''# Root r601 Claude reconciliation

Reconciled resumed Claude r504: fifty disjoint literal record reviews, zero proposals or credit. Cumulative coverage is 5,983 record reviews, not complete-statement or whole-corpus technical coverage. Its old 3,733 assignment baseline is superseded by latest disjoint-union reconciliation. Preserve reported dispositions as evidence-limited, not independently adjudicated public resolutions.

Thirty-five rows relied on abstract metadata only, one selected primary body (406512), two public pages, twelve statements only. No proof audit or current registry clearance. 383181 remains incomplete. 406512's even-n residual is not settled by its odd-n classification. 405483 ordinary/block transposition discrepancy earns no credit. No mathematical acceptance or new outcome.

Failures retained: unguarded manifest schema peek; first arXiv request transmitted the user's email in User-Agent (do not reproduce address); invalid generating-function diagnostic corrected; first manifest verification raced a still-writing log and was repaired. Integrity PASS does not cure these deviations. No external remediation messages authorized. Future delegates must use generic headers without personal identifiers. Root executes only integrity/corpus reconciliation, never upstream or math checkers.

Claude rate-limit resume completed; fifty fresh disjoint records reserved for Claude r602. Sol r598 handback now awaits reconciliation; Sol r600 continues. Adjudications/access stops unchanged; counts remain 9 additional / 39 total / next 40. No user input pending.
'''
s=s[:start]+" (P/'DECISION.md').write_text("+repr(decision)+")"+s[end:]
s=s.replace("['self_contained','scope_flags','statement_scope']","['self_contained','scope_flags','statement_scope','evidence_level']")
s=s.replace(" write('coverage-delta.json',cov)"," cov['383181']['reported_statement_incomplete']=True\n cov['383181']['source_restoration_required']=True\n write('coverage-delta.json',cov)")
(P/'verify.py').write_text(s)
ds=json.loads((P/'frozen/claude-mathdb-primary-qualified-breadth-r504/dispositions.json').read_text());print('prepared; fields:',sorted(ds[0]))
