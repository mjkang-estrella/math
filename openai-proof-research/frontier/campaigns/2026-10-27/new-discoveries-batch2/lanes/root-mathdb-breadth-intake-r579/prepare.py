import pathlib,json
P=pathlib.Path(__file__).resolve().parent
s=(P/'frozen/root-mathdb-breadth-intake-r577/verify.py').read_text()
s=s.replace('root-mathdb-breadth-intake-r575','root-mathdb-breadth-intake-r577').replace('root-mathdb-breadth-intake-r573/reserved-ids.json','root-mathdb-breadth-intake-r575/reserved-ids.json')
s=s.replace('sol-mathdb-primary-qualified-breadth-r574','sol-mathdb-primary-qualified-breadth-r576').replace('sol-mathdb-primary-qualified-breadth-r578','sol-mathdb-primary-qualified-breadth-r580')
s=s.replace("6052,'427da103ab022d8abcfc7d8438a14086261b81b3a3f9021f280828fbc05b8c55'","5653,'818170acc33e4ad45e72340e97665a13a8dbb842082f37618b3e42572c8603ac'")
s=s.replace("'corpus_chunk','corpus_line','statement_utf8_sha256'","'chunk','line','statement_sha256'")
s=s.replace('5383','5433').replace('5333','5383')
start=s.index(" (P/'DECISION.md').write_text(");end=s.index('\n files=[]',start)
decision='''# Root r579 reconciliation

Reconciled r576: fifty disjoint reported literal record reviews, zero proposals or credit. Cumulative coverage is 5,433 record reviews, not complete-statement or whole-corpus technical coverage. Preserve 23 non-self-contained, two incomplete (386396 dangling reference; 387650 malformed integrals), six ambiguous-scope, and nineteen standard-convention assessments alongside all previous flags.

Twenty-nine selected question/definition/update passages across four primary HTML bodies; no whole-paper dependency audit or closest-successor proof-body clearance. 386283's literal entropy route is routine, source intent unqualified. 387832's easy failed-normalization example does not settle the intrinsic classification. 387490/387625 source updates report answers but the cited proof bodies were not audited. No scientific acceptance or novelty clearance.

Preserve failed bs4 extraction and successful standard-library replacement. Root only checks administrative integrity and corpus reconciliation; no upstream checker or mathematical checker executed. Adjudications and parked routes unchanged.

Two fresh disjoint fifty-record batches reserved: Sol r578 uses root r577 assignment; Sol r580 uses this intake. Claude r504 remains rate-limited with fifty reserved unreviewed IDs. No user input pending. Counts remain 9 additional / 39 total / next 40.
'''
s=s[:start]+" (P/'DECISION.md').write_text("+repr(decision)+")"+s[end:]
s=s.replace("['self_contained','scope_flags']","['self_contained','scope_flags','statement_scope']")
(P/'verify.py').write_text(s)
ds=json.loads((P/'frozen/sol-mathdb-primary-qualified-breadth-r576/dispositions.json').read_text())
print('prepared; fields:',sorted(ds[0]));print('scope example:',{k:v for k,v in ds[0].items() if 'scope' in k or 'complete' in k or 'contained' in k})
