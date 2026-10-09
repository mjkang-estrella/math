#!/usr/bin/env python3
import pathlib,json,hashlib
R=pathlib.Path(__file__).resolve().parents[3]; S=R/'frontier/sources/i07_structures_novelty_r3'; O=R/'frontier/sources/i07_structures/literature'
items=[
 ('block-weinberger',O,'Published CMH 83 (2008), 21–33','Problem 1.1, Proposition 1.2, Theorems 1.5–1.6; construction discussion',[(25,207)]),
 ('bartels-lueck',O,'arXiv:0901.0442v2, 25 March 2010','Definition of class B, Theorem A, Proposition 0.3',[(15,181)]),
 ('davis-hayden-huang-ruberman-sunukjian',O,'arXiv:2411.19400v2, 9 December 2024','Theorem 1.1, Proposition 2.1, introductory reflection and lifting argument',[(14,165)]),
 ('daura-serrano',O,'Retained arXiv:2407.13602; publication IMRN 2025 rnaf126','Theorem 1.6, Proposition 1.11; definitions of Minkowski and actual symmetry',[(110,241)]),
 ('davis-book',S/'literature','Author book PDF, 2007 production text','Theorem 11.1.1 and proof; §11.7 including Proposition 11.7.1 and Theorem 11.7.3',[(10880,10995),(11550,11740)]),
 ('davis-leary',S/'literature','Author manuscript, 15 January 2004','Theorems 1–2, equivariant reflection construction §2',[(1,180)]),
 ('davis-lueck',S/'literature','Published Transactions AMS 377 (2024), 7557–7600','Definition 1.3 and complete Theorem 1.4; introduction on action versus proper model',[(60,264)]),
 ('hilman-kirstein-kremer',S/'literature','arXiv:2409.02220v1, 3 September 2024','Question 1.1, Theorem A, Corollary 1.2 and pseudofree definition',[(40,143)]),
 ('avramidi-okun-schreve',S/'literature','arXiv:2301.06112v2, 17 January 2024; GAFA 34 (2024)','Complete Theorem D, §7 proof of D(1)–(4)',[(332,365),(1673,1722)]),
 ('elementary-amenable-four',S/'literature','arXiv:2501.12512v2, 29 June 2026','Complete introductory Theorems A–D and adjacent rigidity statement',[(45,130)]),
 ('zaslavsky-balance',S/'literature','Author-hosted accepted paper, 2018','Complete Theorems 1.1–1.2 and spanning-tree balance proof',[(65,129)])]
records=[]
for name,d,version,read,ranges in items:
 f=d/(name+'.txt'); pdf=f.with_suffix('.pdf');text=f.read_text(); lines=text.splitlines()
 records.append({'name':name,'version':version,'read':read,'text_path':str(f.relative_to(R)),'pdf_path':str(pdf.relative_to(R)),'pdf_sha256':hashlib.sha256(pdf.read_bytes()).hexdigest(),'read_line_ranges':ranges,'scope_note':'Complete identified statements and comparison passages read; not a claim to have read the whole book/paper.'})
(S/'reading-index.json').write_text(json.dumps(records,indent=2)+'\n')
queries=[
'aspherical manifold outer automorphism not homotopic homeomorphism Nielsen realization reflection group trick finite index',
'Poincare duality group dimension four virtually manifold finite extension Nielsen realization',
'aspherical manifold elementary abelian arbitrarily large rank outer automorphism homeomorphism realization',
'"Equivariant Poincaré duality" "Nielsen" 2024 2025',
'"aspherical" "reflection" "equivariant" Nielsen Davis Weinberger',
'"outer" "homeomorphism" "elementary abelian" aspherical',
'"virtually" "manifold" "Poincaré duality" Nielsen 4',
'Davis Lück Nielsen realization problem 2024 manifold models classifying spaces proper actions theorem',
'Davis Leary some examples discrete group actions aspherical manifolds pdf',
'aspherical manifold self homotopy equivalence homeomorphism nonrealizable finite subgroup 2025 2026',
'Zaslavsky signed graphs balance switching theorem gains potential spanning tree pdf',
'Harary 1953 notion of balance of signed graph pdf theorem 1',
'"Nielsen" "aspherical" "2026" homeomorphism',
'"aspherical" "unrealizable" "outer" homeomorphism elementary abelian',
'"aspherical" "homeomorphism" "outer automorphisms" "realization" -site:researchgate.net -site:wikipedia.org',
'"aspherical" "not homotopic to a homeomorphism" -site:researchgate.net',
'"Nielsen realization" "2025" "aspherical" -site:researchgate.net',
'"Nielsen realization" "2026" "aspherical" -site:researchgate.net']
(S/'search-log.json').write_text(json.dumps({'date':'2026-10-08 America/Los_Angeles; 2026-10-09 UTC','provider':'web search tool','queries':queries,'retained_raw_batches':['web3.json','web4.json','web5.json'],'earlier_batches':'Queries retained here; their returned results remain in the tool transcript, not duplicated in artifact files.','selection':'Primary author/publisher/arXiv texts were followed and read. Secondary search hits were leads only, not theorem evidence.','bounded_outcome':'No exact primary-literature duplicate established. Technical-only verdict comes from explicit corpus-relative reductions, not search absence.'},indent=2)+'\n')
print('Recorded',len(records),'primary reading entries and',len(queries),'queries.')
