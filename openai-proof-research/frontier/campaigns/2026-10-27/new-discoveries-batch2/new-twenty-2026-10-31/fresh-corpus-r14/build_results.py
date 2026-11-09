import json,pathlib,hashlib,datetime
notes={
333745:'Permeability formula is an asymptotic pattern-avoidance assertion with source-dependent F_n; finite proportions alone cannot refute its limiting exponent. No full-scope mechanism found.',
333760:'Needs minimum-weight BCH word uniformly in q,m,t and cyclotomic code definitions. Small parameter equality is supporting evidence, not full resolution.',
333765:'Motivic tensor-triangular spectrum converse; no finite witness or existing Lean semantic foundations identified. Do not exploit Q/spectrum wording.',
333771:'Asymptotic ordinary-hyperplane lower bound in every d≥4; degeneracy loopholes would require source hypotheses and yield no significant correction credit.',
333775:'Asymptotic Berge incidence-matrix avoidance bound; a finite m example cannot refute Theta(m²). Needs uniform construction or extremal bound.',
333828:'Uniform bounded-diameter forest decomposition for every k and positive gap. No concrete obstruction to all diameter choices identified.',
333835:'Relative consistency in strong determinacy theory; no tractable accepted-axiom formal route found. Malformed displayed LSA is not an eligible wording target.',
333840:'Sustained pentagonal-ring exact calculation, Cauchy–Binet upper-bound attempt and 160 optimization starts; unresolved general nonsymmetric upper bound. See ATTEMPTS.md.',
333845:'55-vertex third Mycielskian exact circular-order obstruction needs exhaustive all-order certificate; coloring an instance or using bounds 8..9 is insufficient.',
333855:'Requires geometric cohomological restriction ratios for all forest shapes; previously refuted naive matching/path comparison explicitly excluded. No new family obtained.',
333875:'Hypohamiltonian snark invariant needs a nontrivial witness beyond known bounded-order checks. Search located primary-source report checking through 36, not a full proof.',
333932:'Seven-point triangle-type lower bound needs original nondegeneracy and congruence definitions; collinear wording correction excluded. No exact new configuration obtained.',
333946:'Primary Conjecture3.3 read; alpha=2 already proved. Spectral majorization shortcut fails even on P4. Full all-alpha target unresolved here.',
333956:'Known exceptional low-dimensional spherical configurations are not new significant discoveries; asymptotic all-n assertion requires source dimension qualifications. No source audit or new construction.',
333968:'Published Majstorovic2023 Theorem4 subsumes fixed-maximum-degree almost-dendrimer maximizer conjecture; theorem and relevant proof body inspected. Known result, zero credit.',
333977:'For each fixed k with sufficiently large n; a small graph without blow-up control is not a refutation. No uniform family found.',
333978:'Omega(n/hom(G)) has unspecified absolute constant; bounded finite ratios cannot refute it. Need unbounded asymptotic separation; none constructed.',
334022:'Uniform degree-dependent integral-point height bound is a deep Diophantine assertion; a fixed curve or dependence on f is insufficient.',
334037:'Universal shortest circuit cover bound implies major circuit-double-cover consequences; no small exact obstruction or complete constructive route found.',
334155:'Tower-scale asymptotic Ramsey assertion; finite colorings cannot resolve full growth. No uniform stepping-up route developed.',
334179:'Comparison against every lattice local maximum in all dimensions; one local computation does not prove global superiority. No new competitor constructed.',
334196:'Needs a 5/4-tough 2K2-free graph without a spanning2-trail, or a full theorem. Source already has subthreshold examples; those cannot count.',
334218:'Francis et al arXiv2205.06464 Corollary2 and relevant full proof chain resolve exact two-set target. Known result, zero credit.',
334220:'Sustained exact coloring search, known punctured control, ten pentagonal gluings and triangular glued families. All closed tested graphs colorable; three-color repair invariant missing. See ATTEMPTS.md.',
334223:'Full packing of reg(G)/2 edge-disjoint Hamilton cycles in every Dirac graph; endpoint/small-order corrections excluded. No mechanism identified.',
334228:'Lattice-polytope diameter and extremal Minkowski structure; corpus description of k requires original definition. No new full dimension-parameter argument.',
334238:'All oriented trees require uniform min-outdegree subdivision theorem; paths/arborescences are already known, not eligible instances.',
334239:'Existence of h(k) for all digraphs is a difficult partition problem; bounded-degree examples cannot refute existence. No unbounded obstruction.',
334249:'Quadratic clique-index bound with Theta(n) slack requires asymptotic decomposition family; finite excess alone is insufficient.',
334264:'Needs original BB-cell and dense Borel orbit closure definitions and exact graded-poset counterexample. No trustworthy semantic enumeration implemented.',
334290:'Quasi-line chromatic bound; source line-graph theorem is a known subclass. No new quasi-line obstruction or full structural theorem found.',
334302:'Difference-algebra Carlitz exponential independence, no tractable full-scope accepted-axiom Lean route identified.',
334309:'High-probability polylog susceptibility bound needs source stochastic dynamics and uniform exponent. Finite simulation not decisive.',
334313:'Davenport-constant connected zero-sum guarantee for all finite abelian groups; prime cyclic case is known. No full-scope connected-subset obstruction obtained.',
334348:'Limit unbounded reconstruction gap requires partition-minor multiplicity definitions and unbounded collision construction. Finite reconstruction data insufficient.',
334363:'Whole implication-diagram completeness requires multiple algebraic separations; one missing arrow or example would not resolve full target. No source figure audit.',
334419:'Literal record omits numerical equation and operational definitions; must consult full source before any endpoint. No invented replacement formula.',
334437:'Prior full resolution indicated by arXiv1611.06557 Theorem1 plus older small-g cases. Later theorem passage read, full later proof not audited. No rediscovery investment.',
334538:'Norm-attaining Jacobian preimage for every Hardy datum is stronger than surjectivity; no exact functional counterexample or full Lean bridge found.',
334540:'Known Sedlar–Skrekovski bow-tie index4 counterexample (2021), primary-author search passages inspected; full original proof not read here. Excluded from new credit.'}
rec=json.load(open('literal-records.json'));assert len(rec)==40 and len(notes)==40
out={}
for x in rec:
 r=x['record'];i=r['mathdb_id'];depth='literal';passages=[];proof=[]
 if i==333840:depth='primarypassage';passages=['1608.06011 introduction, §5.2 and §5.4'];proof=['Theorem15 plane-case proof only, not a proof of six-vector conjecture']
 if i==333946:depth='primarypassage';passages=['1609.00420 Conjecture3.3, Propositions3.1–3.5, Lemma3.7 proof excerpt'];proof=['selected prior quadratic-moment proof context, not full paper']
 if i==333968:depth='fullproofbody';passages=['1609.01406 definitions, Proposition1.2 proof, §4 Conjecture4.3','published Majstorovic2023 definitions, majorization Theorems2–3, Theorem4'];proof=['complete Theorem4 proof and majorization reduction; imported Jelen–Triesch theorem not independently reproved']
 if i in [334218,334220]:depth='fullproofbody';passages=['1609.09684 §5.5 Conjectures30,35, Lemma29','2205.06464 Theorem1, Corollary2 and §2'];proof=['Lemma29 construction proof','successor Observations5–20/Lemma18 proof chain; only two-color result, not full proof of three-color target']
 if i==334437:depth='primarypassage';passages=['1610.08435 Conjecture1/Theorems1–2','1611.06557 Theorem1'];proof=[]
 known=i in [333968,334218,334437,334540]
 out[str(i)]={'mathdb_id':i,'title':r['title'],'status':'excluded_prior_resolution' if known else 'parked_unresolved','accepted_credit':0,'actual_review_depth':depth,'literal_record_read':True,'primary_passages_read':passages,'relevant_proof_bodies_read':proof,'successor_search_only':i in [333875,334540],'provenance':{k:v for k,v in x.items() if k!='record'},'canonical_url':r['canonical_url'],'source_url':r['source_url'],'source_name':r['source_name'],'literal_statement':r['statement'],'assessment':notes[i],'sustained_attempt':i in [333840,334220],'attempt_file':'ATTEMPTS.md' if i in [333840,333946,333968,334218,334220,334437,334540] else None,'lean_endpoint':None,'novelty_cleared':False,'remaining_obligations':'New full-scope ordinary proof/counterexample, current bounded prior-art and published-body comparison, complete semantic Lean bridge, clean extracted strict replay and axiom audit, independent reviews and root acceptance. Prior-resolved targets ineligible.' if not known else 'No eligible new discovery. No acceptance requested.'}
json.dump(out,open('results.json','w'),indent=2,ensure_ascii=False)
json.dump({'review_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'search_dates':'2026-11-01 approximately06:56–07:04UTC; exact HTTP times in source-receipts.json','primary_prior_urls':['https://match.pmf.kg.ac.rs/electronic_versions/Match90/n3/match90n3_673-684.pdf','https://arxiv.org/abs/2205.06464','https://arxiv.org/abs/1611.06557','https://arxiv.org/abs/2111.08111','https://arxiv.org/abs/2207.03941'],'limits':['Web search results are leads; proof-body review only as itemized. No no-hit novelty inference.','No MathDB or Palomar retries; inherited403 access gaps.','No journal counterpart comparison for Fincher or total-domatic source. Majstorovic fetched as published MATCH body.','40 literal records; fullproofbody means selected relevant proof chain, not full literature audit.']},open('prior-art-limits.json','w'),indent=2)
