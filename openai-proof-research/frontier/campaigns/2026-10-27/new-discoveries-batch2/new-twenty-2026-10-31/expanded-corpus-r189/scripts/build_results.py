"""Build results.json (exactly 20 ID-keyed dispositions) from extracted.json provenance
and the hand-written dispositions below.  usage: build_results.py"""
import json, pathlib
L = pathlib.Path(__file__).resolve().parents[1]
ext = json.loads((L / 'extracted.json').read_text())
res = json.loads((L / 'reservation.json').read_text())
rec = {r['id']: r for r in json.loads((L / 'outputs/fetch-receipts.json').read_text())}
def rc(*ids):
    return [{k: rec[i][k] for k in ('id', 'url', 'status', 'sha256', 'utc')} for i in ids if i in rec]

D = {
 333082: dict(outcome='parked_open_analytic', credit='none', review_depth='abstract and version history (v2, 2017); statement not in the MathDB span (g_n bar undefined there)',
   detail='Pfister-Urbanke polar-code interpolation concavity: an analytic statement about functions on [0,1] for all n; no finite certificate route and no Lean-feasible mechanism. Not pursued per the brief (analytic/deep).',
   receipts=rc('abs-1605.01997')),
 333117: dict(outcome='parked_open_deep', credit='none', review_depth='abstracts of 1605.04415 (Han-Zhu) and 1605.04690 (Zhu); citing-work web search',
   detail="Zhu's (5m-1,m)-choosability conjecture for planar graphs (JCTB 2017 Conjecture 3). No resolution found (searches 2026-11-05); a refutation would need a planar graph that is not (5m-1,m)-choosable for every m and a proof needs a uniform discharging argument. Classic colouring problem penalised by reserve8; not Lean-cheap.",
   receipts=rc('abs-1605.04415', 'abs-1605.04690', 'ep-1605.04690')),
 333134: dict(outcome='parked_open_deep', credit='none', review_depth='source TeX (2016-5-16.tex) read for the conjecture; citing-work search',
   detail='Every planar graph (9,2)-choosable (Zhu, JCTB 2017 Conjecture 4). Open; known: not (8,2)-choosable examples exist (4m+floor((2m-1)/9) bound), 1-defective (9,2)-paintable (Han-Zhu). A counterexample would be a planar graph plus an exhaustive list-assignment certificate: the space is huge, with no structured lead. Parked.',
   receipts=rc('abs-1605.04690', 'ep-1605.04690')),
 333144: dict(outcome='parked_after_exhaustive_search_supporting_conjecture', credit='none', review_depth='full source TeX read (definitions, Theorem 1, Corollaries 1-2, all proofs, Conjectures 1-3); DMGT 2018 version of record; Chen-Wang-Wu DMGT 41 (2021) subcubic case found by search (abstract level)',
   detail=('Conjecture 1 of Henning-Jager-Rautenbach (finitely many minimal forbidden induced subgraphs). Exact source definitions implemented (scripts/hered.py). '
           'Complete level-by-level vertex-extension enumeration of the hereditary class through order 9 (member counts 1,2,4,11,34,154,974,9758 for n=1..8; level 9 in 5 chunks). '
           'Minimal forbidden induced subgraphs found: order 6: 2 (F1 and the net), order 7: 12 (incl. P7, C7), order 8: 4 (incl. the Wagner graph C8(1,4)), order 9: 2 (incl. C9(1,3)); total 20 (outputs/hered/minimal-forbidden-through-9.json). '
           'Every one has gamma = 3 and gamma_e = 2, consistent with the source Conjecture 2. Direct scan of all circulants C_n(S) for n = 8..13 (scripts/circ.py): minimal forbidden only C8(1,4) and C9(1,3). '
           'The data support the conjecture (counts 2,12,4,2 by order), so there is no refutation route; a full proof would need a new bound on the order of minimal forbidden graphs (research-level structural case analysis; the source needed ~4 pages for a subclass). '
           'Coverage limit: order 10 (274668 graphs) not enumerated. Parked; the list is reusable data.'),
   receipts=rc('abs-1605.05056', 'ep-1605.05056')),
 333240: dict(outcome='parked_open_analytic', credit='none', review_depth='abstract and version history (v2, 2017)',
   detail='Schweinhart curvature-flow universality for embedded graphs: dynamical/analytic statement, no finite certificate. Not pursued per the brief.',
   receipts=rc('abs-1605.09063')),
 333242: dict(outcome='source_defect_literal_false_zero_credit', credit='none', review_depth='full source TeX read (Theorems 1.1-1.2, proofs, Section 3 Conjecture); exact-integer computation',
   detail=('The MathDB statement copies Xiong Conjecture 3.1 literally: (p1 h(q^p1) - p2 h(q^p2))/(q)_inf has positive coefficients of q^n for n >= p2. As printed this fails at n = p2 for every pair: the numerator begins -p2 q^p2 (h(q) = q + ...), so the coefficient is exactly -p2 (verified for all 465 prime pairs below 128, scripts/xiong.py). '
           'The sign-reversed reading p2 h(q^p2) - p1 h(q^p1), which is the one that would imply the ACKO conjecture as the source says, also fails, at (p1,p2,n) = (3,2,3) with coefficient -1 (M_3 has 0 at q^3 by the source\'s own printed series); it holds for all other prime pairs below 128 through n = 2000. '
           'Both are sign/endpoint corrections of the source statement (zero-credit class, cf. the 361538/358821 precedents); the corrected intended statement (p2 >= 3, or excluding (3,2)) is an analytic circle-method-type problem with no finite route. Logs: logs/xiong-60-600.log, logs/xiong-130-2000.log.'),
   receipts=rc('abs-1605.09135', 'ep-1605.09135')),
 333317: dict(outcome='parked_open_deep', credit='none', review_depth='abstract, version of record (Pacific J. Math. 292 (2018)); citing-work search',
   detail='Gubeladze-Michalek cone conjecture: proved for d = 3, only computational evidence for d = 4 (searches 2026-11-05). Infinite-dimensional lattice-geometric statement; no tractable finite certificate (a refutation would need a pair of cones with C in C\' but not reachable through additive-generation chains, which is a search over unbounded chains). Parked.',
   receipts=rc('abs-1606.02083')),
 333321: dict(outcome='known_resolved_zero_credit', credit='none', review_depth='source TeX read (S_4 = Pasch graphs, lines 202-204, 593-594); Knauer-Marc arXiv:1701.05525 v3 abstract read',
   detail='S_4 in Chepoi-Knauer-Marc is the class of Pasch graphs. Knauer-Marc, "On tope graphs of complexes of oriented matroids" (arXiv:1701.05525, published Discrete Comput. Geom. 2020), abstract: "all finite Pasch graphs are tope graphs of complexes of oriented matroids, which confirms a conjecture of Chepoi and the two authors". Known; excluded.',
   receipts=rc('abs-1606.02154', 'ep-1606.02154', 'abs-1701.05525')),
 333333: dict(outcome='source_defect_literal_false_zero_credit', credit='none', review_depth='source TeX Section 7 (definition of the first shape coefficient, Conjecture, Examples) read',
   detail='Zeng defines S_1(Omega) = sup d1^2/d2^2 over cubes Sigma1 in Omega in Sigma2, so S_1 <= 1 with equality only for cubes. At k = 1 the conjectured bound reads lambda_2 - lambda_1 <= S_1 (lambda_2 - lambda_1), which fails for every non-cube bounded domain (lambda_2 > lambda_1 on a connected domain). A trivial definitional/formulation defect of the source (zero credit); the intended normalisation is unknown, and the problem is analytic. Parked.',
   receipts=rc('abs-1606.02589', 'ep-1606.02589')),
 333334: dict(outcome='source_defect_literal_false_zero_credit', credit='none', review_depth='same source section as 333333',
   detail='Same defect with balls: S_2 = sup r1^2/r2^2 <= 1 with equality only for balls, so k = 1 fails for every non-ball domain. Zero credit (formulation defect); analytic. Parked.',
   receipts=rc('abs-1606.02589', 'ep-1606.02589')),
 333359: dict(outcome='parked_open_needs_sat', credit='none', review_depth='source TeX read (definitions, Section 5 SAT encoding with the 4- and 5-point rules, Lemma L:extobs); JGAA 21(6) (2017) version of record; citing-work search',
   detail='obs_out(X_n) = 2 for all n >= 4; the authors settle n = 4,5,6 by SAT unsatisfiability of chirotope-based necessary conditions. Extending it needs SAT solving (forbidden in this Claude lane) or a uniform combinatorial proof for all n over abstract orientations (no mechanism found). A refutation would need an explicit one-outside-obstacle drawing for some n >= 7, which the conjecture predicts does not exist. Parked for a Sol lane with SAT if root wants n = 7,8 data.',
   receipts=rc('abs-1606.03782', 'ep-1606.03782')),
 333370: dict(outcome='proved_full_scope_but_routine_classical_bridge_zero_credit', credit='none (routine bridge from Gessel-Reutenauer 1993 Thm 4.1, restated explicitly by Elizalde-Troyka JCTA 2019)', review_depth='full source TeX v2 read (definitions, main theorem, length-3 proofs, Section 8 conjectures); Elizalde-Troyka arXiv:1710.05103 v3 TeX read (Section "Complements of descent sets"); exhaustive computation',
   detail=('PROOF (all k >= 2): membership of pi in the sigma-class depends only on Des(pi); pi -> w0 pi (value complement) maps C_n bijectively onto w0 C_n, complements Des, and maps S^sigma to S^{sigma^c}. Hence c_sigma(n) = sum_{D in Des(S^sigma)} beta(D) and c_{sigma^c}(n) = sum_{D in Des(S^sigma)} beta([n-1] minus D), where beta(D) = number of n-cycles with descent set D. '
           'By Gessel-Reutenauer, beta(D) = <L_n, r_D> with L_n = (1/n) sum_{d|n} mu(d) p_d^{n/d}; omega r_D = r_{D^c} and omega L_n = (1/n) sum mu(d) (-1)^{n-n/d} p_d^{n/d} = L_n when n is not 2 mod 4 (a squarefree d with n/d odd would have to contain the whole 2-power of n). So beta(D) = beta(D^c) and c_sigma(n) = c_{sigma^c}(n) for n not 2 mod 4. '
           'PRIOR ART: Elizalde-Troyka (arXiv:1710.05103, J. Combin. Theory Ser. A 165 (2019) 360-391), Section "Complements of descent sets": "It follows from [GR, Thm. 4.1] that beta^cyc_n(I bar) = beta^cyc_n(I) when n is not 2 mod 4". The conjecture is therefore a few-line consequence of a 1993 classical theorem (zero credit, cf. 343238/345906/351504). '
           'Computation (independent check): c_sigma(n) for all sigma of length 4 and 5 and n <= 11 (scripts/cycgrid.py, cycsweep.py; DFS validated against the source Table 1 and brute force); complementary pairs agree for all n not 2 mod 4. The descent-set symmetry was checked for n <= 9 (logs/cycdes-2-9.log). '
           'SIDE FINDING (not a MathDB item in this corpus): the source\'s stronger Conjecture 38 (signatures with the same number of corners are weakly cyc-Wilf-equivalent) is FALSE: c_{+++-}(7) = 433 but c_{++--}(7) = 418 (both one corner, n = 7 odd; brute-force verified over all 5040 permutations); also fails at n = 8, 9, 11 and for k = 5. The corpus has no record for Conjecture 38 (only 333370, 333371 cite 1606.04502), so it is not creditable here.'),
   receipts=rc('abs-1606.04502', 'ep-1606.04502', 'abs-1710.05103', 'ep-1710.05103')),
 333371: dict(outcome='source_resolved_in_current_version_zero_credit', credit='none', review_depth='source TeX v2 (2018) read: Section "Alternating grid classes"',
   detail='The alternating-signature conjecture appears only commented out in v2 (lines 941-944) and is replaced by a Theorem (live text): "For all k >= 2, the signatures sigma_alt^{+k} and sigma_alt^{-k} are cyc-Wilf-equivalent", proved via Lemma lem:alt plus the main theorem; the v2 abstract and introduction also state it. MathDB copied the v1 conjecture (r134 lesson). Zero credit. Consistent with the computation (k = 5: +-+-+ and -+-+- agree for all n <= 11).',
   receipts=rc('abs-1606.04502', 'ep-1606.04502')),
 333522: dict(outcome='parked_famous_open', credit='none', review_depth='abstract of the source (Hatami-de Quehen)',
   detail='Jaeger-Linial-Payan-Tarzi additive bases conjecture: famous open problem (p = 3 implies the weak 3-flow conjecture); the source proves only a log n-type bound. Disposed quickly per the brief.',
   receipts=rc('abs-1607.00563')),
 333594: dict(outcome='parked_famous_open', credit='none', review_depth='abstract; web search for later status',
   detail='Potocnik-Spiga-Verret conjecture (semiprimitive iff graph-restrictive): the graph-restrictive => semiprimitive direction is proved by PSV (2012); the converse is open (Giudici-Morgan describe it as possibly the most intractable problem in the section). No finite certificate route. Parked.',
   receipts=rc('abs-1607.03798')),
 333609: dict(outcome='known_resolved_zero_credit', credit='none', review_depth='source abstract; Tang-Ding-Xiong DCC 87 (2019) 2793-2811 / arXiv:1901.09228 (abstract level via search)',
   detail='The Ding-Li conjecture that all supports of every nonzero weight in the two ternary cyclic codes of length (3^m-1)/2 (m odd) form 2-designs was proved by Tang, Ding and Xiong, "Steiner systems S(2,4,(3^m-1)/2) and 2-designs from ternary linear codes of length (3^m-1)/2" (Des. Codes Cryptogr. 2019), who prove Conjectures 1 and 2 of Ding-Li. Known; excluded (also near the excluded 336565 design family).',
   receipts=rc('abs-1607.04813', 'ep-1607.04813')),
 333726: dict(outcome='parked_open_not_lean_feasible', credit='none', review_depth='abstract, v3 (referee corrections); Crump thesis noted via search (equal permanents for unexplained equal-period pairs)',
   detail='Equal periods => equal extended graph permanents. Open; the thesis reports agreement on pairs with equal (conjectured) periods. A refutation needs graphs with PROVEN equal Feynman periods: a literal Lean endpoint would need Feynman periods formalised (infeasible), and the topic is adjacent to the credited 352253 family. Parked.',
   receipts=rc('abs-1608.01414')),
 333908: dict(outcome='parked_open_deep', credit='none', review_depth='abstract (J. Algebra version of record)',
   detail='Maximal commutativity of the spectral-curve Hamiltonians in A/[A,A]: an infinite-dimensional algebraic maximality statement; finite computations can only check commutativity in bounded degree. Parked.',
   receipts=rc('abs-1608.08287')),
 334120: dict(outcome='source_suppressed_conjecture_zero_credit', credit='none', review_depth='full source TeX read; \\iffalse/\\fi structure verified',
   detail='The G-positivity order and the conjugation conjecture appear only in lines 1248-1292 of the arXiv TeX, enclosed in \\iffalse ... \\fi (opened at 1248, closed at 1292 before the Acknowledgments). They are absent from the compiled arXiv v1 paper (the only arXiv version), so the conjecture was suppressed by the authors (treated as withdrawn, per the 349435 precedent). The Involve 11 (2018) version of record was NOT checked (access not attempted). The live text keeps only a weaker Question on transposition preserving g- and G-equivalence. Not pursued (zero credit). Note: a K-theoretic duality involution sending G_lambda to G_lambda\' may make it routine anyway; that was not checked.',
   receipts=rc('abs-1609.06171', 'ep-1609.06171')),
 334133: dict(outcome='parked_open_deep', credit='none', review_depth='abstract, v5 / J. Symbolic Comput. 91 (2019) version of record',
   detail='Dimca-Sticlaru bounded stabilisation conjecture (q0 <= 3d+1) for pole-order spectral sequences of plane curves: the authors note they cannot even check it on a specific example. It needs computer algebra (Singular) beyond this lane, and there is no Lean route. Parked.',
   receipts=rc('abs-1609.06818')),
}
assert set(D) == set(res['ids']) and len(D) == 20
out = {}
for i in res['ids']:
    e = ext[str(i)]
    out[str(i)] = dict(mathdb_id=i, title=e['title'], source_url=e['source_url'], provenance=e['provenance'], **D[i])
(L / 'results.json').write_text(json.dumps(out, indent=1, ensure_ascii=False) + '\n')
print('wrote', len(out), 'entries')
