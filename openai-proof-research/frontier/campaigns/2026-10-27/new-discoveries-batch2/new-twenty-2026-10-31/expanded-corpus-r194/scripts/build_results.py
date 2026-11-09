import json, pathlib, hashlib
L=pathlib.Path(__file__).resolve().parents[1]
ex=json.loads((L/'extracted.json').read_text())
rec={}
for r in json.loads((L/'outputs/fetch-receipts.json').read_text()):
    if 'sha256' in r: rec[r['id']]={k:r.get(k) for k in ('url','status','sha256','bytes','file','utc')}
def R(*ids): return [dict(id=i,**rec[i]) for i in ids if i in rec]
D={
'323194':dict(outcome='parked_deep_nonfinite',depth='literal statement; source abstract (Ara, arXiv:1203.2815 v1/v2); status search',
 note='Injectivity conjecture for finitely separated graph C*-algebras (Ara-Goodearl/Ara-Exel programme). Operator-algebraic, infinite objects, no finite certificate route; secondary sources describe the monoid correspondence as still open. Disposed quickly per brief.',receipts=R('abs-323194')),
'323220':dict(outcome='parked_no_finite_route',depth='source section 3.1 read (eqs 3.1-3.4, Conjectures 3.1-3.3, arXiv:1203.4419 v1 only version; JCTA 120 (2013)); citing-work searches (no proof found)',
 note='Conjecture 3.2 (alpha-beta decomposition) is a structural statement about the alpha-triangle, which is defined from the A-matrix of all higher-dimensional partitions (a_{m+r+1,r} = sum_z alpha_{m,z} r^{2m-z}/(2m)!!). Each new alpha row m needs a_{n,r} for n up to 3m+1 in dimension 2m; the author computed partitions only to n <= 25 with Bratley-McKay code. No capped-Python route beyond the authors verified rows; a proof would need a full cluster-expansion theory of higher-dimensional partitions with heavy Lean cost. Parked.',receipts=R('abs-323220','ar5iv-1203.4419')),
'323656':dict(outcome='known_refuted',depth='source Conjecture 2.5 read (arXiv:1206.2717, JCTA 120 (2013)); Murphy arXiv:1709.10438 v2 introduction and Theorem 2 read',
 note='The record is Conjecture 2.5 of Schwartz-Solymosi-de Zeeuw, attributed there to the second author (Solymosi), not to Elekes as the MathDB title says. Murphy, Upper and lower bounds for rich lines in grids (arXiv:1709.10438), states it as Conjecture 1 ([14, Conjecture 3.10]: at most C(alpha) alpha-rich lines in general position, alpha-rich = alpha N points) and disproves it: RLGP(Q,N,alpha) >= C(1-alpha) log N / log log N. Known refutation; zero credit.',receipts=R('abs-323656','ar5iv-1206.2717','abs-1709.10438','ar5iv-1709.10438')),
'323845':dict(outcome='parked_deep_nonfinite',depth='literal statement; source abstract (Huang, arXiv:1207.5969)',
 note='ACGT projective-bundle extremal metric conjecture; Kahler geometry, source gives only a proof conditional on bounded Calabi-flow curvature. No finite route; disposed quickly.',receipts=R('abs-323845')),
'323879':dict(outcome='known_proved',depth='source abstract (Dukes-Le Borgne arXiv:1208.0024 v1/v2); ADDHL arXiv:1301.4803 abstract',
 note='Aval, D Adderio, Dukes, Hicks, Le Borgne (arXiv:1301.4803; JCTA 2014) show (area,bounce) and (area,dinv) give the same q,t-Narayana polynomial introduced in arXiv:1208.0024 and prove its main conjectures: symmetric in q and t, and in m and n, via the diagonal-harmonics interpretation. Known; zero credit.',receipts=R('abs-323879','abs-1301.4803')),
'323949':dict(outcome='known_proved_by_source',depth='source abstract (Balkova-Pelantova-Starosta arXiv:1208.2505, TCS 475 (2013))',
 note='The source is titled Proof of Brlek-Reutenauer conjecture and proves the general version. Known; zero credit.',receipts=R('abs-323949')),
'324150':dict(outcome='known_proved',depth='source abstract all versions (Matsuda arXiv:1209.4300 v1-v3); LaClair-McCullough arXiv:2601.15403 v2 abstract',
 note='LaClair and McCullough, F-Purity of Binomial Edge Ideals (arXiv:2601.15403; J. London Math. Soc. 113 (2026) e70474), confirm Matsuda first conjecture: in characteristic 2, S/J_G is F-pure iff G is weakly closed. Known; zero credit.',receipts=R('abs-324150','abs-2601.15403')),
'324252':dict(outcome='parked_after_structured_search',depth='full source read (arXiv:1210.2543 v1, Conjecture 6.1, Theorems 3.1, 4.1, 5.1); Miskolc Math. Notes 14 (2013) 845-850 abstract; citing searches; GitHub/Lean Pool screen',
 note='H(G) >= r(G) for connected non-even-path G. Source proves trees (H > r + 1/15), unicyclic (equality iff even cycle), H >= r - 31(k-1)/105. Since H <= R, the conjecture implies the Caporossi-Hansen conjecture R >= r and Fajtlowicz 1988 R >= r - 1 (still open), so a full proof is flagship-hard. Structured search: (1) all 995 connected graphs on <= 7 vertices: min H - r over non-even-paths is 0, attained only by C4 and C6 (min 1/15 for odd n); (2) exact reduction of the path-like regime (long paths with gadgets) to a gadget excess: counterexample iff some gadget has excess < 1/6; all rooted end gadgets and two-terminal inline/side gadgets on <= 7 vertices have excess >= 7/30 (the source pendant-near-end value), cyclic gadgets >= 1/3; (3) simulated-annealing local search, 2215 restarts, up to 22 vertices: best is C4 with H - r = 0. No counterexample; no proof route; parked.',receipts=R('abs-324252','ar5iv-1210.2543','miskolc-662','gh-zavbia-readme'),
 coverage=dict(exhaustive_connected_graphs_max_n=7,gadget_max_vertices=7,min_gadget_excess='7/30',threshold='1/6',local_search='seed 1, 85 s, n <= 22')),
'324673':dict(outcome='parked_deep_nonfinite',depth='literal statement; source abstract (Solymosi arXiv:1212.3365)',
 note='Bounded APs in g(Q); the author states it would follow from the Uniformity Conjecture and could not prove it. Arithmetic-geometric, no finite certificate route.',receipts=R('abs-324673')),
'346734':dict(outcome='known_proved',depth='source abstract (Younsi-Lacasse arXiv:2006.01387 v1/v2); citing searches',
 note='Lacasse identity xi_2(m) = xi(m) + m was proved by Younsi (arXiv:1209.0824; Electron. J. Combin. 20(2) (2013) P11) and again in the source itself; further proofs by Sun, Prodinger, Chen-Peng-Yang. Known; zero credit.',receipts=R('abs-346734')),
'381117':dict(outcome='known_refuted',depth='literal statement; Bodirsky HDR abstract (arXiv:1201.0856 v1-v10); Evans-Hubicka-Nesetril arXiv:1801.01165 v5 abstract',
 note='Evans, Hubicka, Nesetril, Automorphism groups and Ramsey properties of sparse graphs (arXiv:1801.01165; Proc. LMS 2019): Hrushovski omega-categorical sparse graph has no omega-categorical expansion with extremely amenable automorphism group, i.e. its closed oligomorphic automorphism group has no closed oligomorphic extremely amenable subgroup. This refutes the record as stated (the finite-language Bodirsky-Pinsker-Tsankov question is a different, still open, variant). Known; zero credit.',receipts=R('abs-381117','abs-1801.01165')),
'372920':dict(outcome='parked_after_exhaustive_search',depth='source read (Hafner arXiv:2602.02448 v1, the only version: Sections 2-3, 5; Definitions 3.1-3.4, Theorem 5.1, Conjecture 5.2); Kohnert-adjacent family warning noted',
 note='Conjecture 5.2: for every almost vexillary w there is A in D(w) with supp(G_w) = weights of SBD(D(w), {}, A). Implemented isobaric divided differences (validated against G_2143) and the bubbling/K-bubbling moves; validated on all of S4 and all 103 vexillary w in S5 (theorem cases). Exhaustive: every almost vexillary non-vexillary w in S5 (16), S6 (179) and S7 (1765) admits such an A, already with at most one square per column; no state-space caps hit. S8: hash-sampled 171 of 16545 targets across all lengths, all pass. No counterexample; a proof would extend the source vexillary machinery (and sits next to the Kohnert-poset family). Parked.',receipts=R('abs-372920','html-2602.02448v1'),
 coverage=dict(S5=16,S6=179,S7=1765,S8_sampled=171,S8_total_targets=16545)),
'373454':dict(outcome='parked_deep_nonfinite',depth='literal statement; source abstract (Dalla Riva arXiv:2603.05703 v1)',
 note='Generic full SO(d) holonomy for Laplacian dynamics, d >= 3; differential-geometric transversality statement, not finite. Disposed quickly.',receipts=R('abs-373454')),
'373969':dict(outcome='parked_deep_nonfinite',depth='literal statement; source abstract (Veeranonchai arXiv:2603.29938 v1/v2)',
 note='Gerke-Marciniszyn-Steger sparse counting lemma, general H; the source proves only H = K4 and calls the general case widely open. Asymptotic probabilistic statement; no finite route.',receipts=R('abs-373969')),
'374530':dict(outcome='parked_deep_nonfinite',depth='literal statement; source abstract (Kunisky arXiv:2605.02023 v1)',
 note='Stochastic domination of Gaussian minima by the cosine covariance; the source proves it only conditionally on a volumetric zone conjecture. Analytic; no finite certificate.',receipts=R('abs-374530')),
'374917':dict(outcome='parked_deep_nonfinite',depth='source v2 (arXiv:2605.24751v2, 2026-09-19) introduction read: Question 1.2 still stated as open',
 note='Infinite partition-regularity (Hindman-type sums and products of block sums); ultrafilter methods; no finite certificate route.',receipts=R('abs-374917','html-2605.24751v2')),
'374944':dict(outcome='source_refuted',depth='all three arXiv versions checked; v3 (2026-10-21) abstract and Section 1 read (Conjectures 1.1, 1.2)',
 note='Riener-Shapiro arXiv:2605.25743 v3 prove the record (Conjecture 1.2, square-graph cone) fails for k = n - 4 for all n >= 23, smallest failing pair (n,k) = (23,19), certified by an explicit linear functional. MathDB copies an earlier version. Known; zero credit.',receipts=R('abs-374944','html-2605.25743v3')),
'375060':dict(outcome='source_refuted',depth='source abstract (St. Dizier arXiv:2606.02257 v1, the only version)',
 note='The source is titled Counterexamples to Robichaux conjecture for Grothendieck polynomials and provides counterexamples to Robichaux ghost K-Kohnert rule (it proves both rules for 1432-avoiding permutations). Known; zero credit; Kohnert family.',receipts=R('abs-375060')),
'375072':dict(outcome='parked_deep_nonfinite',depth='source v1 and v2 (2026-10-28) Section 11.3 read (Definition 11.12, Proposition 11.15, Example, Conjecture 11.18)',
 note='Combinatorial criterion for kinematic support is still Conjecture 11.18 in v2; necessity is proved in the source (Propositions 11.10, 11.15); sufficiency is a dimension statement about restricted moduli spaces of origami crease patterns. No finite route in this lane.',receipts=R('abs-375072','html-2606.03439v1','html-2606.03439v2')),
'375229':dict(outcome='parked_open_famous',depth='source abstract and HTML v1 (arXiv:2606.11494, the only version); ledger exclusion of sibling 375232 read; status searches',
 note='General matroid EF1 conjecture with common additive valuation (open; known for base-orderable, regular, laminar/transversal cases; follows from Gabow conjecture; Akrami-Raj-Vegh SODA 2026 equitability gives only tri-valued common valuations). Sibling 375232 (Conjecture 4 of the same source) was excluded as a realisation of the cited Dror-Feldman-Segal-Halevi obstruction. A counterexample would require quantifying over all real valuations on a non-base-orderable non-regular matroid; no tractable mechanism. Parked.',receipts=R('abs-375229','html-2606.11494v1')),
}
assert set(D)==set(ex)==set(map(str,json.loads((L/'reservation.json').read_text())['ids']))
out={}
for k in sorted(D,key=int):
    out[k]=dict(mathdb_id=int(k),title=ex[k]['title'],source_url=ex[k]['source_url'],provenance=ex[k]['provenance'],
                statement_literal=ex[k]['statement'],review_depth=D[k]['depth'],outcome=D[k]['outcome'],disposition=D[k]['note'],
                receipts=D[k]['receipts'],**({'coverage':D[k]['coverage']} if 'coverage' in D[k] else {}),
                candidate=False,credit_claim='none')
(L/'results.json').write_text(json.dumps(out,indent=1,ensure_ascii=False)+'\n')
from collections import Counter
print(len(out),Counter(v['outcome'] for v in out.values()))
