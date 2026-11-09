# Build results.json for lane-1: one entry per reserved MathDB ID. Record metadata is read (not copied wholesale) from
# the immutable r628 literal-records.json; dispositions below are this lane's evidence-backed findings.
import json, hashlib
REC = '../../lanes/claude-mathdb-primary-qualified-breadth-r628/literal-records.json'
HAY = 'lanes/sol-mathdb-primary-qualified-breadth-r576/1809.07200.txt (sha256 451cd756...a50d26 of arXiv HTML 1809.07200v2 fetched 2026-10-31T15:32:45Z)'
H = 'Hayman-Lingham, Research Problems in Function Theory, arXiv:1809.07200v2 (21 Sep 2018), cached text ' + HAY
EG = 'Egres Open page via Wayback snapshot (live oldlemon.cs.elte.hu unreachable 2026-11-01T03:0xZ, curl code 000); sources/egres/'
CO = 'Cooper, Combinatorial Problems I Like, https://people.math.sc.edu/cooper/combprob.html fetched 2026-11-01T03:25:25Z sha256 ba547f05...cf501e5a; statement matches MathDB'
PR = 'publicly_resolved_or_answered'; OF = 'open_hard_no_tractable_full_route'; OE = 'open_ended_or_nonexact_question'; IA = 'investigated_no_full_route'
D = {
 387469: (PR, 'arXiv:1911.12255 (Cheriha-Gati-Kostov, 26 Nov 2019; sources/prior/arxiv-1911.12255-abs.html sha256 acbf436c...) gives the degree-9 counterexample: sign pattern (+,-,-,-,-,+,+,+,+,-) with pair (1,6) is non-realizable, so Conjecture 7 is refuted. Kostov later gave a degree-11 one.', 'Shapiro arXiv:1503.05295, cached as lanes/sol-mathdb-primary-qualified-breadth-r576/1503.05295.txt'),
 387479: (PR, 'Update 1.3: proved completely by Drasin; Eremenko gave a simpler proof of a stronger result.', H),
 387486: (PR, 'Update 1.11: Kotman showed the answer is no.', H),
 387528: (PR, "Update 2.17: Kjellberg disproved the 1/4 conjecture, showing 0.24<A<0.248. The exact best A remains an unspecified-constant determination with no tractable route.", H),
 387535: (PR, 'Update 2.24: sin(z^2) has all zeros and ones on the real and imaginary axes (Al-Katifi, Ozawa), so the answer is yes.', H),
 387586: (OF, "Update 2.77: 'uniformly' was added, and the problem is equivalent to 2.87 (bounded-orbit wandering domains). No progress reported; famous open problem in transcendental dynamics. No finite or formalizable mechanism found.", H),
 387607: (PR, "Update 3.7: Dahlberg obtained the subharmonic generalization of Govorov's theorem (Problem 1.17).", H),
 387641: (OF, 'Update 4.7: open (Mo attempt has gaps; Eremenko-Hayman length bound). Sharp Cartan constant 2: no tractable route.', H),
 387649: (PR, "Answered yes by Kashin (1987) and Konyagin (1994): min over |z|=1 of |P| < n^{-1/2+eps} for all but o(2^n) +-1 polynomials (see also Konyagin-Schlag 1999, Cook-Nguyen arXiv:2101.07203). The book's 'no progress' update is stale.", H),
 387675: (PR, 'MathDB statement is a fragment of Problem 5.14 (a normality question). Update 5.14 (Eremenko): equivalent to Problem 5.13 with n>=1, which Update 5.13 records as solved by Pang together with Bergweiler-Eremenko.', H),
 387693: (OE, "Asks what norm convergence 'means geometrically': no exact true/false statement.", H),
 387726: (PR, 'Update 5.66: Stephenson answered negatively (inner function with finite fibres on a dense set; Frostman shifts give Blaschke products).', H),
 387731: (OF, 'Update 5.71: no progress. Murai gap-series deficiency question; no finite mechanism found.', H),
 387734: (OE, "'Characterise' question with no single exact claim.", H),
 387741: (PR, "Update 6.2: K_0=1 by de Branges' theorem.", H),
 387744: (OE, "'Orders of magnitude' question with no exact claim (Springer's conjecture is a separate statement; Kubota proved n=3,4,5).", H),
 387754: (PR, 'Update 6.16: counterexample to this Marx-conjecture version given by Hummel.', H),
 387771: (OE, "'Same questions as 6.32' (what can be said about coefficients; find a sup): open-ended.", H),
 387774: (PR, "Open-ended ('what can be said'); the natural sharp bounds follow from de Branges (Aharonov, Grinshpan, Hayman-Hummel, Update 6.36).", H),
 387776: (OF, 'Update 6.38: Milin partial (beta-weighted bound with 50). Exact beta=(sqrt2-1)^2 question open; no tractable route.', H),
 387781: (OF, 'Update 6.43: Hayman partial counterexample to a stronger version; general problem open. No route.', H),
 387787: (OE, 'Extreme-point descriptions for four classes: open-ended characterization.', H),
 387820: (OE, "'Characterise' sequences: Overholt partial. No exact claim.", H),
 387858: (OF, 'Asks for the best constant c. Equals Erdos #519 (erdosproblems.com/519, snapshot sha256 debb48c9...): Atkinson 1/6 (the record says 1/3), Biro >1/2, R_n<0.69368 for large n. Exact optimum is open; no tractable route.', H),
 387873: (PR, 'Erdos #987 (= Hayman 7.21): erdosproblems.com/987 (snapshot sha256 bee2f033...) records a construction with A_k << (k log k)^{1/2}, so A_l=o(l) is possible [APSSV26b]. Publicly answered.', H),
 387880: (PR, 'arXiv:2608.04540 (Guo-Xiao, submitted 5 Aug 2026; snapshot sha256 d13c52d1...): for continuous f, o(r^2) circle integrals at every point imply holomorphic, so both (i) and (ii) are answered yes. Later independent public answer; not ours.', H),
 387898: (PR, 'Update 7.46: proved by Fuchs; generalized by Gehring-Hayman-Hinkkanen.', H),
 387906: (IA, 'See SUMMARY section Rippon. Open per Update 7.54 (no progress). Exact computation extends prior lane evidence; structural reduction to a Yoccoz-type Koenigs function; no full proof route.', H),
 387920: (OF, 'Update 7.68: no progress. A.e. density of partial sums of Hadamard-gap cosine sums: deep probabilistic and lacunary question, no finite mechanism.', H),
 387943: (OE, "'Describe geometrically' a set: no exact claim.", H),
 388036: (IA, 'Open (Egres: even k=l=2 open). Exhaustive n<=5 and random n=6 search for k=l=2 found no counterexample (diagnostic only). No proof route.', EG),
 388057: (OF, "Thomassen's conjecture (Egres: false for k=2, open for k=3; decision version NP-complete). No route.", EG),
 388059: (OF, 'Itai-Zehavi conjecture: known k<=4 (Gopalan-Ramasubramanian k=3, Hoyer-Thomas k=4); open k>=5. No route.', EG),
 388072: (OF, 'Independent trees conjecture: known k<=4 and planar; open k>=5. No route.', EG),
 388087: (OF, "Kiraly's conjecture: reduces to minimally nonideal clutters, and Pap proved the cyclic-core case. I checked by hand that degenerate projective planes J_t admit (p,q). Non-cyclic-core mni catalog (Lutolf-Margot) not accessed: access gap.", EG),
 388092: (IA, 'Correa-Goemans question (Egres; Feige-Singh Conjecture 1.4). No counterexample in about 3.44M random and targeted decided instances (DFS, plus exact MILP for budget cases) or 611,294,019 exhaustive small-size graph-by-pattern instances (up to 4x5 simple and 3x3 multiplicity <=2, k=3,4). Diagnostic only. Universal circle-labelling strengthening refuted on small graphs. No proof found. See SUMMARY.', EG),
 388097: (OF, 'Polynomial recognition of Seymour graphs: co-NP characterization (Ageev-Kostochka-Szigeti) and excluded-minor characterization (Ageev-Benchetrit-Sebo-Szigeti) known; complexity open. No route.', EG),
 388113: (OF, 'Aharoni-Berger conjecture: fractional version and factor-2 approximation known; open. No route.', EG),
 388119: (OF, 'Graham non-equilateral triangle 3-colouring (Euclidean Ramsey): open in general. No route.', CO),
 388126: (OF, 'Regular tetrahedra sharing a vertex (20<=N<=22): no resolution found in searches (2026 arXiv:2604.21451 still frames it as a question). Continuous-geometry certificate; no route.', CO),
 388134: (OF, 'Erdos hypercube C4 Turan density (conjectured 1/2): open (best upper bounds about 0.6068). No route.', CO),
 388146: (OE, "Open-ended 'what is the expected number' over all sigma, tau. Bona has partial results.", CO),
 388158: (OF, '1/3-2/3 conjecture: famous open. No route.', CO),
 388164: (OF, 'Equidistribution of (3/2)^n mod 1: famous open. No route.', CO),
 388166: (OF, 'Niederreiter bounded-in-average multipliers: Zaremba-type, known only for density-one sets, special moduli, or log-type averages (Larcher). No route.', CO),
 388168: (OF, 'Erdos-Turan additive basis conjecture: famous open. No route.', CO),
 388171: (OE, "Asks 'how large can R be' (exact supremum): bounds 2.0649<R<3.9998 (Levine-O'Sullivan, Abbott, Zhang). Determining R is open. No route.", CO),
 388172: (OF, 'No-three-in-line (Guy-Kelly conjecture): open. No route.', CO),
 388175: (OF, 'Rado boundedness conjecture: Fox-Kleitman for 3 variables; open in general. No route.', CO),
 388180: (OE, 'Prime-gap growth (Cramer-type): famous open and partly vague. No route.', CO),
}
R = json.load(open(REC, encoding='utf-8'))
out = {}
for r in R:
    x = r['record']; i = x['mathdb_id']; disp, ev, src = D[i]
    out[str(i)] = {
        'mathdb_id': i, 'title': x['title'], 'canonical_url': x['canonical_url'], 'source_name': x['source_name'], 'source_url': x['source_url'],
        'mathdb_record_ref': {'file': 'lanes/claude-mathdb-primary-qualified-breadth-r628/literal-records.json', 'file_sha256': '4eba068ba21ac7b6ed22228dc4e1cc5e09601d5ab1eecdec5cba0c6319480ca5',
                              'corpus_chunk': r['chunk'], 'line': r['line'], 'literal_line_sha256': r['literal_line_sha256'], 'statement_utf8_sha256': r['statement_utf8_sha256'],
                              'mathdb_status_field': x['status'], 'solution_count': x['solution_count'], 'lastmod': x['lastmod']},
        'inspection_level': 'primary_source_body' if 'cached text' in src or 'Egres' in src or 'Cooper' in src or 'arXiv' in src else 'metadata_only',
        'primary_source_used': src, 'disposition': disp, 'evidence': ev,
        'candidate_for_credit': False, 'lean_endpoint': None,
    }
assert len(out) == 50
json.dump({'lane': 'lane-1 (new-twenty-2026-10-31; previous_lane claude-mathdb-primary-qualified-breadth-r628)', 'generated_utc': '2026-11-01',
           'accepted_claimed': 0, 'viable_full_scope_candidates': [], 'note': 'No acceptance asserted; no counts incremented. Search results are numerical diagnostics, not proofs.',
           'records': out}, open('results.json', 'w', encoding='utf-8'), indent=1, ensure_ascii=False)
from collections import Counter
print(Counter(v['disposition'] for v in out.values())); print(Counter(v['inspection_level'] for v in out.values()))
