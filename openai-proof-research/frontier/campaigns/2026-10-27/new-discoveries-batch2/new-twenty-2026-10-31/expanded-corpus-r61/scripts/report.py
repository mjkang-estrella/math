"""Build results.json (exactly 40 ID-keyed entries) from extracted.json plus lane dispositions."""
import json, pathlib, datetime, hashlib
D = pathlib.Path(__file__).resolve().parents[1]
x = json.loads((D / 'extracted.json').read_text())
res = json.loads((D / 'reservation.json').read_text())
ids = [str(i) for i in res['ids']]
assert len(ids) == 40 and set(ids) == set(x)

S = 'literal statement read; arXiv HTML fetched with receipt; primary body not reviewed'
H = 'campaign-history grep by ID and title: no prior disposition (numeric hits are hash-substring collisions or the current ledger reservation)'
PARK = 'PARKED: no tractable exact full-scope mechanism identified in this pass'

D_ = {
 '366272': (S, PARK, 'Spectral extremal problem over all trees of odd diameter; MathDB paraphrase leaves C^- and AS(r,b,c) undefined (source gap); no exact finite route.'),
 '366290': (S, PARK, 'Payne-Wood Theta(s^2) planar Ramsey order: famous asymptotic problem.'),
 '366361': (S, PARK, 'Infinite family of Eisenstein/Witten zeta identities for all n; verified only computationally in source; no proof route here. Prior jacobi-lane hits are hash collisions.'),
 '366371': ('primary body read: Definition 1.1, (7.1)-(7.3), Definition 7.1, Prop 7.2, Prop 7.3, Thm 7.5, Conjecture 7.4; arXiv abs lists v1 only',
            'CANDIDATE REFUTATION with full Lean endpoint (zero credit until review/root acceptance)',
            'Six-point tie-free ordinal space; identity enumeration has the majorization property for all k (finite reduction proved in Lean); not line-embeddable (5-term Farkas certificate). n=5 diagnostic: no counterexample. See PROOF-366371.md, formal/OrdinalLine.lean.'),
 '366376': (S, PARK, 'Asymptotic growth constants for minimizer counts; analytic, no exact finite route.'),
 '366412': (S, PARK, 'Planar uniquely restricted chromatic index bound; no small-counterexample mechanism (bound is loose for small graphs).'),
 '366424': (S, PARK, 'Chernikov field conjecture (model theory); research-level.'),
 '366434': (S, PARK, 'Behzad-Chartrand-Wall (Caccetta-Haggkvist case); famous.'),
 '366438': ('campaign history read: lanes/root-supertoken-exclusion-r1/DECISION.md and EXCLUSION.json',
            'EXCLUDED (inherited): old root disposition retained',
            'Prior root decision: valid refutation but routine adaptation of Bailey-Cameron path-block construction; zero credit. Route stopped per task rule.'),
 '366458': ('campaign history read: lanes/sol-fresh-source-discovery-r186 discovery note (2026-10-25 algebra lane sigma-fusion-366458 with Lean)',
            'EXCLUDED (inherited): already solved in an earlier campaign',
            'All four fusion properties were proved and formalized earlier (SigmaFusion.lean); duplicate MathDB 318649 noted there. Not new; route stopped.'),
 '366485': (S, 'EXCLUDED: definition, not a resolvable claim', 'Introduces the variational quantity d_sep^min; no assertion to prove or refute.'),
 '366489': ('primary bodies read: arXiv:2501.01295 (full, Props 2-7, Cor 1-2, Table 1); arXiv:2503.01343 (Conjecture 1 and Theorem 1 statement; proof body not audited)',
            'EXCLUDED: known (published proof)',
            'H. Gao, arXiv:2503.01343 (AIMS Press version restricts m < ceil(n/2)) proves the Furtula-Oz extremal structure; with Saber et al. Cor 2 (3n/10 < k < 4n/10 for n>=11) and Furtula-Oz n<=10 data the k-range follows. No new credit possible.'),
 '366500': (S, PARK, 'Rognes equivariant equivalence; homotopy theory.'),
 '366514': ('primary body read: arXiv:2501.02563 introduction, Conjecture 1.5, Definition 2.1, Theorem 2.2',
            PARK,
            'Diagnostics: exhaustive n=6 labeled graphs and closed vertex multiplications of all base graphs on <=5 vertices with weights 1-3 found no non-H_{a,b} graph with lambda_3 = n/3 - 1 (signature check; outputs via logs/lambda3.log). A proof needs spectral structure theory; Nikiforov c_3=1/3 question itself is open.'),
 '366572': (S, PARK, 'Traub basin topology; complex dynamics.'),
 '366603': ('source context read (arXiv:2501.05830 Section 3 conjectures)', PARK, 'Infinite Fibonacci-index identities; authors note automatic (Walnut) verification fails because A(F_n) not eventually constant.'),
 '366625': (S, 'EXCLUDED: known (resolved by the cited source)', 'MathDB text itself states the source paper proves the Wang-Wu inequality.'),
 '366627': (S, PARK, 'fasd(5,3)=3: supremum over weighted orgraphs; no finite certificate route.'),
 '366682': (S, PARK, 'Asymptotic distance bounds for M_3-codes, large-n ranges only.'),
 '366695': (S, PARK, 'FB(s,2^{s-1}) = 2^s - 1 for all s; open coding problem, no full-scope route.'),
 '366705': (S, PARK, 'Fiamcik-Alon acyclic edge colouring conjecture; famous.'),
 '366723': (S, PARK, 'Havet-Reed-Wood-Stein tree embedding; famous.'),
 '366752': (S, PARK, 'Bipartite gluing extremal-number conjecture; equivalent to a Zarankiewicz statement per source.'),
 '366775': (S, PARK, 'Requires SDP certificates for an infinite family of SRGs.'),
 '366807': (S, PARK, 'Markov sail duality identities for all Markov numbers.'),
 '366808': (S, PARK, 'Location-of-4 conjecture for Markov sails, all continued fractions.'),
 '366816': ('source context read (arXiv:2501.15170 Section 5, Conjecture 5.1)', 'EXCLUDED: claimed proof in source / wording', 'Source states "A proof of this conjecture has been claimed in [9]"; MathDB text also conflates the Lemma direction with the conjecture.'),
 '366834': ('primary bodies read: survey arXiv:2501.16144v4 Section 1 definitions, Section 4, Conjecture 39, Section 6 question 2(b); Estrugo-Pastine arXiv:2009.00732 (full); original DAM 2024 paper unread (paywall, no arXiv version)',
            'CANDIDATE REFUTATION with full Lean endpoint (zero credit until review/root acceptance)',
            '11-vertex caterpillar, r=6 < alpha=7: maximum 6-centres are exactly two leaves whose neighbour has degree 3 < Delta=4; refutes universal and existential readings. Minimum order among strong failures (n<=11 exhaustive diagnostic). See PROOF-366834.md, formal/CaterpillarCenter.lean.'),
 '366919': ('source context read (arXiv:2502.00777 Section 1-2)', PARK, 'Ancestor conjecture for all finite Coxeter groups (infinite families A_n, B_n, D_n); small-type checks would not give full scope.'),
 '366988': (S, PARK, 'Bose-Burton basis-number extremality for all prime powers t and ranks.'),
 '366991': (S, PARK, 'Caro-Roditty zero-sum tree embedding for all m,k.'),
 '367008': (S, PARK, 'Realization-count ratio for all E1a extensions; no finite route, Lean infeasible.'),
 '367021': (S, PARK, 'Existence of non-admissible weight with BMOA_v non-invariance; analytic construction.'),
 '367055': (S, PARK, 'Maximal index of smooth Calabi-Yau n-folds; algebraic geometry.'),
 '367056': (S, PARK, 'Maximal Betti sum of smooth Calabi-Yau n-folds; algebraic geometry.'),
 '367075': ('source context read (arXiv:2502.07933 introduction, Conjecture 4)', PARK, 'Exhaustive diagnostic: all 4,165 labeled digraphs on <=4 vertices (2-cycles allowed) and all 59,049 labeled oriented graphs on 5 vertices admit weakly locally irregular 2-colourings (outputs/lir-small.txt); no counterexample.'),
 '367083': ('primary body read: arXiv:2502.08128v2 abstract, Section 1, Section 7 (Conjectures 7.1, 7.2, Example 1, subsequent-work note)', 'EXCLUDED: known', 'Source v2 states Conjecture 7.1 was proven independently by Saengrungkongka [16]; literal t=1 case also fails by the stars-plus-edge family noted in the source (endpoint issue).'),
 '367091': (S, PARK, 'Asymptotic diameter bound with O(1); no exact finite route.'),
 '367101': (S, PARK, 'Rational curves on projective IHS manifolds; algebraic geometry.'),
 '367107': (S, PARK, 'delta_VC = delta_B for all H; open extremal problem.'),
}
assert set(D_) == set(ids)
out = {}
for i in ids:
    depth, outcome, notes = D_[i]
    o = x[i]
    out[i] = dict(mathdb_id=int(i), title=o['title'], source_url=o['source_url'],
                  provenance=o['provenance'], history_check=H if i not in ('366438', '366458') else 'prior campaign disposition found and retained',
                  review_depth=depth, outcome=outcome, notes=notes,
                  source_fetch_receipt=f"sources/{o['source_url'].rsplit('/', 1)[-1]}.html.receipt.json")
(D / 'results.json').write_text(json.dumps(dict(
    utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    lane='expanded-corpus-r61', counts_changed=False, accepted_count_unchanged='6/20 beyond 39 prior',
    candidates=['366834', '366371'], results=out), indent=2, ensure_ascii=False) + '\n')
print(len(out), 'entries;', sum('CANDIDATE' in v['outcome'] for v in out.values()), 'candidates')
