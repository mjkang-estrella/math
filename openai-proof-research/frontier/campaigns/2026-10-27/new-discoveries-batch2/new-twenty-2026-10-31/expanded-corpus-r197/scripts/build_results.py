"""Build results.json (exactly the 20 reserved IDs) from extracted.json, fetch receipts and the
dispositions below."""
import json, pathlib
L = pathlib.Path(__file__).resolve().parents[1]
ext = json.loads((L / 'extracted.json').read_text())
res = json.loads((L / 'reservation.json').read_text())
rec = json.loads((L / 'outputs/fetch-receipts.json').read_text())
byid = {}
for r in rec:
    byid.setdefault(r['id'], r)  # first receipt per id
def receipts(*ids):
    out = []
    for i in ids:
        r = byid.get(i)
        if r: out.append({k: r.get(k) for k in ('id', 'url', 'status', 'sha256', 'bytes', 'file', 'utc', 'error') if r.get(k) is not None})
    return out

D = {
 381851: dict(outcome='parked_after_exhaustive_search_literal_defect_recorded',
   review_depth='full source TeX (arXiv:2212.07706 v1, only version) Sections 2-3 read: definitions, Prop. NC, Lemma m_ij, Lemma no-diag-touching, Theorem SC (conditions i-iii), Conjecture; web/citing search (no later work found)',
   disposition=('Ellison-Jouve-Stone conjecture (switching checkerboards). The printed quantifier fixes (R,C): the left side is vacuous when no pair has difference M, and the fixed-(R,C) "only if" already fails at R=C=(1,1,1,1) with the source\'s own Example 2 matrix M (the unique pair, permutation matrices, is reachable although P_1(M) is a ring): formulation defects, zero credit. '
     'Substantive "if" direction ((i)+(ii) => A->A\', i.e. condition (iii) of Theorem SC unnecessary) tested exhaustively: all 3x3 (512), 4x4 (65,536) and 4x5 (1,048,576; 16 chunks) binary matrices, reachability closure of every class G(R,C); 12,818,863 ordered dominance-comparable pairs (cond (i) <=> 2D prefix-sum dominance); only 112 comparable pairs are unreachable and every one fails (ii). No counterexample. 5x5 (33.5M matrices) exceeds the lane caps; a targeted search over (iii)-violating T was designed but not run.'),
   scripts=['scripts/checker.py', 'scripts/aggregate_checker.py'], outputs=['outputs/checker/summary.json'], rec=('abs-381851', 'src-381851')),
 381931: dict(outcome='parked_deep_computational',
   review_depth='abstract v1-v4 (SIGMA 20 (2024) 016); citing work Antolini-Early arXiv:2411.07293 abstract read',
   disposition='Cachazo-Early-Zhang chirotopal tropical Grassmannian conjecture (rank 3). Antolini-Early (Le Matematiche 2025) prove Trop^chi G(3,n)=Dr^chi(3,n) for n=6,7,8 and show failure for (4,8); n>=9 open. Next case needs polyhedral fan computations over all rank-3 realizable chirotopes on 9 elements (no polymake/solver in this lane). Parked.',
   rec=('abs-381931', 'abs-2411.07293')),
 381982: dict(outcome='parked_infinite_q_series',
   review_depth='source abstract (Dousse-Konan arXiv:2212.12728 v1); CMPP arXiv:2106.06262 and Kanade-Russell-Tsuchioka-Warnaar arXiv:2404.03851 (Selecta 2026) abstracts',
   disposition='Odd-modulus CMPP partition identity for all (k_0..k_n). Source proves the level-1 case; KRTW relate the remaining CMPP families to A_{2n}^{(2)}, D_{n+1}^{(2)} specialisations without (per abstract) a full proof. An infinite product identity; coefficient checks cannot prove it and the authors/KRTW verified it numerically. No finite certificate route; parked (abstract-level status, not body-verified).',
   rec=('abs-381982', 'abs-2404.03851', 'abs-2106.06262')),
 349920: dict(outcome='parked_deep', review_depth='abstract v1-v4 (Fargues-Scholze)',
   disposition='Independence-of-l for the spectral Bernstein centre map (Fargues-Scholze). Deep arithmetic geometry; no finite route. Disposed quickly per brief.', rec=('abs-349920',)),
 350007: dict(outcome='parked_deep_structural', review_depth='abstract (Steiner arXiv:2103.04191 v1)',
   disposition='Aboulker et al. heroic-triple conjecture (oriented star forests + hero). Infinite chi-boundedness statement; refutation needs an infinite family, proof is structural. Near the parked 371680 acyclic-heroes family. Parked; later literature not body-checked.', rec=('abs-350007',)),
 350024: dict(outcome='EXCLUDED_KNOWN', review_depth='source TeX Section 1 read (Lin-Wang-Zhao arXiv:2103.04599): Conjecture 1.1 = Spiro Conjecture 1.2; text states Wang-Zhao proved it',
   disposition='Spiro descent / cyclic-excedance equidistribution. Proved by Wang-Zhao (arXiv:2009.05973, generating functions) and bijectively by the source itself. Same family as 345225 (excluded known in r168).', rec=('abs-350024', 'src-350024')),
 350106: dict(outcome='parked_analytic', review_depth='abstract v1-v2 (Briet-Krejcirik, J. Math. Phys. 2022)',
   disposition='Faber-Krahn analogue for the infinite-mass Dirac operator; analytic spectral geometry (the source itself only treats rectangles, with a gap in v1). Parked.', rec=('abs-350106',)),
 350481: dict(outcome='EXCLUDED_KNOWN', review_depth='Pan arXiv:2104.10346 full TeX; Fang-Li arXiv:2502.10744 abstract v1-v2',
   disposition='Green-Liebeck Conjecture 2.3 (Y_k = S_k x S_{n-k}). Proved by Fang and Li, arXiv:2502.10744 (Feb 2025, v2 Dec 2025). Lane note: via permutation characters (chi^{(n-i,i)} = pi_i - pi_{i-1}) the condition is that x fixes exactly one i-subset for each i<=k, which a two-line induction reduces to the binary cycle-type condition; in any case known.', rec=('abs-350481', 'src-350481', 'abs-2502.10744')),
 350580: dict(outcome='parked_meta_conjecture', review_depth='abstract (Ollis-Pasotti-Pellegrini-Schmitt arXiv:2105.00980 v1)',
   disposition='Growable-realizations conjecture: for each U a finite set of growable realizations covers all but finitely many admissible L. A meta-statement about the method for every U; neither finitely refutable nor provable by bounded computation. Parked.', rec=('abs-350580',)),
 350969: dict(outcome='parked_deep', review_depth='abstract v1-v3 (Schiffler-Serhiyenko; v3 5 Aug 2026 adds condition (Q3))',
   disposition='Geometric model conjecture for syzygies over dimer tree algebras; v3 abstract still proves only the case of chordless cycles of length 3. Deep representation theory; parked.', rec=('abs-350969',)),
 350973: dict(outcome='CANDIDATE_high_credit_risk', candidate=True,
   review_depth='full source TeX read for all definitions used (Def. 1.1, Section 2, Prop. 4.2, skeletal def., Prop. 4.4, Def. 5.3 + Example 5.4, Theorem 5.4 and proof, cutting, Realization Algorithm, Section 9); citing work Cuntz-Holm-Jorgensen arXiv:2603.18975 TeX grepped; web searches; registry screen',
   disposition=('Banaian-Chen Conjecture 9.5 is false. Explicit quotient dissection (Def. 5.3) of the annulus A_{4,3}: regions (a,b)=(0,1),(2,0),(0,2),(2,0) (triangle + three squares), identify the two outer squares R1,R3 (share v0,v2, no shared arc) exactly as in the source Example 5.4; quiddity (1+sqrt2, sqrt2, 2sqrt2, sqrt2), A=({3,4},{4},{4,4},{4}) passes the Prop. 4.2 test, is skeletal, infinite (proved), and m_{0,11} = 31-22 sqrt2 < 0 (exact). '
     'Caveats: the literal first sentence is already contradicted by the source\'s own example (1+sqrt2,1,2,1+sqrt2) (zero at row 5, negative -(sqrt2-1)); the source Theorem 5.4 proof also fails for ({5},{5},{4,5}). Credit risk HIGH (source-internal literal conflict; short modification of printed Example 5.4; REU preprint). See CANDIDATE-350973.md.'),
   scripts=['scripts/frieze.py', 'scripts/quotient.py', 'scripts/exact_frieze.py', 'scripts/infinite_check.py', 'scripts/model_check.py', 'scripts/frieze_one.py'],
   outputs=['outputs/frieze/exact-quotient-example.json', 'outputs/frieze/infinite-check.json', 'outputs/frieze/quotient-n5-m4-r5-p1.json', 'outputs/frieze/model-check-example54.json', 'outputs/frieze/source-example-nonskeletal.json', 'outputs/frieze/n4-p6-m2.json', 'outputs/frieze/n3-p10-m2.json'],
   rec=('abs-350973', 'src-350973', 'abs-2603.18975', 'src-2603.18975')),
 351924: dict(outcome='parked_analytic', review_depth='abstract (Manners arXiv:2109.05731 v1)',
   disposition='Asymmetric true-complexity bound provable by iterated Cauchy-Schwarz; higher-order Fourier analysis, no finite certificate. Parked.', rec=('abs-351924',)),
 353037: dict(outcome='parked_deep', review_depth='abstract v1-v2 (Borot-Charbonnier-Garcia-Failde-Leid-Shadrin)',
   disposition='Functional relations for topological recursion under x<->y symplectic exchange. Deep; plausibly addressed by later x-y swap work of Alexandrov-Bychkov-Dunin-Barkowski-Kazarian-Shadrin (unverified lead, not read). No finite route; parked.', rec=('abs-353037',)),
 345116: dict(outcome='parked_no_finite_certificate', review_depth='abstract v1-v2 (Martin, scaffolds)',
   disposition='Duality conjecture for planar scaffold equations: hypothesis and conclusion quantify over all association schemes with d>=delta classes; a refutation needs a universally valid implication plus a scheme where the dual fails; no bounded certificate. Parked.', rec=('abs-345116',)),
 345190: dict(outcome='parked_asymptotic_route_recorded', review_depth='full source TeX (McDiarmid arXiv:2001.05256 v2, 4 pages) read; web search for later work (none found)',
   disposition=('McDiarmid Conjecture 3 (bounded E[frag] for each bridge-addable decomposable class, unlabelled). Pairs with the parked 345188. The source\'s awkward example needs a different class for each k. Lane idea (not proved): a single class whose 2-edge-connected pieces are vertex-transitive (Cayley) graphs of super-sparse sizes k_i with per-vertex richness increasing level by level makes two-piece graphs dominate at n=2k_i, with P(disconnected) about 1/2, so E[frag] is about k_i/2 and unbounded. '
     'A rigorous proof needs counting isomorphism classes of Cayley graphs; asymptotic, no finite certificate, Lean-infeasible. Parked; recorded for root.'),
   rec=('abs-345190', 'src-345190')),
 345617: dict(outcome='parked_analytic', review_depth='abstract v1-v3 (David-Schul)',
   disposition='Tree-factorization conjecture for Lipschitz maps with small (2,1)-mapping content; quantitative metric geometry; parked.', rec=('abs-345617',)),
 345654: dict(outcome='parked_after_extended_verification',
   review_depth='full source TeX Section 5 (Burstein-Jones arXiv:2002.12189 v4 = DMTCS 2021) read incl. tables n=5,6,7; citing works arXiv:2610.01077 and arXiv:2610.30975 abstracts',
   disposition=('Burstein-Jones dominance Conjecture 5.3 (refinement of 2143~3421 on Dumont-1). The plain Wilf-equivalence was proved in Oct 2026 (Dong-Liu-Zhao arXiv:2610.01077; Zhang-Zhao arXiv:2610.30975, descent-top/ascent-top preserving bijections); neither abstract claims the (2-31)/(13-2) dominance. '
     'Exact enumerator (incremental 2143/3421 avoidance, vincular counts) cross-checked against brute force at n=4 and reproduces the source tables at n=7 exactly; extended to n=8 (168,503 permutations each side): dominance holds, tail slack 3,12,38,... n=9 exceeds the per-call cap (first entries 1,2 alone > 100 s). No counterexample; parked.'),
   scripts=['scripts/dumont.py', 'scripts/dominance.py'], outputs=['outputs/dumont/dominance-n8.txt', 'outputs/dumont/fast-n7.json'], rec=('abs-345654', 'src-345654', 'abs-2610.01077', 'abs-2610.30975')),
 345968: dict(outcome='parked_hard_finite', review_depth='abstract v1-v3 (Beierle-Brinkmann-Leander, IEEE TIT 2021)',
   disposition='Every APN function has a nontrivial automorphism (and APN permutations a CCZ-representative with nontrivial LE-automorphism). Quadratic APN functions always have translation automorphisms; a counterexample would be a new non-quadratic APN class; classification is complete only for n<=5. Parked (Lean Pool APN project concerns Kasami functions, unrelated).', rec=('abs-345968',)),
 346025: dict(outcome='parked_family', review_depth='abstract (Zhao arXiv:2003.14006 v1); r161 record of sibling 346023 (parked after bounded search)',
   disposition='Zhao local characterization conjecture for multiplier sets / cyclic direct factors; known for k<=2; same source family as the parked 346023 (r161 bounded search, no counterexample). Not repeated; parked.', rec=('abs-346025', 'src-346025')),
 346486: dict(outcome='EXCLUDED_KNOWN', review_depth='abstract (Lin-Ma-Zhang arXiv:2005.06689 v1)',
   disposition='Ma-Ma-Yeh partial gamma-positivity conjecture for Jacobi-Stirling plateau/descent/ascent polynomials: the reserved source itself proves it ("Specialization ... confirms a recent partial gamma-positivity conjecture due to Ma, Yeh and the second named author").', rec=('abs-346486',)),
}
out = {}
for row in res['rows']:
    i = row['mathdb_id']; e = ext[str(i)]; d = D[i]
    out[str(i)] = dict(mathdb_id=i, title=e['title'], source_url=e['source_url'], provenance=e['provenance'],
                       statement_literal=e['statement'], review_depth=d['review_depth'], outcome=d['outcome'],
                       disposition=d['disposition'], scripts=d.get('scripts', []), outputs=d.get('outputs', []),
                       receipts=receipts(*d.get('rec', ())), candidate=d.get('candidate', False),
                       credit_claim='none')
assert len(out) == 20 and set(out) == {str(x) for x in res['ids']}
(L / 'results.json').write_text(json.dumps(out, indent=1, ensure_ascii=False) + '\n')
print('ok', len(out), sum(o['candidate'] for o in out.values()))
