from work import *
proof='''# Finite counterexample to Hegarty–Martinsson–Wedin Conjecture 4.2

Status: complete ordinary computer-assisted argument, eligibility HOLD. One source family only. This is not an independently reviewed or novelty-cleared result. The explicit rational table is part of the construction, not numerical evidence replacing a proof.

## Literal target and separating inequality

Primary body: https://arxiv.org/pdf/1803.00823v1, Hegarty, Martinsson and Wedin, submitted 2 March 2018, Section 4 pp11–13, Conjecture 4.2. For every n in N, the conjecture identifies the attainable symmetric honest tournament win-vector region with A*_n, the convex hull defined by Rules 1–3 and equation (4.7). Whether a bar is attached to the attainable region is immaterial here: a strict separating inequality refutes both the actual and closure formulations. Section 2 requires a bounded number of sequential matches; the construction below has exactly 192. No extra identity-dependent information or access to unknown strengths is used.

Every vector x in A*_4 satisfies x1+x2 >= 1/2: vertices 1 and 2 each send two arcs, all four land in {1,2}, and v_i=indeg(i)/8. Convex combinations preserve the inequality. No hull software is needed for this inequality.

## Exact rational table and global map

Use edge order (12,13,14,23,24,34). The 729 rows in witness-table.csv enumerate all s in {0,1,2}^6 exactly once. Its four integers w_i(s), divided by 48, define V_i(s). verify_finite.py exhaustively checks, using integer arithmetic, the following finite assertions:

1. Every w_i is nonnegative and their sum is 48.
2. Under every permutation p of four players, V_{p(i)}(p.s)=V_i(s), with reversed edges complemented s->2-s.
3. If coordinate ij increases by 1, V_i does not decrease and V_j does not increase.

The verifier uses the CSV directly; it does not import the LP, floating point, symmetry quotient or discovery witness JSON. Every assertion is a bounded integer comparison; all 729 states and all 17,496 state/permutation combinations are checked. The table is an explicit finite definition. Replacing this certificate with a short structural winner rule would improve exposition but is not an unproved mathematical bridge.

For q in [0,1], define h0(q)=max(1-2q,0), h2(q)=max(2q-1,0), h1(q)=1-h0(q)-h2(q). Define, on the whole six-dimensional cube,

f_i(P)=sum_s V_i(s) product_{ij} h_{s_ij}(p_ij).

The h's are nonnegative and sum to 1, so f is a continuous probability-valued map. The permutation identities h0(1-q)=h2(q), h1(1-q)=h1(q) and the table symmetry prove global symmetry. Holding other coordinates fixed, the slope of f_i as p_ij increases on either half interval is twice a nonnegative convex combination of the corresponding table differences. Thus f_i is nondecreasing in its own win probability. Likewise f_j is nonincreasing. This proves honesty on the entire cube, including boundaries, rather than only on sampled doubly-monotonic matrices. This is also the explicit construction underlying source Proposition 6.8, whose proof was read before the attack.

## Actual finite tournament; no limiting theorem needed

Each unordered pair plays exactly N=32 times, in any fixed sequential schedule. Write Q_ij for the observed fraction won by i. Elect a single winner according to the distribution f(Q). This requires only rational sampling and match results. Relabeling players relabels the independent match-count distribution and f, so the source's winning-probability definition of symmetry holds. Even conditioning on the outcomes of every other match, changing a loss to a win raises one's own Q_ij and hence cannot lower one's probability of selection. Averaging proves honesty at each history, for every underlying P in M_4. There are precisely 6*32=192 matches.

Specialize to P with rows

    (1/2,1/2,1,1)
    (1/2,1/2,1/2,1/2)
    (0,1/2,1/2,1/2)
    (0,1/2,1/2,1/2).

Entries increase along rows and decrease down columns, so this is literally in D_4. Edges 13 and 14 are deterministic wins. Counts on the other four edges are independent Binomial(32,1/2).

For a fair count K, set t=E h0(K/32). Symmetry gives E h2=t and E h1=1-2t. Finite summation yields t=300540195/4294967296 (the verifier also checks t=binom(32,16)/2^33). Independence and the displayed multilinear formula collapse the expected top-two winning probability to only 81 terms. Expansion of those exact table entries gives

S(t)=1/4+(15/4)t-(17/2)t^2+(185/24)t^3-(11/4)t^4.

verify_finite.py independently derives all five coefficients directly from the CSV using the binomial theorem; it does not trust the LP or a stored polynomial. At the displayed t, S(t) is

    644305742079015272838458033019501771781 /
    1361129467683753853853498429727072845824

which is strictly less than 1/2. The positive gap is

    36258991762861654088291181844034651131 /
    1361129467683753853853498429727072845824.

Consequently this actual symmetric honest four-player tournament has a doubly-monotonic specialization outside A*_4. It refutes the universally quantified Conjecture 4.2, without claiming a characterization of the attainable region.

## Objections and limits

The finite table is large and was found by linear optimization. Its rational properties have separate exhaustive standard-library checks, not an external independent review or formal certificate. The source itself supplies the general finite-discretization technique (Propositions 6.6–6.8); only finding an actual separating table and finite tournament could be credited, never interpolation or LP formalization. The frugal theorem (Section 5) does not apply: no uniformly selected player is omitted from play. This construction uses all six pairs. No current registry head was obtained, no worldwide priority is claimed, and a classical/source-method routine-adaptation objection remains for root adjudication. No Lean or manuscript was written.
'''
(L/'PROOF.md').write_text(proof)
scout='''# Fourteen distinct primary-source question families

30 October 2026. Fourteen screens, not fourteen open nominations. Every identifier below names a frozen PDF fetched from https://arxiv.org/pdf/IDENTIFIER. retrieval.jsonl records exact URL/UTC/hash; bindings.jsonl binds PDF and extracted body. slice.json records first/latest chronology; the XML retains original author metadata. No variants or multiple clauses are counted separately. A March 2018 slice was deliberately distinct from r256/r258. Those scouts and the broader historical index were hash-bound before scientific reading. Early exact identifier/title checks and subsequent semantic checks are recorded; they are bounded rather than exhaustive duplicate clearance.

## Only ranked survivor

1. Hegarty–Martinsson–Wedin, 1803.00823v1, 2 March 2018, Conjecture 4.2 p13: for every n, the symmetric honest attainable win-vector region equals A*_n of Rules1–3/Eq4.7. **Complete finite refutation, eligibility HOLD.** PROOF.md constructs a 192-match four-player tournament whose top-two winning probability is approximately .4733611, below A*_4's universal .5 bound. First mechanism: exact symmetry-quotiented LP on the full ternary comparison cube, with integer-normal separating facets and rational primal/dual reconstruction. Second mechanism: independent table checking, global multilinear honesty proof, and exact binomial-collapse calculation for an actual finite tournament; small N failures through24 were retained rather than being treated as disproof of the route. Nearest applicable source proofs: Theorem4.3 establishes only A* inclusion, Theorem5.1 controls frugal tournaments, Propositions6.6–6.8 give discrete-map equivalence. The actual source approximation proof6.3 was read, but the finite construction avoids relying on a merely limiting implementation. No exact/title/semantic history match was found for this target. Current narrow arXiv title and honesty searches identify the source, not a proof of current openness. Current registry head unavailable; no specialist exhaustive citer search. Decisive next step: independently check the literal source quantifiers, CSV verifier and finite probability argument, then evaluate source-method/classical-subsumption and current-prior objections before any formalization. No second or third nomination is manufactured.

## Compact remaining screens

2. Sun–Gutin–Yeo–Zhang, 1803.00284v1, Section4: for every fixed k>=2,l>=2, is deciding kappa_k(D)>=l NP-complete? Here kappa_k is the minimum over k-vertex sets of the maximum number of internally disjoint strong subgraphs containing that set. Section2 proves the local fixed-set hardness and special-class algorithms, but replacing one prescribed set by a universal minimum is a genuine reduction gap. Park: need a forcing gadget preserving every other terminal set; local hardness alone does not transfer. No such gadget, no new complexity result.

3. Kai Wang, 1803.00673v1, Section4.3(1): D_f(n)/D(n)->1 for all zero-free graphical degree sequences counted uniformly by length; also predicts monotonicity for n>=8. Algorithm1's decomposition checks characterize forcibly connected sequences; potentially connected counts do not prove the limit. Park: need a uniform counting injection bounding graphical split sequences, with multiplicity control. Random labeled-graph connectivity uses a different measure. No asserted asymptotic theorem or counterexample.

4. Karimi–Mafi, 1803.00730v2, Herzog–Qureshi question in introduction: astab(I)=dstab(I) for every polymatroidal monomial ideal. **Already refuted in the actual source**, Examples2.21–2.22. The proof gives dstab=1 and astab=n-2 in the displayed n-variable family via monomial localization and maximal associated-prime tests. Theorem0.1's surviving restricted equalities cannot be presented as the unrestricted question. No new nomination.

5. Sho Matsumoto, 1803.01121v2, Conjecture1.6: every coefficient of every spin Kerov polynomial K^spin_(2k-1), k>=1, in the specified R_(2j), is a nonnegative integer. Theorem1.4 establishes polynomiality; the triangular inversion proof does not preserve signs. Ordinary Kerov positivity is not itself a proof under the spin substitution. Closest fetched follow-up1811.10434v2 gives linear/spin character relations and lists further closed-form work as in preparation; not a positivity clearance. Park: need a positive factorization formula in the exact double-diagram cumulants. No fresh mechanism sufficient for full-scope attack; no assumption that ordinary positivity solves it.

6. Murat Şahin, 1803.01603v1, Conjecture1: for all1<=r<=d, N_(d,r)(s)=s for1<=s<=d, N(d+1)=d+r, and N(s)=N(s-1)+N(s-d-1) for s>=d+2, counting (s,s+r)-cores with d-distinct parts. **Publicly proved**, Noah Kravitz1807.08875v2, Theorem4.1/Section4 (actual proof read): r-reduction reduces to the r=1 twin-free beta-set recurrence. Historical semantic Şahin hit also exists in r63; no rediscovery. No extension beyond source hypotheses nominated.

7. Melissa Sherman-Bennett, 1803.02492v2, Conjecture6.1: for every marked surface, quadrilateral-with-chosen-diagonal objects q_T(gamma) union {gamma} map bijectively to the semifield-independent X-variables. Theorem1.1 supplies finite classical-type injectivity using surface formulas; the general known surjection does not prove injectivity. Park: a uniform cross-ratio/lamination separation invariant must survive repeated sides and punctures. No such invariant proved; finite-type extension is not a new result.

8. Kanade–Russell, 1803.02515v1, Section4.1/Eq4.1 and companion identities as ONE family: coefficientwise equality of the displayed triple q-sum with its modulus12 product. Its staircase/jagged-partition proof derives the sum-side, not every product identity; source Theorem3.3.2 uses an already-known product relation. **Park prior-heavy**, not an open nomination. Actual follow-up bodies1809.06089v2 and2211.03652v3, plus current September2026 mod12 proof metadata, show several overlapping proved/reduced identities. No unverified assertion that one follow-up settles all clauses. Exact product-by-product matching is required before solving; new coefficient sweeps would be premature.

9. Balogh–Kostochka–Liu, 1803.02537v2, introduction: chi_p(D(G))<=5 for every subcubic G, where D subdivides each edge once and color-i vertices have distance>i. Actual Theorem1 proves8, with feasible-coloring recoloring machinery. **Publicly resolved route identified before solving:**2603.23434v1 proves the (1,1,2,2) theorem outside Petersen and explicitly transfers it to subdivision5; Petersen's subdivision coloring is already known. Thus no new generic coloring attack. Original predecessor body not separately retrieved; this is exclusion by a later actual primary body.

10. Beaudou–Brewster–Foucaud, 1803.02550v2, Conjecture2: gamma_b(G)<=2mp(G) for every graph, where mp imposes at most r chosen vertices in every radius-r ball and gamma_b minimizes total covering radius. Theorem1 proves2mp+3; Section2 handles mp<=4. Its isometric-path grouping and endpoint cover lose an additive constant; the restricted theorem is not the general statement. Park: need a new charging/exchange lemma linking uncovered branches to an extra packing point. Current cactus/chordal/hypercube metadata is restricted, not a universal closure. No graph census result nominated.

11. Margolis–Schnabel, 1803.03569v1, Question1 (attributed Y. Ginosar): every G-harmonic finite n-tuple of subgroup indices is Z-harmonic? Pairwise disjoint cosets must transfer to pairwise disjoint integer residue classes. TheoremB handles n<=4 and TheoremA handles HSC for group order<1440, using gcd/index exclusions. **Reject famous-hard disguise:** the unrestricted implication would settle Herzog–Schönheim; no new harmonic-transfer mechanism. Bounded group enumeration cannot prove it. A semantic Herzog hit in r172 reinforces nonfreshness; no reattack.

12. Alderson–Neri, 1803.04020v3, introduction/Sections3–4: for every prime power q and k>=1 does an [n,k]_q code attain (q^k-1)/(q-1) distinct nonzero weights for some finite n? **Already proved by source**, Theorems3.4 and4.9. Geometric proof assigns powers-of-two multiplicities to projective points so hyperplane characters are all distinct; algebraic proof uses repeated-coordinate vectors to separate counts. Minimal length is a different optimization question and not silently counted as another nomination.

13. Xiang-Dong Hou, 1803.04071v1, Tu–Zeng–Li–Helleseth necessity question: for even prime power q and nonzero a,b in F_(q²), is X+aX^[q(q-1)+1]+bX^[2(q-1)+1] a permutation exactly under Eqs1.3–1.4? **Already proved** by Bartoli and this source's Theorem1.1 after b-normalization. Actual Section2 reduction to the unit circle and Sections3–4 Hasse–Weil factorization conditions are the mechanism; no search for a source counterexample was started. Original Bartoli body not separately read, so exclusion rests on Hou's proof body.

14. Anđelić–Ghorbani–Simić, 1803.00245v1, Conjecture3.1 attributed to Alazemi et al.: every vertex of every chain graph is a downer for every nonzero eigenvalue. **Already refuted in source** Theorems3.4–3.5: periodic half-graph eigenvectors with zero entries give neutral vertices. The explicit six-period vector/eigenvector verification is the nearest proof; no new spectral family nominated. The predecessor's original body is not separately cleared.

## Access and chronology limits

No denied GitHub API/raw/codeload/diff/patch, ScienceDirect or Google challenge routes were retried; no browser/proxy/TLS bypass or external mutation. Current public-registry HEAD is unknown. Dated arXiv version metadata, current search responses and actual bodies are separate evidence, not a blanket novelty clearance. Nonsingular-block source v3 returned404; a distinct v1 request returned a PDF with a December2024 internal date, inconsistent with its nominal2018 tag. It is not nominated and no chronology claim rests on it. Additional SF/chomp/block bodies were incidental exclusions and not added to the fourteen. No recursive historical tree copy.
'''
(L/'SCOUTING.md').write_text(scout)
(L/'SUMMARY.md').write_text('''# r260 handoff

Fourteen distinct primary-source families screened; exactly one ranked survivor. A finite table and exact ordinary computer-assisted proof refute Hegarty–Martinsson–Wedin1803.00823v1 Conjecture4.2: a symmetric honest four-player tournament with192 matches has top-two winning mass approximately0.4733611, whereas A*_4 requires at least1/2. Read PROOF.md, witness-table.csv and verify_finite.py. The separate standard-library verifier passes729 states and17,496 permutation checks, plus monotonicity and exact binomial arithmetic. A second expanded-state checker passes75,816 component checks.

**Eligibility HOLD.** Independent review, current proof-registry clearance and substantive/classical-adaptation adjudication remain. The source already contains the generic discrete-LP/interpolation technique; these helpers receive no credit. No worldwide priority or acceptance claim. Counts unchanged9 additional/39 total/next40; root alone accepts/counts. No children, shared/git/public/browser/MathDB edits, Lean or manuscript. Final manifest excludes itself and its separately generated verification receipt.
''')
(L/'discovery.md').write_text('''# One-family candidate; root decision required

Claim: the literal universally quantified Conjecture4.2 in Hegarty–Martinsson–Wedin2018 is false, already at n=4. The witness is an actual finite192-match tournament, not merely an unattainable abstract map. Complete source-scoped argument and objections are in PROOF.md. Exact rational separation is positive. No assertion about the complete achievable region, strict honesty, or all n is needed.

Two sustained mechanisms were completed. First: symmetry quotient and full-grid honesty LP;126 facet/state optimizations were rationally checked. Second: remove both the numerical optimizer and asymptotic approximation from the mathematical endpoint by integer table verification, interpolation, and a binomial-basis collapse. Direct small-round attempts1–24 fail to separate;32 works. Failures are preserved. None of these substeps is an extra discovery.

Nearest source prior is the source's own discrete-map polytope method; its frugal-tournament theorem does not cover the all-pairs construction. Current narrow arXiv searches and446 hash-bound historical/catalogue references do not establish absence of public prior. No live registry head was available under inherited route blocks. Independent source/adversarial review and novelty/substantive review must precede Lean or manuscript investment. Root alone decides acceptance. Count credit requested now:0.
''')
(L/'progress.md').write_text('''# Final lane progress

Read ancestor/batch instructions and administrative snapshots; counts9/39/next40. Froze and hash-bound r256/r258 and historical immediate reports before body reading. Retrieved distinct primary bodies and early prior/subsumption evidence. Screened14 source families without counting variants. Found one exact finite tournament refutation and sustained it through an LP mechanism and a separate binomial/interpolation mechanism. Two exact standard-library verifiers pass. No acceptance or external action.

The source already provides the generic LP method; routine-adaptation is an explicit strongest objection. No full registry head, specialist database sweep, independent review, Lean, manuscript or strict replay. Administrative files are snapshots only. Scientific originals and derived text hashes are separately checked again after all reports are written. Only this assigned lane was written.
''')
(L/'failures.md').write_text('''# Preserved failures and negative checks

- Source https://arxiv.org/pdf/1803.03947v3 returned HTTP404; recorded in retrieval.jsonl. A different v1 body has an internal2024 date; not used as a nominee or historical-priority evidence.
- Initial query helper failed TypeError unsupported operand / for str and str before retrieval. Corrected module import; no source mutation or cap raise.
- First HiGHS run aborted with exit134, terminate called without an active exception, sampled groupRSS89,239,552 bytes. Explicit single-thread HiGHS option then succeeded under the identical guard; scipy warns that this option is forwarded verbatim. Both retained here; no cap was increased.
- Finite tournament top-two mass at N1,2,3,4,6,8,12,16,24 does not violate1/2. finite-tournament.json preserves direct first calculations; binomial-collapse.json retains extended checks. N24 gives approximately.5009261; N32 separates. These failures prompted exact binomial-collapse rather than expanded brute-force enumeration.
- Initial broad phrase query returned many unrelated records; preserved XML/JSON, replaced with bounded more precise title/author combinations. No irrelevant hit used as prior clearance.
- Inherited denied GitHub/ScienceDirect/Google routes were parked without retry, not silently marked clear.
''')
guard=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py')
(L/'provenance.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'lane':str(L),'counts':{'additional':9,'total':39,'next':40,'changed':False},'status':'finite mathematical refutation; eligibility HOLD','guard':{'path':str(guard),'sha256':sha(guard),'AS':536870912,'group_RSS':536870912,'CPU':210,'wall':230,'cap_raises':False},'sources':'bindings.jsonl','retrievals':'retrieval.jsonl','immutable_references':'references.json','current_registry_head':None,'independent_review':False,'external_mutations':False,'lean':False,'manuscript':False},indent=2))
print('reports written')
