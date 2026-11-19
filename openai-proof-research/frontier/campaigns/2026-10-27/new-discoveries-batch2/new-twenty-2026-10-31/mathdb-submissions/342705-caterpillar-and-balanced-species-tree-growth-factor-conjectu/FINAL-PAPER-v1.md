# Duplication-loss histories: the four source claims

Author implementation, 2026-11-15. The unconditional canonical, source-event and unranked endpoints are proved in FinalAssembly. This is a standalone proof and literal-source record, not independent semantic acceptance or fresh extracted replay. Credit remains zero; administrative counts remain 72/80 NEW, 111 total.

## Statement and source fidelity

For each k>=1 there is N_k>=1 such that for EVERY k-leaf species s and every n>=N_k, a(B_k,n)<=a(s,n)<=a(C_k,n). Equality on the left holds exactly for the balanced shape; equality on the right holds exactly for the caterpillar shape. Every species has a positive real nth-root limit g(s)=1/rho(s). Moreover g(C_k)/k tends to infinity and 2k<=g(B_k)<=1000k for every k>=1. Here linear means Theta(k), not an asserted limiting slope. No quadratic caterpillar order or historical constant 80 is asserted.

The target is MathDB342705, bound to the owned raw record and live target-only field projection dated 2026-11-15. Source: Cedric Chauve, Yann Ponty, Michael Wallner, Counting and sampling gene family evolutionary histories in the duplication-loss and duplication-loss-transfer models, arXiv1905.04971v1 (2019-05-13), Conjecture4.1; owned final PMC7052048, Conjecture4.5. Both exact conjectures were read; the v1 material pages4,8,11,16 were rendered and inspected. Source URLs and file hashes are in the source index. The source asks for superlinearity, not Theta(k^2).

A species is a rooted full binary tree with k leaves. C_1=B_1 is a leaf; C_(k+1)=(C_k,leaf); B_k=(B_floor(k/2),B_ceil(k/2)). These are the source families for every positive k. The source page16 footnote identifies balance up to child swaps. Zero-index families denote a leaf only as an auxiliary convention.

## Actual histories and analytic foundation

Hist has extant, ordered duplication, both-child speciation, keep-left and keep-right constructors. Loss is the explicit disappearing sibling at a speciation, never a disposable duplication child. Size n counts extant genes. Species addresses in encode retain the species map at every event, including losses. Induction gives encode_valid; inverse parsing gives valid_has_history and encode_injective. Their size-preserving equivalence sourceFiberEquiv identifies the finite size fiber with Valid event trees of extantCount n. Thus count is an actual cardinality and sourceCard is the cardinality of the literal source event fiber, with sourceCard_eq proved, not postulated. Duplication children remain ordered throughout.

Finiteness follows from depth<=n*weight(s) and the finite recursive pool. Unique root decomposition gives H_leaf=z+H_leaf^2 and H_(a,b)=H_a+H_b+H_a*H_b+H_(a,b)^2. The derivation uses disjoint constructors and finite-fiber equivalences. Skeleton decomposition cuts duplication nodes into binary skeletons whose atoms are the nonduplication constructors. Summing their nonnegative weights gives the least fixed point: finite cuts increase to the complete history sum, and every nonnegative prefixed value bounds every finite cut. This proves that the formal evaluation is the actual history sum, not a substitute recurrence definition.

The scalar least solution is C(q)=(1-sqrt(1-4q))/2 on 0<=q<=1/4. Starting at the leaf and then inducting over species, continuity and strict increase of the child input locate a positive first threshold rho, strictly below each proper child threshold; at that threshold H=1/2. The least-fixed-point bound gives finiteness up to rho. Above rho, a finite solution would solve the same quadratic beyond its critical input (or violate a child threshold), impossible. This proves the actual summability characterization used below. All these bridges are included in the source appendix.

Duplication is an injection from the product of size-i and size-j fibers to the size-(i+j) fiber. Positive fibers exist at every n>=1, so the negative logarithms of counts are subadditive. The threshold coefficient bound supplies a linear lower bound, making Fekete's limit finite. Exponentiating yields the positive actual real root limit g. Convergence at rho gives count(s,n)*rho^n<=1 and hence g*rho<=1. If g*rho<1, choose rho<z<1/g; the root limit bounds the tail by a convergent geometric series, forcing actual summability at z, contrary to the threshold characterization. Thus g=1/rho. This proves an actual limit over all n, not just a limsup or a formal growth symbol.

## Caterpillar maximum

Order formal series coefficientwise. Put u=a+b+ab, v=c+b+cb, where a>=c>=0 and b>=0 have zero constant coefficients. Compare the two outer inputs Q_L=(1+c)C(u)+c and Q_R=(1+a)C(v)+a. The m=1 Catalan term is u(1+c)-v(1+a)=a-c, cancelling c-a. For every m>=2 direct polynomial factorization gives
 (1+c)u^m-(1+a)v^m
 =(a-c)[sum_{j=0}^{m-1}u^(m-1-j)v^j + uv*sum_{j=0}^{m-2}u^(m-2-j)v^j].
To verify: substitute (1+c)=(1+v)/(1+b), (1+a)=(1+u)/(1+b), factor u^m-v^m and uv*(u^(m-1)-v^(m-1)), and cancel u-v=(1+b)(a-c). This is a polynomial identity; it does not rely on coefficient positivity of a reciprocal series. Summing positive Catalan coefficients proves Q_L>=Q_R and F(F(a,b),c)>=F(a,F(b,c)). All formal compositions are locally finite. At positive real admissible inputs, a>c and b>0 give strictness already at m2.

Every nonleaf H dominates the leaf series L=C(z), strictly for positive real z. By induction first replace both root children by caterpillars of their sizes a>=b. For b>=2, rotate (C_a,(C_(b-1),leaf)) to ((C_a,C_(b-1)),leaf), strictly since H_Ca>L, then replace the inside by C_(k-1) by induction. For b1 the root already has caterpillar form. Induction terminates at smaller leaf counts; a noncaterpillar forces either a strict child replacement or this strict root rotation. Hence H_S<=H_Ck coefficientwise and rho_Ck<=rho_S.

If radii were equal for a noncaterpillar, every intermediary k-leaf tree is coefficientwise bounded by C_k, hence has radius at least this common radius. Its proper children have strictly larger radii by the source lemma. All endpoint values thus exist on the closed principal branch. Strict root-input/child comparisons still hold there, forcing H_Ck>H_S while both are1/2, impossible. No derivative at the singular root or divergent Catalan endpoint sum is used: C has a finite value at1/4 and is strictly increasing on[0,1/4]. Thus rho_Ck<rho_S unless S is a caterpillar.


## Balanced minimum

Write x_s(z)=log(1+H_s(z)) and f(u)=log(1+C(exp(u)-1)). The proved closed-domain theorem says f is strictly convex on [0,log(5/4)], f(0)=0, and f(v)-f(u)>v-u for 0<=u<v<=log(5/4). The derivative formula in the supplied ordinary proof is f'(u)=(1+w-w^2)/(1-w-2w^2)>1, where w=C(exp(u)-1); its derivative with respect to w is (2+2w+3w^2)/(1-w-2w^2)^2>0 in the interior. Closed endpoint inequalities use the common continuity/convexity theorem, not a finite derivative at the endpoint.

Fix a finite K>=1 and 0<z<=rho(B_K). The proved single-leaf expansion B_j to B_(j+1), independent of extremality, strictly lowers radius and strictly increases branch value at any common valid positive argument. Thus rho(B_K)<=rho(B_j) for 1<=j<=K. Put b_j=x_(B_j)(z). All b_j needed through K exist, are positive and strictly increasing. At every internal index j<=K, b_j=f(b_floor(j/2)+b_ceil(j/2)); the input belongs to the CLOSED domain, by the actual node-input bound <=1/4. `exp_log_pair` verifies the conjugation directly from actual branch values.

We prove 2b_n<b_(n-1)+b_(n+1) for 2<=n and n+1<=K by strong induction. At center 2, f(2b_1)>2b_1, so b_2>2b_1. Expansiveness between 2b_1 and b_1+b_2 yields b_3-b_2>b_2-b_1. At odd center n=2m+1, the three inputs are 2b_m, b_m+b_(m+1), 2b_(m+1), equally spaced and distinct; strict convexity applies. At even center n=2m>=4, the inputs are b_(m-1)+b_m, 2b_m, b_m+b_(m+1). The smaller-center induction gives that twice the middle input is strictly below the sum of the outside inputs. Monotonicity together with strict midpoint convexity again gives the desired strict inequality. Every referenced index is <=K. This is `discrete_convex`, discharged for the actual balanced log sequence by `balanced_log_discrete`.

Consequently d_i=b_(i+1)-b_i strictly increases over its finite valid index range. If 1<=i<=j and j>i+1, replacing (i,j) by (i+1,j-1) strictly decreases b_i+b_j, since d_i<d_(j-1). Finite induction on j-i shows that only the floor/ceiling split minimizes this sum. `split_min` proves both the weak inequality and equality iff i<=j+1 and j<=i+1. The cases with total size 2 or 3 are already central and need no nonexistent convexity index.

Now fix also z<=rho(s), leaves(s)<=K. Structural induction proves x_(B_leaves(s))(z)<=x_s(z), with equality iff ShapeIso(s,B_leaves(s)). The leaf case is literal reflexivity. At a node, both children are valid because each child radius is strictly larger than the parent's. Apply the induction to both children and the split inequality to their positive leaf counts; the resulting input ordering is within f's closed domain on BOTH sides. Strict expansiveness implies that equality after applying f forces equal inputs. The ordered sum of two weak child inequalities can be equal only if each is equal, and the split must be central. The child isomorphisms therefore combine by a node or a swap constructor. Conversely ShapeIso preserves branch values. This proves `log_minimum` without any extremum hypothesis.

For a nonisomorphic s of k leaves, suppose rho(s)>=rho(B_k). Take z=rho(B_k)>0 in the preceding theorem with K=k. Its weak inequality is strict because equality would give ShapeIso. But the actual threshold endpoint is H_(B_k)(z)=1/2 and every actual branch value, including H_s(z), is <=1/2 there. Their logarithms cannot have the asserted strict ordering. This contradiction proves rho(s)<rho(B_k). ShapeIso radius invariance supplies equality for the isomorphic class; the strict result excludes equality elsewhere and yields the weak global comparison. These are `rho_balanced_strict`, `rho_balanced_le` and `rho_balanced_eq_iff`.

For the actual counts, use the proved convergence count(s,n)^(1/n)->growth(s)>0 and growth(s)=1/rho(s). If s is outside the balanced class, the strict radius comparison gives growth(B_k)<growth(s). A real number between the two limits separates the nth roots for all sufficiently large n. Monotonicity of nonnegative real rpow shows count(B_k,n)<count(s,n) eventually. This is the already-proved actual-root comparison helper `eventual_count_lt_of_rho_lt`, not an assumed asymptotic transfer theorem. For ShapeIso trees the common cardinality invariance gives equality for all n. `FiniteShapes.fixedLeavesFintype` provides a finite type of all ordered k-leaf species. Finite conjunction of these eventual statements has an eventual threshold N; replace it by max(1,N). Thus one N_k works simultaneously for every s and all n>=N_k, with the exact equality and strictness classes. The final endpoint is the conjunction of these radius and actual-count statements.


## Quantitative growth arguments

Write H_s(z) for the actual nonnegative history evaluation on 0<=z<=rho(s). The foundation proves H_s(rho(s))=1/2 and strict child threshold separation. For a leaf, H=z+H^2. At a binary node with child values x,y and parent value w, w=x+y+xy+w^2. Every term is nonnegative. Induction gives H_s(z)>=leaves(s)*z, hence g(s)>=2*leaves(s).

For caterpillars let x_j=H_Cj(z), with a fixed z in the critical interval of C_k. All smaller caterpillars remain in their critical intervals. The node identity gives x_(j+1)>=x_j+x_(j+1)^2, and the universal leaf-mass bound gives x_(j+1)>=(j+1)z. Induction starting at j=1 yields

    x_j >= (j^3-j) z^2 / 3.

Indeed the polynomial increment is j^2+j, at most (j+1)^2. At the actual critical value z=rho(C_k), x_k=1/2. Multiplication by g(C_k)^2, using g*rho=1, gives

    k^3-k <= (3/2) g(C_k)^2.

For k>=2, k^3>=2k, so g(C_k)^2>=k^3/3. For any M>0, choose an integer N>3M^2+2. If k>=N and g(C_k)/k<M, positivity implies g(C_k)^2<M^2 k^2<k^3/3, a contradiction. M<=0 follows from positivity. This proves the full filter limit, not merely a subsequence. The k^(3/2) lower bound suffices; no quadratic upper bound or two-sided quadratic order is claimed.

For balanced trees we prove the following quantitative bound throughout the actual critical interval:

    H_Bk(z) <= k*z + 20*(k*z)^2, provided k*z <= 1/1000.

The leaf case follows from H<=1/2 and H=z+H^2: H<=2z, then H<=z+4z^2. For a split k=a+b, a=floor(k/2), b=ceil(k/2), we have a,b>=1 and k^2<=5ab. Put x=H_Ba(z), y=H_Bb(z), w=H_Bk(z), and q=x+y+xy. The inductive bounds and az,bz<=1/1000 give x<=1.02az, y<=1.02bz, xy<=2abz^2, and q<=1.1kz. The exact node equation and w<=1/2 imply w<=2q and w^2<=4q^2<=5(kz)^2. Thus

    w <= kz + [20(a^2+b^2)+2ab+5k^2]z^2
      <= kz + 20k^2 z^2,

because 5k^2<=25ab<=38ab. The children are inside their proved critical intervals by strict child threshold separation. Strong induction covers every positive integer k, including odd splits.

If g(B_k)>1000k then krho(B_k)<1/1000. Apply this bound at the actual root threshold: 1/2<=1/1000+20/1000^2, impossible. Hence g(B_k)<=1000k. The universal lower bound supplies 2k. This proof uses neither the parallel strict balanced extremum theorem nor dyadic comparisons, generic singularity transfer, numerical samples, or an assumed semantic bridge.

The formal endpoint also states the positive actual count root limit and inverse-threshold identity for every species tree. ShapeIso preserves count, radius, growth and leaf number. Additional exported theorems transport the balanced inequalities and caterpillar family limit across arbitrary child swaps.


## One cutoff and genuine unranked transport

For each k take A_k from eventual_balanced_minimum and B_k from eventual_caterpillar_maximum. Set N_k=max(A_k,B_k). It is at least one. Each n>=N_k satisfies both comparisons and both equality equivalences simultaneously for every species with k leaves. The finite family here is all ordered full binary k-leaf trees, so it covers every unranked class; it is not a selected sample. At k=1,2,3 the shared shape cases obey the same proofs. No k-independent cutoff is asserted.

ShapeIso is exactly the inductive independent-child-swap relation. Its refl/symm/trans proofs make a setoid. FinalSourceTransport constructs the actual quotient Unranked and uses proved invariance to descend leaves, count, rho and growth via Quotient.lift. Quotient equality is proved equivalent to ShapeIso. Quotient induction transports the uniform inequalities and positive root limits to every unranked species; canonical family growth is definitionally the descended growth. This is the expanded unranked_four_claims_expanded theorem. Arbitrary representatives of the balanced family satisfy the same uniform bounds, and arbitrary caterpillar representatives satisfy the same superlinear limit. The source_event_four_claims_expanded theorem separately replaces every count by sourceCard using the proved event-fiber equivalence. These transports assume no source-count, extremum or convergence bridge.

## Reproduction contract

The source appendix is UTF-8 literal text, with byte length and SHA256 in each SOURCE marker. Copy the extractor below verbatim and run `taskset -c 4,5 python3 -I -B extract_final_paper.py FINAL-PAPER-v1.md cache/paper-extracted`. It does not consult the project layout, JSON index or provider cache. Compare its manifest to the embedded source map and both prefix maps.

The pinned external boundary is Lean4.34.1 plus mathlib revision d13f23b723b8a846827a245b89c10fc7d3f11612 and the exact upstream package paths/imports in PINS. Binary hashes are enforced by formal_command.py. Upstream oleans are trusted pinned inputs; no complete upstream source rebuild/origin attestation is claimed. Each custom import must resolve only to the listed production module of that name.

Author commands, from this lane, were `taskset -c 4,5 bash ./check32.sh MODULE UNIQUE_LABEL` and separately `taskset -c 4,5 bash ./checker32.sh MODULE UNIQUE_LABEL`. The embedded receipt/resource map gives every exact invocation and low-level argv, source/olean hashes, limits, stdout references and outcomes, including the failed initial transport elaboration. A fresh paper-only replay must use a separately authorized empty build directory, extracted src, literal harness and pins, and execute those two commands once for each module in the embedded dependency_order. No cached project olean is a replacement for that replay. The author32-call allocation does not authorize spending126 replay calls here.

Author extraction verifies all63 literal sources without invoking Lean on the60cached providers. For independent replay, archive the full output of each wrapper invocation and reparse all axiom outputs, rather than trusting this paper's stored success labels. Olean hashes can depend on file metadata/build context; source equality is mandatory and fresh separate kernel checking is mandatory.

## Exact expanded endpoint types

### LiteralDL.FinalStage.source_target

```lean
theorem source_target : SourceTarget
```

### LiteralDL.FinalStage.source_four_claims_expanded

```lean
theorem source_four_claims_expanded :
  (∀ k : Nat, 0 < k → ∃ N : Nat, 1 ≤ N ∧
    ∀ s : Species, leaves s = k → ∀ n : Nat, N ≤ n →
      count (balanced k) n ≤ count s n ∧ count s n ≤ count (caterpillar k) n ∧
      (count (balanced k) n = count s n ↔ ShapeIso s (balanced k)) ∧
      (count s n = count (caterpillar k) n ↔ ShapeIso s (caterpillar k))) ∧
  (∀ s : Species, 0 < growth s ∧
    Tendsto (fun n : Nat => (count s n : ℝ) ^ (1/(n:ℝ))) atTop (nhds (growth s)) ∧
    growth s = (rho s)⁻¹) ∧
  Tendsto (fun k : Nat => growth (caterpillar k)/(k:ℝ)) atTop atTop ∧
  (∀ k : Nat, 0 < k → 2*(k:ℝ) ≤ growth (balanced k) ∧
    growth (balanced k) ≤ 1000*(k:ℝ))

```

### LiteralDL.FinalStage.source_event_four_claims_expanded

```lean
theorem source_event_four_claims_expanded :
  (∀ k : Nat, 0 < k → ∃ N : Nat, 1 ≤ N ∧
    ∀ s : Species, leaves s = k → ∀ n : Nat, N ≤ n →
      sourceCard (balanced k) n ≤ sourceCard s n ∧ sourceCard s n ≤ sourceCard (caterpillar k) n ∧
      (sourceCard (balanced k) n = sourceCard s n ↔ ShapeIso s (balanced k)) ∧
      (sourceCard s n = sourceCard (caterpillar k) n ↔ ShapeIso s (caterpillar k))) ∧
  (∀ s : Species, 0 < growth s ∧
    Tendsto (fun n : Nat => (sourceCard s n : ℝ) ^ (1/(n:ℝ))) atTop (nhds (growth s)) ∧
    growth s = (rho s)⁻¹) ∧
  Tendsto (fun k : Nat => growth (caterpillar k)/(k:ℝ)) atTop atTop ∧
  (∀ k : Nat, 0 < k → 2*(k:ℝ) ≤ growth (balanced k) ∧
    growth (balanced k) ≤ 1000*(k:ℝ))

```

### LiteralDL.FinalStage.unranked_four_claims_expanded

```lean
theorem unranked_four_claims_expanded :
    (∀ k : Nat, 0 < k → ∃ N : Nat, 1 ≤ N ∧
      ∀ q : Unranked, unrankedLeaves q = k → ∀ n : Nat, N ≤ n →
        unrankedCount (shape (balanced k)) n ≤ unrankedCount q n ∧
        unrankedCount q n ≤ unrankedCount (shape (caterpillar k)) n ∧
        (unrankedCount (shape (balanced k)) n = unrankedCount q n ↔
          q = shape (balanced k)) ∧
        (unrankedCount q n = unrankedCount (shape (caterpillar k)) n ↔
          q = shape (caterpillar k))) ∧
    (∀ q : Unranked, 0 < unrankedGrowth q ∧
      Tendsto (fun n : Nat => (unrankedCount q n : ℝ) ^ (1/(n:ℝ)))
        atTop (nhds (unrankedGrowth q)) ∧ unrankedGrowth q = (unrankedRho q)⁻¹) ∧
    Tendsto (fun k : Nat => unrankedGrowth (shape (caterpillar k))/(k:ℝ))
      atTop atTop ∧
    (∀ k : Nat, 0 < k → 2*(k:ℝ) ≤ unrankedGrowth (shape (balanced k)) ∧
      unrankedGrowth (shape (balanced k)) ≤ 1000*(k:ℝ))
```

## Author SELF, read/unread and process record
# Final four-claim assembly handoff v1

AUTHOR IMPLEMENTATION COMPLETE; acceptance pending independent review/replay. No credit claimed or administered. Current campaign72/80 NEW,111 total unchanged.

## Mathematical deliverable

FinalAssembly.source_target (namespace LiteralDL.FinalStage) proves SourceTarget without source, extremum, root-limit or family-bound assumptions. source_four_claims_expanded exposes the canonical actual-cardinality statement; source_event_four_claims_expanded exposes the same statement for literal species-addressed Valid event-tree cardinalities. unranked_four_claims_expanded is the fully expanded quotient statement. uniform_extrema uses max of the two independently proved cutoffs and covers all k-leaf species and all n beyond one N_k>=1, with equality iff the corresponding ShapeIso. Positive real root limits and growth=1/rho are included. Caterpillar growth/k tends to infinity; balanced growth lies between2k and1000k for every positive k. No stronger historical quadratic or80 claim is made.

Three new production modules: FinalSourceTransport, FinalAssembly, FinalExpandedAudit. The 60 cached providers were neither overwritten nor recompiled. Exact own-paper prefix comparison matches all52 balanced sources and all54 growth sources, with common46 identical; SOURCE-APPENDIX-v1.json verifies cached source and olean hashes against the supplied provider map. PREFIX-HASH-MATCH-v1.json is byte custody, not an assertion about the separate Claude reader. No other lane was read or polled.

## Verification and remaining acceptance gates

11/32 formal invocations used, including one failed elaboration and all intermediate compiles/checkers. Every call used frozen check32/checker32, CPU4,5,32GiB AS,6GiB RSS,CPU115/wall130,j1/M3500,warnings-as-errors. FORMAL-RESOURCES-v1.json records commands, hashes, full outputs and telemetry. All three FINAL modules compiled and separately kernel checked. FinalExpandedAudit prints272 named transitive axiom closures, all within propext/Classical.choice/Quot.sound. Runtime reports4.34.1; wrappers enforce pinned executable hashes.

The complete paper appendix mechanically extracts all63 production source files with exact bytes/hashes and verified dependency order. No redundant whole-closure author compilation was performed. Independent semantic review of the new growth8, transport/assembly and full expanded endpoint remains required, as does one fresh paper-only extraction, full closure compile and separate kernel audit under a separately authorized replay allocation. The independent52-prefix review result is not assumed. Root must compare exact source hashes before reusing any reading coverage. These are external acceptance gates, not unproved hypotheses in our theorem.

## Hostile SELF review

Checked: one cutoff shared by both inequalities; finite conjunction over EVERY fixed-k species, not a selected family; all positive k and all n beyond the cutoff; both equality directions; genuine unranked quotient with equality equivalent to ShapeIso; histories retain ordered duplication children and explicit loss/species maps; root limits are real positive actual-count limits; cubic certificate suffices for superlinearity; balanced bound covers odd splits; no asymptotic-equivalent slope or quadratic estimate is smuggled into the result. Quotient descent uses already proved count/rho/growth invariance. Source-event cardinality is tied by an actual equivalence. Expanded endpoints have no residual bridge premise.

Author checks do not certify source fidelity independently, significance, novelty, or literature clearance. Parker's Conditions for Optimality of the Huffman Algorithm remains unread/closed after SIAM robots denial; its precise subsumption risk remains unresolved. Gromada, DMGT companion, homomesy/toggleability, legacy github.com/openai/math and all other named stops remain in force; no body recovery, origin traversal, network/search, prototypes, children, ledger, accounts or credit actions occurred. The common provider producer was UNSEALED; root byte custody does not repair that historical defect or replace independent review.

## Honest reading and process inventory

Personally read full TASK/current model/additional restrictions (initial overlarge output), full three applicable AGENTS across bounded slices, prospective clarification, budgets/reservation/grants/PINS and wrappers/runner/writer; Parker/Gromada named controls and matched legacy/homomesy stops. All own JSON keys/scalars were machine screened recursively; CONTROL-SCREEN-v1 and CONTROL-RESCREEN-v2 preserve exact scope/patterns/matches. Machine screening is not personal reading. Broad host matches do not close unrelated works. The later authenticated-author rescreen does not retroactively repair chronology.

Scientific reading: complete raw342705 record and live target statement projection; title/authors/date metadata; v1 text0:1900,17478:21278,36232:40032,51000:54800,75393:77293; final text60437:62337. Rendered v1 pages4,8,11,16 inspected. A prior source-locate display exceeded the cap and was truncated; exact conjecture passages were subsequently reread in bounded slices. Other source bodies, unrelated control narratives and historical proofs/receipts were not personally read end to end.

Provider/interface reading: SpeciesShapes complete; ShapeTransport complete; ActualRootLimit complete; ThresholdIdentity except final namespace tail; GrowthFinalEndpoint complete; BalancedFinalExtremum through character3800 (exports and proof complete, final print tail unread); SourceHistory0:1900,SourceFiber0:1900,CaterpillarCounts0:1200; EndpointAudit complete. The ordinary caterpillar section of PAPER-v3, balanced ordinary proof in BALANCED-PAPER-v1 and growth ordinary proof in GROWTH-PAPER-v1 were read and integrated. Other provider bodies are copied and hashed, not thereby personally read. Newly authored source/proofs were personally constructed and reviewed.

UNWAIVED current defects: directory inventory preceded the prescribed initial sequence; initial combined controls response exceeded6000 and logical/payload limits; full run.py and combined PINS read exceeded logical slices; source-locate output was oversized/truncated; some payloads exceeded2400; comprehensive normalized author/host/control screening and title metadata authentication occurred after some technical reading; runtime version attestation followed early compiles (binary hashes were enforced from the first wrapper call). One wrong ancestor-path read failed without reading an outside source. Historical defects remain UNWAIVED. No clean-process PASS is asserted.

## Files and closure

FINAL-PAPER-v1.md contains the full ordinary proof, exact expanded endpoint types, literal63-module source appendix in dependency order, pins, imports, provider/source/olean/declaration/axiom maps, prefix byte comparisons, actual formal receipt/resource map and literal build/extraction harness. SOURCE-APPENDIX-v1.json is its structured index. extract_final_paper.py performs independent-of-layout byte extraction into cache/paper-extracted; extraction verification is recorded in paper-extraction and paper-byte-verification receipts. The full formal closure is intentionally not recompiled in this author lane.

After all writes and documentary checks, standalone verify_frozen.py after produces frozen-after.json. Terminal physical sealing enumerates every own-lane physical directory/file, rejects symlinks/special files, hashes every regular file, and excludes exactly FINAL-SHA256-v1.json, final-seal.receipt.json, final-seal.output.txt. The terminal seal invocation produces those three files and is followed by no commands or writes. Its actual outcome, not this prospective description, is authoritative. No resource/mathematical blocker remains for the assigned author assembly; remaining independent acceptance work is explicitly external.

## Complete SOURCE-APPENDIX-v1.json

```json
{
  "dependency_order": [
    "LiteralHistory",
    "SourceHistory",
    "CardinalRecurrence",
    "SourceFiber",
    "DuplicationSkeleton",
    "WeightedSkeleton",
    "LeastFixedPoint",
    "SourceWeighted",
    "AtomMass",
    "EndpointAudit",
    "ScalarBranch",
    "ScalarEvaluation",
    "HistoryEvaluation",
    "BranchRegularity",
    "CatalanAssociator",
    "HistoryOrder",
    "ActualThreshold",
    "ClippedCatalan",
    "CatalanDerivative",
    "RealAssociator",
    "ThresholdFacts",
    "ConjugateSlope",
    "LogFekete",
    "ActualRootLimit",
    "LogConjugateConvex",
    "GeometricBridge",
    "LogConjugateExpansive",
    "ThresholdIdentity",
    "SpeciesShapes",
    "FiniteShapes",
    "StrictChildThreshold",
    "ThresholdUniqueness",
    "ClosureAudit",
    "ShapeTransport",
    "BranchDomain",
    "BranchGlobal",
    "CaterpillarOrder",
    "GrowthFinalBounds",
    "GrowthFinalCaterpillar",
    "GrowthFinalScalar",
    "StrictRotation",
    "GrowthFinalBalanced",
    "StrictMerge",
    "CaterpillarSplit",
    "GrowthFinalAsymptotic",
    "GrowthFinalLimit",
    "StrictExtension",
    "GrowthFinalEndpoint",
    "LeafExpansion",
    "StrictCaterpillar",
    "BalancedExpansion",
    "CaterpillarCounts",
    "BalancedFinalDiscrete",
    "ProgressAudit",
    "BalancedFinalSplit",
    "GrowthFinalAudit",
    "BalancedFinalValues",
    "BalancedFinalOrder",
    "BalancedFinalExtremum",
    "BalancedFinalAudit",
    "FinalSourceTransport",
    "FinalAssembly",
    "FinalExpandedAudit"
  ],
  "modules": {
    "LiteralHistory": {
      "source": "src/LiteralHistory.lean",
      "source_bytes": 5556,
      "source_sha256": "c40f422055fb4dce20d15df8871f649a2e98e1a26ab7b6f9856015eb7e73a97c",
      "olean": "build/LiteralHistory.olean",
      "olean_sha256": "a5de3957f9a788c99b3327e4b70a51795950ca5b3b90d65a299a8956fab97dc5",
      "imports": [
        "Mathlib.Data.Fintype.Card",
        "Mathlib.Data.Fintype.Prod",
        "Mathlib.Data.Fintype.OfMap",
        "Mathlib.Data.Finset.Prod",
        "Mathlib.Tactic.Linarith"
      ],
      "declarations_syntactic": [
        "Species",
        "weight",
        "weight_pos",
        "Hist",
        "size",
        "size_pos",
        "depth",
        "depth_bound",
        "pool",
        "mem_pool",
        "Fiber",
        "fiberFintype",
        "count",
        "duplicate",
        "duplicate_injective",
        "supermultiplicative",
        "fiber_zero_empty",
        "one",
        "positiveFiber",
        "count_pos"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "LiteralHistory",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/LiteralHistory.lean",
        "source_sha256": "c40f422055fb4dce20d15df8871f649a2e98e1a26ab7b6f9856015eb7e73a97c",
        "bytes": 5556,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/LiteralHistory.olean",
        "olean_sha256": "a5de3957f9a788c99b3327e4b70a51795950ca5b3b90d65a299a8956fab97dc5",
        "imports": [
          "Mathlib.Data.Fintype.Card",
          "Mathlib.Data.Fintype.Prod",
          "Mathlib.Data.Fintype.OfMap",
          "Mathlib.Data.Finset.Prod",
          "Mathlib.Tactic.Linarith"
        ]
      }
    },
    "SourceHistory": {
      "source": "src/SourceHistory.lean",
      "source_bytes": 3518,
      "source_sha256": "b7df492ce4f3049440b665cfd106a52127b54247863226220151a484591a9e13",
      "olean": "build/SourceHistory.olean",
      "olean_sha256": "3c0c504ac13c2051241460c054f2018fb735f051442e598d7cc715a38ec8420c",
      "imports": [
        "LiteralHistory"
      ],
      "declarations_syntactic": [
        "Event",
        "EventTree",
        "encode",
        "Valid",
        "encode_valid",
        "valid_has_history",
        "encode_ne_loss",
        "encode_injective",
        "sourceEquiv"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "SourceHistory",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/SourceHistory.lean",
        "source_sha256": "b7df492ce4f3049440b665cfd106a52127b54247863226220151a484591a9e13",
        "bytes": 3518,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/SourceHistory.olean",
        "olean_sha256": "3c0c504ac13c2051241460c054f2018fb735f051442e598d7cc715a38ec8420c",
        "imports": [
          "LiteralHistory"
        ]
      }
    },
    "CardinalRecurrence": {
      "source": "src/CardinalRecurrence.lean",
      "source_bytes": 4086,
      "source_sha256": "410eb8a7ff37d70df547f84c705de81e78fccd5a8b49819a2b3d0cfb114fe977",
      "olean": "build/CardinalRecurrence.olean",
      "olean_sha256": "f026a2037f1cde0ffdfbcbf7dd512fd9058445696f8699b9d858937169f8391e",
      "imports": [
        "SourceHistory",
        "Mathlib.Data.Fintype.Sigma",
        "Mathlib.Data.Fintype.Sum",
        "Mathlib.Data.Fintype.BigOperators"
      ],
      "declarations_syntactic": [
        "PairFiber",
        "Split",
        "splitEquiv",
        "pairFintype",
        "pairCount",
        "NodeRoot",
        "nodeJoin",
        "nodeCut",
        "nodeEquiv",
        "count_node",
        "pairCount_eq",
        "LeafRoot",
        "leafJoin",
        "leafCut",
        "leafEquiv",
        "count_leaf",
        "count_node_convolution"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "CardinalRecurrence",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/CardinalRecurrence.lean",
        "source_sha256": "410eb8a7ff37d70df547f84c705de81e78fccd5a8b49819a2b3d0cfb114fe977",
        "bytes": 4086,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/CardinalRecurrence.olean",
        "olean_sha256": "f026a2037f1cde0ffdfbcbf7dd512fd9058445696f8699b9d858937169f8391e",
        "imports": [
          "SourceHistory",
          "Mathlib.Data.Fintype.Sigma",
          "Mathlib.Data.Fintype.Sum",
          "Mathlib.Data.Fintype.BigOperators"
        ]
      }
    },
    "SourceFiber": {
      "source": "src/SourceFiber.lean",
      "source_bytes": 2303,
      "source_sha256": "06c19bc61776a55a41d4d37870213de34ca94722181953024d9e5f9a6819c748",
      "olean": "build/SourceFiber.olean",
      "olean_sha256": "3c23827e9d06b2c48a63880d4bb8447b6ec15bc27004b229e122516cdd54dc59",
      "imports": [
        "CardinalRecurrence"
      ],
      "declarations_syntactic": [
        "extantCount",
        "encode_size",
        "sourceFiberEquiv",
        "swapRoot",
        "swapRoot_size",
        "swapRoot_twice",
        "swapFiber",
        "count_swap",
        "count_zero"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "SourceFiber",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/SourceFiber.lean",
        "source_sha256": "06c19bc61776a55a41d4d37870213de34ca94722181953024d9e5f9a6819c748",
        "bytes": 2303,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/SourceFiber.olean",
        "olean_sha256": "3c23827e9d06b2c48a63880d4bb8447b6ec15bc27004b229e122516cdd54dc59",
        "imports": [
          "CardinalRecurrence"
        ]
      }
    },
    "DuplicationSkeleton": {
      "source": "src/DuplicationSkeleton.lean",
      "source_bytes": 1762,
      "source_sha256": "99169772c17e784b3a61538feb7ffd50a73ed7157c199a7aeb3f860cb5abc497",
      "olean": "build/DuplicationSkeleton.olean",
      "olean_sha256": "0393db6f795a682ef14d75e9996d8644aec988f1ddf015defc808abd56fba117",
      "imports": [
        "SourceFiber"
      ],
      "declarations_syntactic": [
        "Skeleton",
        "Atom",
        "atomHist",
        "assemble",
        "cutSkeleton",
        "assemble_cut",
        "cut_assemble",
        "skeletonEquiv",
        "skeletonSize",
        "assemble_size"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "DuplicationSkeleton",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/DuplicationSkeleton.lean",
        "source_sha256": "99169772c17e784b3a61538feb7ffd50a73ed7157c199a7aeb3f860cb5abc497",
        "bytes": 1762,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/DuplicationSkeleton.olean",
        "olean_sha256": "0393db6f795a682ef14d75e9996d8644aec988f1ddf015defc808abd56fba117",
        "imports": [
          "SourceFiber"
        ]
      }
    },
    "WeightedSkeleton": {
      "source": "src/WeightedSkeleton.lean",
      "source_bytes": 2041,
      "source_sha256": "ac7cdbbd7f1f70dc59380e1fca6f5993c6e03def31787d8800a40ca2e4c49309",
      "olean": "build/WeightedSkeleton.olean",
      "olean_sha256": "612ed77240027f249bbe4f6328cadce5f3255cdc02a3c07bf3a8e8604f639dfc",
      "imports": [
        "DuplicationSkeleton",
        "Mathlib.Topology.Algebra.InfiniteSum.ENNReal"
      ],
      "declarations_syntactic": [
        "rootEquiv",
        "skWeight",
        "total",
        "total_quadratic",
        "historySum",
        "skWeight_pow",
        "historySum_skeleton"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "WeightedSkeleton",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/WeightedSkeleton.lean",
        "source_sha256": "ac7cdbbd7f1f70dc59380e1fca6f5993c6e03def31787d8800a40ca2e4c49309",
        "bytes": 2041,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/WeightedSkeleton.olean",
        "olean_sha256": "612ed77240027f249bbe4f6328cadce5f3255cdc02a3c07bf3a8e8604f639dfc",
        "imports": [
          "DuplicationSkeleton",
          "Mathlib.Topology.Algebra.InfiniteSum.ENNReal"
        ]
      }
    },
    "LeastFixedPoint": {
      "source": "src/LeastFixedPoint.lean",
      "source_bytes": 2881,
      "source_sha256": "6c5d6b8fb1c9b5eff6d906ff3c8811d2035ca653d1d846c82f2980af20252904",
      "olean": "build/LeastFixedPoint.olean",
      "olean_sha256": "fcdb7a609cb54b99614558accffd44118e2ac102de0e1e39f820775ee2be407f",
      "imports": [
        "WeightedSkeleton"
      ],
      "declarations_syntactic": [
        "skHeight",
        "cutWeight",
        "cutTotal",
        "cutWeight_fork",
        "cutTotal_succ",
        "cutTotal_zero",
        "cutTotal_bound",
        "total_le_of_prefixed"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "LeastFixedPoint",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/LeastFixedPoint.lean",
        "source_sha256": "6c5d6b8fb1c9b5eff6d906ff3c8811d2035ca653d1d846c82f2980af20252904",
        "bytes": 2881,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/LeastFixedPoint.olean",
        "olean_sha256": "fcdb7a609cb54b99614558accffd44118e2ac102de0e1e39f820775ee2be407f",
        "imports": [
          "WeightedSkeleton"
        ]
      }
    },
    "SourceWeighted": {
      "source": "src/SourceWeighted.lean",
      "source_bytes": 1218,
      "source_sha256": "515af092f29045a8f72d60929c699e934ebd7ffad7a71065031efbb548bba240",
      "olean": "build/SourceWeighted.olean",
      "olean_sha256": "03f821b9825c450bec41c9aa43bc76668b262e997aa145d0e1492986aa52c4da",
      "imports": [
        "LeastFixedPoint"
      ],
      "declarations_syntactic": [
        "sizeEquiv",
        "historySum_coeff",
        "historySum_le_of_atom_prefixed"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "SourceWeighted",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/SourceWeighted.lean",
        "source_sha256": "515af092f29045a8f72d60929c699e934ebd7ffad7a71065031efbb548bba240",
        "bytes": 1218,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/SourceWeighted.olean",
        "olean_sha256": "03f821b9825c450bec41c9aa43bc76668b262e997aa145d0e1492986aa52c4da",
        "imports": [
          "LeastFixedPoint"
        ]
      }
    },
    "AtomMass": {
      "source": "src/AtomMass.lean",
      "source_bytes": 1619,
      "source_sha256": "14b9c6e105c9b771aa225ae4ac6758539d9c7f31551f312766dc9e0cab1eba33",
      "olean": "build/AtomMass.olean",
      "olean_sha256": "686c95a73a3674e06734d195a5e0d14e32a6132c98b721e4afd198e6deea57ec",
      "imports": [
        "SourceWeighted"
      ],
      "declarations_syntactic": [
        "atomNodeEquiv",
        "atomMass_node",
        "total_eq_of_mass_eq"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "AtomMass",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/AtomMass.lean",
        "source_sha256": "14b9c6e105c9b771aa225ae4ac6758539d9c7f31551f312766dc9e0cab1eba33",
        "bytes": 1619,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/AtomMass.olean",
        "olean_sha256": "686c95a73a3674e06734d195a5e0d14e32a6132c98b721e4afd198e6deea57ec",
        "imports": [
          "SourceWeighted"
        ]
      }
    },
    "EndpointAudit": {
      "source": "src/EndpointAudit.lean",
      "source_bytes": 2806,
      "source_sha256": "e432baead9010f2c89502100283a0283551c9528eb049dddc26bd9811d1ce713",
      "olean": "build/EndpointAudit.olean",
      "olean_sha256": "d662ac20035971fcdeabe1e558e6d357866e9d2a9dfff28fa9b315b87f107a73",
      "imports": [
        "SourceWeighted"
      ],
      "declarations_syntactic": [],
      "namespace": [],
      "provider": {
        "module": "EndpointAudit",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/EndpointAudit.lean",
        "source_sha256": "e432baead9010f2c89502100283a0283551c9528eb049dddc26bd9811d1ce713",
        "bytes": 2806,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/EndpointAudit.olean",
        "olean_sha256": "d662ac20035971fcdeabe1e558e6d357866e9d2a9dfff28fa9b315b87f107a73",
        "imports": [
          "SourceWeighted"
        ]
      }
    },
    "ScalarBranch": {
      "source": "src/ScalarBranch.lean",
      "source_bytes": 687,
      "source_sha256": "c78303497a7380e33a8b6d16e04f4e84526b5247430fc71794523d5c0ae4e65a",
      "olean": "build/ScalarBranch.olean",
      "olean_sha256": "276fbf91e462218ae56d1944097eafa0eead785460fecc2a266bffdba441ec2c",
      "imports": [
        "AtomMass",
        "Mathlib.Analysis.Real.Sqrt"
      ],
      "declarations_syntactic": [
        "catalanBranch",
        "catalanBranch_properties"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "ScalarBranch",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/ScalarBranch.lean",
        "source_sha256": "c78303497a7380e33a8b6d16e04f4e84526b5247430fc71794523d5c0ae4e65a",
        "bytes": 687,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/ScalarBranch.olean",
        "olean_sha256": "276fbf91e462218ae56d1944097eafa0eead785460fecc2a266bffdba441ec2c",
        "imports": [
          "AtomMass",
          "Mathlib.Analysis.Real.Sqrt"
        ]
      }
    },
    "ScalarEvaluation": {
      "source": "src/ScalarEvaluation.lean",
      "source_bytes": 1644,
      "source_sha256": "98ae402407c7160787ae036fffd0ead5cdb0db8a19b83ca799ca5e4d0fe149b3",
      "olean": "build/ScalarEvaluation.olean",
      "olean_sha256": "c25f09deb1464e18ecb9928d2a3451f48b717b4e33ecd06e81de883a97a35c54",
      "imports": [
        "ScalarBranch"
      ],
      "declarations_syntactic": [
        "total_principal",
        "total_infinite_above"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "ScalarEvaluation",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/ScalarEvaluation.lean",
        "source_sha256": "98ae402407c7160787ae036fffd0ead5cdb0db8a19b83ca799ca5e4d0fe149b3",
        "bytes": 1644,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/ScalarEvaluation.olean",
        "olean_sha256": "c25f09deb1464e18ecb9928d2a3451f48b717b4e33ecd06e81de883a97a35c54",
        "imports": [
          "ScalarBranch"
        ]
      }
    },
    "HistoryEvaluation": {
      "source": "src/HistoryEvaluation.lean",
      "source_bytes": 1402,
      "source_sha256": "8c04464ad6eed77805e9d8d884f9c62d94a5de483e3c431dbae0fffcc43c6eca",
      "olean": "build/HistoryEvaluation.olean",
      "olean_sha256": "b70d6b5dd5c658ecbdaa7195b821e9bab457b8723c3f93f5671ec198ae11572f",
      "imports": [
        "ScalarEvaluation"
      ],
      "declarations_syntactic": [
        "atomMass_leaf",
        "historySum_leaf_principal",
        "historySum_leaf_infinite",
        "historySum_node_principal"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "HistoryEvaluation",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/HistoryEvaluation.lean",
        "source_sha256": "8c04464ad6eed77805e9d8d884f9c62d94a5de483e3c431dbae0fffcc43c6eca",
        "bytes": 1402,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/HistoryEvaluation.olean",
        "olean_sha256": "b70d6b5dd5c658ecbdaa7195b821e9bab457b8723c3f93f5671ec198ae11572f",
        "imports": [
          "ScalarEvaluation"
        ]
      }
    },
    "BranchRegularity": {
      "source": "src/BranchRegularity.lean",
      "source_bytes": 1484,
      "source_sha256": "7ca57947772b15de3737bc28c07ef62616cb91b1172a956fb46ca9458fc63b3f",
      "olean": "build/BranchRegularity.olean",
      "olean_sha256": "90d0b9747b59fb811c6a0f0cba561b556ebc3d1ff2c0116f3af5c1b5ea41db15",
      "imports": [
        "HistoryEvaluation",
        "Mathlib.Topology.Order.IntermediateValue"
      ],
      "declarations_syntactic": [
        "branchValue",
        "continuous_catalanBranch",
        "branchValue_continuous",
        "catalanBranch_zero",
        "catalanBranch_quarter",
        "branchValue_zero",
        "catalanBranch_strictMono"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "BranchRegularity",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/BranchRegularity.lean",
        "source_sha256": "7ca57947772b15de3737bc28c07ef62616cb91b1172a956fb46ca9458fc63b3f",
        "bytes": 1484,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/BranchRegularity.olean",
        "olean_sha256": "90d0b9747b59fb811c6a0f0cba561b556ebc3d1ff2c0116f3af5c1b5ea41db15",
        "imports": [
          "HistoryEvaluation",
          "Mathlib.Topology.Order.IntermediateValue"
        ]
      }
    },
    "CatalanAssociator": {
      "source": "src/CatalanAssociator.lean",
      "source_bytes": 852,
      "source_sha256": "9558b44afc6a606019328be98a17e0096e89a128306ed1c75f8156df2b88ddf8",
      "olean": "build/CatalanAssociator.olean",
      "olean_sha256": "c90d137fe5a19d20ed42f74f017bd1c3817f142abe35a5070df10c16a317f0e6",
      "imports": [
        "BranchRegularity",
        "Mathlib.Tactic.LinearCombination"
      ],
      "declarations_syntactic": [
        "catalan_associator_identity",
        "catalan_associator_strict"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "CatalanAssociator",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/CatalanAssociator.lean",
        "source_sha256": "9558b44afc6a606019328be98a17e0096e89a128306ed1c75f8156df2b88ddf8",
        "bytes": 852,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/CatalanAssociator.olean",
        "olean_sha256": "c90d137fe5a19d20ed42f74f017bd1c3817f142abe35a5070df10c16a317f0e6",
        "imports": [
          "BranchRegularity",
          "Mathlib.Tactic.LinearCombination"
        ]
      }
    },
    "HistoryOrder": {
      "source": "src/HistoryOrder.lean",
      "source_bytes": 1705,
      "source_sha256": "f2969071f4489d94a5c91f978fe54c9793c9f1cc13ef1b68ab070db68b713852",
      "olean": "build/HistoryOrder.olean",
      "olean_sha256": "d2e85497085bcf767fb6d18196766c1d62f6bda7ea2516e2b74ff4cca0838a5a",
      "imports": [
        "BranchRegularity"
      ],
      "declarations_syntactic": [
        "mass_le_total",
        "historySum_node_ge_left",
        "historySum_node_ge_right",
        "historySum_mono",
        "historySum_node_infinite"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "HistoryOrder",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/HistoryOrder.lean",
        "source_sha256": "f2969071f4489d94a5c91f978fe54c9793c9f1cc13ef1b68ab070db68b713852",
        "bytes": 1705,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/HistoryOrder.olean",
        "olean_sha256": "d2e85497085bcf767fb6d18196766c1d62f6bda7ea2516e2b74ff4cca0838a5a",
        "imports": [
          "BranchRegularity"
        ]
      }
    },
    "ActualThreshold": {
      "source": "src/ActualThreshold.lean",
      "source_bytes": 5409,
      "source_sha256": "ee2377e55440b4aeaf494d2d5bc85164d8641e7e35405bd4e3f4d6fd218bd8d0",
      "olean": "build/ActualThreshold.olean",
      "olean_sha256": "d7cfbf38786b6246101988b5c6375e263c34d353d53837e33bd2ac41fdd0d4b8",
      "imports": [
        "HistoryOrder"
      ],
      "declarations_syntactic": [
        "ActualThreshold",
        "leafThreshold",
        "nodeThreshold",
        "actualThreshold"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "ActualThreshold",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/ActualThreshold.lean",
        "source_sha256": "ee2377e55440b4aeaf494d2d5bc85164d8641e7e35405bd4e3f4d6fd218bd8d0",
        "bytes": 5409,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/ActualThreshold.olean",
        "olean_sha256": "d7cfbf38786b6246101988b5c6375e263c34d353d53837e33bd2ac41fdd0d4b8",
        "imports": [
          "HistoryOrder"
        ]
      }
    },
    "ClippedCatalan": {
      "source": "src/ClippedCatalan.lean",
      "source_bytes": 1948,
      "source_sha256": "af77c1f426ed8226fd29a83b872eb0ba7054e5988f711fc022ec5cc18ca49298",
      "olean": "build/ClippedCatalan.olean",
      "olean_sha256": "0eb8999a9733281b16b3a94cebf1b6428b384b2d5a258478b848b53eb789ee5c",
      "imports": [
        "CatalanAssociator"
      ],
      "declarations_syntactic": [
        "catalanBranch_global_bounds",
        "catalanBranch_saturated",
        "catalanBranch_mono",
        "mergeValue",
        "mergeValue_nonneg",
        "mergeValue_half",
        "mergeValue_mono",
        "mergeValue_comm",
        "mergeValue_ge_left"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "ClippedCatalan",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/ClippedCatalan.lean",
        "source_sha256": "af77c1f426ed8226fd29a83b872eb0ba7054e5988f711fc022ec5cc18ca49298",
        "bytes": 1948,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/ClippedCatalan.olean",
        "olean_sha256": "0eb8999a9733281b16b3a94cebf1b6428b384b2d5a258478b848b53eb789ee5c",
        "imports": [
          "CatalanAssociator"
        ]
      }
    },
    "CatalanDerivative": {
      "source": "src/CatalanDerivative.lean",
      "source_bytes": 1575,
      "source_sha256": "04019b62d0775ec340e97c2459555d12522c5f16a9709e725ae2e2e416ee61cf",
      "olean": "build/CatalanDerivative.olean",
      "olean_sha256": "ec771f0bed141bdd35e80840ead677203cc62228606af77a3736faeeb28705b9",
      "imports": [
        "ClippedCatalan",
        "Mathlib.Analysis.SpecialFunctions.Sqrt",
        "Mathlib.Analysis.Convex.Deriv",
        "Mathlib.Analysis.SpecialFunctions.Log.Deriv"
      ],
      "declarations_syntactic": [
        "hasDerivAt_catalanBranch",
        "logConjugate",
        "hasDerivAt_logConjugate"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "CatalanDerivative",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/CatalanDerivative.lean",
        "source_sha256": "04019b62d0775ec340e97c2459555d12522c5f16a9709e725ae2e2e416ee61cf",
        "bytes": 1575,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/CatalanDerivative.olean",
        "olean_sha256": "ec771f0bed141bdd35e80840ead677203cc62228606af77a3736faeeb28705b9",
        "imports": [
          "ClippedCatalan",
          "Mathlib.Analysis.SpecialFunctions.Sqrt",
          "Mathlib.Analysis.Convex.Deriv",
          "Mathlib.Analysis.SpecialFunctions.Log.Deriv"
        ]
      }
    },
    "RealAssociator": {
      "source": "src/RealAssociator.lean",
      "source_bytes": 1776,
      "source_sha256": "c18e24444937abda69bea7466d9dfa3566ff48821dd29b1fcb1aea098d88c94c",
      "olean": "build/RealAssociator.olean",
      "olean_sha256": "48ddfc082310629e0efd8403057e4b2c0b707aca6ac12399336f6cf061b04e5b",
      "imports": [
        "ClippedCatalan"
      ],
      "declarations_syntactic": [
        "mergeValue_associator"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "RealAssociator",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/RealAssociator.lean",
        "source_sha256": "c18e24444937abda69bea7466d9dfa3566ff48821dd29b1fcb1aea098d88c94c",
        "bytes": 1776,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/RealAssociator.olean",
        "olean_sha256": "48ddfc082310629e0efd8403057e4b2c0b707aca6ac12399336f6cf061b04e5b",
        "imports": [
          "ClippedCatalan"
        ]
      }
    },
    "ThresholdFacts": {
      "source": "src/ThresholdFacts.lean",
      "source_bytes": 1561,
      "source_sha256": "d10d2af7884d5f715c6b7f1d08eb4f007e807af97c6fc22808fedf5b16a55be5",
      "olean": "build/ThresholdFacts.olean",
      "olean_sha256": "1bc8b65fbcab85c792e16d99e35d92fa5bcaf024689543e33f094a9c180da900",
      "imports": [
        "ActualThreshold"
      ],
      "declarations_syntactic": [
        "rho",
        "rho_pos",
        "historySum_at_rho",
        "historySum_finite_iff",
        "count_exponential_bound"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "ThresholdFacts",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/ThresholdFacts.lean",
        "source_sha256": "d10d2af7884d5f715c6b7f1d08eb4f007e807af97c6fc22808fedf5b16a55be5",
        "bytes": 1561,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/ThresholdFacts.olean",
        "olean_sha256": "1bc8b65fbcab85c792e16d99e35d92fa5bcaf024689543e33f094a9c180da900",
        "imports": [
          "ActualThreshold"
        ]
      }
    },
    "ConjugateSlope": {
      "source": "src/ConjugateSlope.lean",
      "source_bytes": 2108,
      "source_sha256": "3644958867104896feea7f8b5c163200a14c65c72ffebe7883db445f1c217adb",
      "olean": "build/ConjugateSlope.olean",
      "olean_sha256": "51033178344c6d55d565d2efeaf158829b6933d6107210df6b68661d4aff0acc",
      "imports": [
        "CatalanDerivative"
      ],
      "declarations_syntactic": [
        "conjugateSlope",
        "conjugateSlope_den_pos",
        "conjugateSlope_gt_one",
        "conjugateSlope_strictMono",
        "deriv_logConjugate"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "ConjugateSlope",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/ConjugateSlope.lean",
        "source_sha256": "3644958867104896feea7f8b5c163200a14c65c72ffebe7883db445f1c217adb",
        "bytes": 2108,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/ConjugateSlope.olean",
        "olean_sha256": "51033178344c6d55d565d2efeaf158829b6933d6107210df6b68661d4aff0acc",
        "imports": [
          "CatalanDerivative"
        ]
      }
    },
    "LogFekete": {
      "source": "src/LogFekete.lean",
      "source_bytes": 2416,
      "source_sha256": "15d54f9d7b83b58fe82acabf7a38886c156f9ae7108619f821795c51c6e72095",
      "olean": "build/LogFekete.olean",
      "olean_sha256": "cdcdbd08659f8f3a0dfa8c8fa7bb4f476ecfee3dcef712120a3684bdf8e42274",
      "imports": [
        "ThresholdFacts",
        "Mathlib.Analysis.Subadditive",
        "Mathlib.Analysis.SpecialFunctions.Log.Basic"
      ],
      "declarations_syntactic": [
        "negativeLogCount",
        "count_cast_pos",
        "negativeLogCount_subadditive",
        "negativeLogCount_bddBelow",
        "negativeLogCount_tendsto"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "LogFekete",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/LogFekete.lean",
        "source_sha256": "15d54f9d7b83b58fe82acabf7a38886c156f9ae7108619f821795c51c6e72095",
        "bytes": 2416,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/LogFekete.olean",
        "olean_sha256": "cdcdbd08659f8f3a0dfa8c8fa7bb4f476ecfee3dcef712120a3684bdf8e42274",
        "imports": [
          "ThresholdFacts",
          "Mathlib.Analysis.Subadditive",
          "Mathlib.Analysis.SpecialFunctions.Log.Basic"
        ]
      }
    },
    "ActualRootLimit": {
      "source": "src/ActualRootLimit.lean",
      "source_bytes": 958,
      "source_sha256": "2991e373022b7ff7a9d20b1fbd19bac939b7d2470d3758fbf7f10ba00253ada4",
      "olean": "build/ActualRootLimit.olean",
      "olean_sha256": "9b7fbaac12899ec838b62b2351730a3408ccbe9705a1c4e50887e931aa0f22cb",
      "imports": [
        "LogFekete",
        "Mathlib.Analysis.SpecialFunctions.Pow.Real"
      ],
      "declarations_syntactic": [
        "growth",
        "growth_pos",
        "actual_root_limit"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "ActualRootLimit",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/ActualRootLimit.lean",
        "source_sha256": "2991e373022b7ff7a9d20b1fbd19bac939b7d2470d3758fbf7f10ba00253ada4",
        "bytes": 958,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/ActualRootLimit.olean",
        "olean_sha256": "9b7fbaac12899ec838b62b2351730a3408ccbe9705a1c4e50887e931aa0f22cb",
        "imports": [
          "LogFekete",
          "Mathlib.Analysis.SpecialFunctions.Pow.Real"
        ]
      }
    },
    "LogConjugateConvex": {
      "source": "src/LogConjugateConvex.lean",
      "source_bytes": 2022,
      "source_sha256": "8f13c8201b3f86ff2bbc991b5bef32424058f8194c39dc733fa5312f230f3235",
      "olean": "build/LogConjugateConvex.olean",
      "olean_sha256": "733609ba985404ff12aad6deaf4b588577e3aa121f1f5387365a34eb45ffcddc",
      "imports": [
        "ConjugateSlope"
      ],
      "declarations_syntactic": [
        "conjugate_input_nonneg",
        "conjugate_input_lt",
        "logConjugate_continuousOn",
        "logConjugate_strictConvex"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "LogConjugateConvex",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/LogConjugateConvex.lean",
        "source_sha256": "8f13c8201b3f86ff2bbc991b5bef32424058f8194c39dc733fa5312f230f3235",
        "bytes": 2022,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/LogConjugateConvex.olean",
        "olean_sha256": "733609ba985404ff12aad6deaf4b588577e3aa121f1f5387365a34eb45ffcddc",
        "imports": [
          "ConjugateSlope"
        ]
      }
    },
    "GeometricBridge": {
      "source": "src/GeometricBridge.lean",
      "source_bytes": 1515,
      "source_sha256": "e6fd52f129ea9915ee33243a906bf4a79ff2cf7f40a3eea9ca4feb89b75cd755",
      "olean": "build/GeometricBridge.olean",
      "olean_sha256": "5b402dd6dff3ab0094cdc76c49dedeb78ef004fb30703429128974be954ef5a4",
      "imports": [
        "ActualRootLimit",
        "Mathlib.Analysis.SpecificLimits.Basic"
      ],
      "declarations_syntactic": [
        "count_le_growth_pow",
        "finite_below_growth"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "GeometricBridge",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/GeometricBridge.lean",
        "source_sha256": "e6fd52f129ea9915ee33243a906bf4a79ff2cf7f40a3eea9ca4feb89b75cd755",
        "bytes": 1515,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/GeometricBridge.olean",
        "olean_sha256": "5b402dd6dff3ab0094cdc76c49dedeb78ef004fb30703429128974be954ef5a4",
        "imports": [
          "ActualRootLimit",
          "Mathlib.Analysis.SpecificLimits.Basic"
        ]
      }
    },
    "LogConjugateExpansive": {
      "source": "src/LogConjugateExpansive.lean",
      "source_bytes": 1683,
      "source_sha256": "65ff16048e4059e7fc83d81c9160130d33a93f36ec147c1373d25e38a9c38c4c",
      "olean": "build/LogConjugateExpansive.olean",
      "olean_sha256": "06f5cf8ee8bc5e53d01e6da25b1e93c08a34e50adcf9acc8576cff1c822675b6",
      "imports": [
        "LogConjugateConvex"
      ],
      "declarations_syntactic": [
        "logConjugate_zero",
        "conjugate_branch_interior",
        "logConjugate_minus_id_strictMono",
        "logConjugate_expansive"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "LogConjugateExpansive",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/LogConjugateExpansive.lean",
        "source_sha256": "65ff16048e4059e7fc83d81c9160130d33a93f36ec147c1373d25e38a9c38c4c",
        "bytes": 1683,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/LogConjugateExpansive.olean",
        "olean_sha256": "06f5cf8ee8bc5e53d01e6da25b1e93c08a34e50adcf9acc8576cff1c822675b6",
        "imports": [
          "LogConjugateConvex"
        ]
      }
    },
    "ThresholdIdentity": {
      "source": "src/ThresholdIdentity.lean",
      "source_bytes": 1933,
      "source_sha256": "d8ca6bb8d48881e89fb7f06f1661d72e0317c2c33b64468884790688e377e9bc",
      "olean": "build/ThresholdIdentity.olean",
      "olean_sha256": "544fa211bae41bd492a11f2d520fe252070113d971c8c423a40dcf39ceb2d255",
      "imports": [
        "GeometricBridge"
      ],
      "declarations_syntactic": [
        "growth_mul_rho_le",
        "growth_mul_rho_ge",
        "growth_eq_inv_rho"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "ThresholdIdentity",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/ThresholdIdentity.lean",
        "source_sha256": "d8ca6bb8d48881e89fb7f06f1661d72e0317c2c33b64468884790688e377e9bc",
        "bytes": 1933,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/ThresholdIdentity.olean",
        "olean_sha256": "544fa211bae41bd492a11f2d520fe252070113d971c8c423a40dcf39ceb2d255",
        "imports": [
          "GeometricBridge"
        ]
      }
    },
    "SpeciesShapes": {
      "source": "src/SpeciesShapes.lean",
      "source_bytes": 1482,
      "source_sha256": "5fc19e0d5318e6e3c7aac98c60c45002847b0d4400e9537b6adeb909fa761a28",
      "olean": "build/SpeciesShapes.olean",
      "olean_sha256": "01b866b7f297524155d388c194342df45c64897f71725fc756751a15064349a1",
      "imports": [
        "ThresholdIdentity"
      ],
      "declarations_syntactic": [
        "leaves",
        "leaves_pos",
        "caterpillar",
        "balanced",
        "leaves_caterpillar",
        "leaves_balanced",
        "ShapeIso"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "SpeciesShapes",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/SpeciesShapes.lean",
        "source_sha256": "5fc19e0d5318e6e3c7aac98c60c45002847b0d4400e9537b6adeb909fa761a28",
        "bytes": 1482,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/SpeciesShapes.olean",
        "olean_sha256": "01b866b7f297524155d388c194342df45c64897f71725fc756751a15064349a1",
        "imports": [
          "ThresholdIdentity"
        ]
      }
    },
    "FiniteShapes": {
      "source": "src/FiniteShapes.lean",
      "source_bytes": 1177,
      "source_sha256": "311e58b8603450f8347e21c68d935f8c30fb7f2c333dfc12c56b2349eaa4b16c",
      "olean": "build/FiniteShapes.olean",
      "olean_sha256": "b2aecb34c9e626bbd4458981878010617aad66c054724329bbe09d9e2c5165ff",
      "imports": [
        "SpeciesShapes"
      ],
      "declarations_syntactic": [
        "speciesPool",
        "mem_speciesPool",
        "fixedLeavesFintype"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "FiniteShapes",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/FiniteShapes.lean",
        "source_sha256": "311e58b8603450f8347e21c68d935f8c30fb7f2c333dfc12c56b2349eaa4b16c",
        "bytes": 1177,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/FiniteShapes.olean",
        "olean_sha256": "b2aecb34c9e626bbd4458981878010617aad66c054724329bbe09d9e2c5165ff",
        "imports": [
          "SpeciesShapes"
        ]
      }
    },
    "StrictChildThreshold": {
      "source": "src/StrictChildThreshold.lean",
      "source_bytes": 1798,
      "source_sha256": "928790d737670955732c6f55f34256e0565c0a85f3e291774aae21110829f451",
      "olean": "build/StrictChildThreshold.olean",
      "olean_sha256": "77b76d1ab8e9b4e0f42bcfba34a5ed46de4459776b76187945bac7ef760db3d9",
      "imports": [
        "FiniteShapes"
      ],
      "declarations_syntactic": [
        "historySum_node_quadratic",
        "rho_node_lt_left"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "StrictChildThreshold",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/StrictChildThreshold.lean",
        "source_sha256": "928790d737670955732c6f55f34256e0565c0a85f3e291774aae21110829f451",
        "bytes": 1798,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/StrictChildThreshold.olean",
        "olean_sha256": "77b76d1ab8e9b4e0f42bcfba34a5ed46de4459776b76187945bac7ef760db3d9",
        "imports": [
          "FiniteShapes"
        ]
      }
    },
    "ThresholdUniqueness": {
      "source": "src/ThresholdUniqueness.lean",
      "source_bytes": 896,
      "source_sha256": "4bcceca20683bd6db0a2c65aeb3eee64d4f3512c4cf184c55088c70ca36f09fe",
      "olean": "build/ThresholdUniqueness.olean",
      "olean_sha256": "bf910466837616e0d2ab99f385dc93fd8784a6a3c73239e63ae5e915ba4013bb",
      "imports": [
        "StrictChildThreshold"
      ],
      "declarations_syntactic": [
        "rho_eq_of_historySum_eq",
        "rho_swap",
        "rho_node_lt_right"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "ThresholdUniqueness",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/ThresholdUniqueness.lean",
        "source_sha256": "4bcceca20683bd6db0a2c65aeb3eee64d4f3512c4cf184c55088c70ca36f09fe",
        "bytes": 896,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/ThresholdUniqueness.olean",
        "olean_sha256": "bf910466837616e0d2ab99f385dc93fd8784a6a3c73239e63ae5e915ba4013bb",
        "imports": [
          "StrictChildThreshold"
        ]
      }
    },
    "ClosureAudit": {
      "source": "src/ClosureAudit.lean",
      "source_bytes": 5315,
      "source_sha256": "630ce8302045fafd7c9bc55eda311822fb6f71cf610b0cdde60dbf9529644c07",
      "olean": "build/ClosureAudit.olean",
      "olean_sha256": "bf4c88feb64ede06265be96588ef945cc86ade2f63539393362206442d9b00c1",
      "imports": [
        "ThresholdUniqueness"
      ],
      "declarations_syntactic": [],
      "namespace": [],
      "provider": {
        "module": "ClosureAudit",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/ClosureAudit.lean",
        "source_sha256": "630ce8302045fafd7c9bc55eda311822fb6f71cf610b0cdde60dbf9529644c07",
        "bytes": 5315,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/ClosureAudit.olean",
        "olean_sha256": "bf4c88feb64ede06265be96588ef945cc86ade2f63539393362206442d9b00c1",
        "imports": [
          "ThresholdUniqueness"
        ]
      }
    },
    "ShapeTransport": {
      "source": "src/ShapeTransport.lean",
      "source_bytes": 2326,
      "source_sha256": "b7ab47e12db46b1b9cbdeb67696e1a4d94c957509326a121b10bb44192b0b218",
      "olean": "build/ShapeTransport.olean",
      "olean_sha256": "d390586a24f762052825a54e6f8326737bd52a35ee1488b52663fe830f609691",
      "imports": [
        "FiniteShapes",
        "ThresholdUniqueness"
      ],
      "declarations_syntactic": [
        "ShapeIso.refl",
        "ShapeIso.symm",
        "ShapeIso.trans",
        "count_node_congr",
        "ShapeIso.count_eq",
        "ShapeIso.leaves_eq",
        "ShapeIso.rho_eq"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "ShapeTransport",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/ShapeTransport.lean",
        "source_sha256": "b7ab47e12db46b1b9cbdeb67696e1a4d94c957509326a121b10bb44192b0b218",
        "bytes": 2326,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/ShapeTransport.olean",
        "olean_sha256": "d390586a24f762052825a54e6f8326737bd52a35ee1488b52663fe830f609691",
        "imports": [
          "FiniteShapes",
          "ThresholdUniqueness"
        ]
      }
    },
    "BranchDomain": {
      "source": "src/BranchDomain.lean",
      "source_bytes": 2060,
      "source_sha256": "e18b14b5411d660e2462491a406e3f457560f93ba95ba1caf965f8b8fd5e1ad7",
      "olean": "build/BranchDomain.olean",
      "olean_sha256": "f30ffcf31e09d0c5dc8ddabfc002143044209700095e23496a56459c4975b946",
      "imports": [
        "ShapeTransport"
      ],
      "declarations_syntactic": [
        "branchValue_nonneg",
        "branchValue_pos",
        "branchValue_lt_half",
        "branch_node_quadratic"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "BranchDomain",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/BranchDomain.lean",
        "source_sha256": "e18b14b5411d660e2462491a406e3f457560f93ba95ba1caf965f8b8fd5e1ad7",
        "bytes": 2060,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/BranchDomain.olean",
        "olean_sha256": "f30ffcf31e09d0c5dc8ddabfc002143044209700095e23496a56459c4975b946",
        "imports": [
          "ShapeTransport"
        ]
      }
    },
    "BranchGlobal": {
      "source": "src/BranchGlobal.lean",
      "source_bytes": 1163,
      "source_sha256": "fad4cb732022a2cac389675409bdc280e9febe4b87b223e0d80b9eef48d65ac1",
      "olean": "build/BranchGlobal.olean",
      "olean_sha256": "78dec75234956534df38cf7ae49a59949aeb706de00d378fbc63110f7c59244c",
      "imports": [
        "BranchDomain",
        "RealAssociator"
      ],
      "declarations_syntactic": [
        "branchValue_global_bounds",
        "branchValue_ge_leaf",
        "rho_le_of_global_branch_le"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "BranchGlobal",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/BranchGlobal.lean",
        "source_sha256": "fad4cb732022a2cac389675409bdc280e9febe4b87b223e0d80b9eef48d65ac1",
        "bytes": 1163,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/BranchGlobal.olean",
        "olean_sha256": "78dec75234956534df38cf7ae49a59949aeb706de00d378fbc63110f7c59244c",
        "imports": [
          "BranchDomain",
          "RealAssociator"
        ]
      }
    },
    "CaterpillarOrder": {
      "source": "src/CaterpillarOrder.lean",
      "source_bytes": 1961,
      "source_sha256": "88ec591cc6516889d9bd570a95b958ea90a7dc95d73f33c1a47a95f37cb1b715",
      "olean": "build/CaterpillarOrder.olean",
      "olean_sha256": "6cb0a42951b4e8252857731ce4ee10fc9179b3fd03c5d60b1998f4c7ea7698cb",
      "imports": [
        "BranchGlobal"
      ],
      "declarations_syntactic": [
        "caterpillar_succ",
        "caterpillar_merge_le",
        "branchValue_le_caterpillar",
        "rho_caterpillar_le"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "CaterpillarOrder",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/CaterpillarOrder.lean",
        "source_sha256": "88ec591cc6516889d9bd570a95b958ea90a7dc95d73f33c1a47a95f37cb1b715",
        "bytes": 1961,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/CaterpillarOrder.olean",
        "olean_sha256": "6cb0a42951b4e8252857731ce4ee10fc9179b3fd03c5d60b1998f4c7ea7698cb",
        "imports": [
          "BranchGlobal"
        ]
      }
    },
    "GrowthFinalBounds": {
      "source": "src/GrowthFinalBounds.lean",
      "source_bytes": 1348,
      "source_sha256": "12bfccfaa2c9422929e4744a958bac1ea838a5002ffc212dea7d9199fa42fbe0",
      "olean": "build/GrowthFinalBounds.olean",
      "olean_sha256": "3057f5168e92d58f18ca306e0121f12b0a4f10e14baf96b43256655589d33b57",
      "imports": [
        "BranchGlobal",
        "SpeciesShapes"
      ],
      "declarations_syntactic": [
        "leaf_quadratic",
        "leaf_mass",
        "growth_lower"
      ],
      "namespace": [
        "LiteralDL.GrowthStage"
      ],
      "provider": {
        "module": "GrowthFinalBounds",
        "owner": "dl-history-source-growth-bounds-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-source-growth-bounds-formal-sol-r4/src/GrowthFinalBounds.lean",
        "source_sha256": "12bfccfaa2c9422929e4744a958bac1ea838a5002ffc212dea7d9199fa42fbe0",
        "bytes": 1348,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-source-growth-bounds-formal-sol-r4/build/GrowthFinalBounds.olean",
        "olean_sha256": "3057f5168e92d58f18ca306e0121f12b0a4f10e14baf96b43256655589d33b57",
        "imports": [
          "BranchGlobal",
          "SpeciesShapes"
        ]
      }
    },
    "GrowthFinalCaterpillar": {
      "source": "src/GrowthFinalCaterpillar.lean",
      "source_bytes": 1600,
      "source_sha256": "ea139539772fa7bec96112db8e341dcbe6f51541d6f2aaa8cc9a94c15df6d4c9",
      "olean": "build/GrowthFinalCaterpillar.olean",
      "olean_sha256": "5bd088ffd8857f51b1ecda24df90f2f41f51be35617cb916108ced5d9f231cdd",
      "imports": [
        "GrowthFinalBounds"
      ],
      "declarations_syntactic": [
        "caterpillar_cubic"
      ],
      "namespace": [
        "LiteralDL.GrowthStage"
      ],
      "provider": {
        "module": "GrowthFinalCaterpillar",
        "owner": "dl-history-source-growth-bounds-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-source-growth-bounds-formal-sol-r4/src/GrowthFinalCaterpillar.lean",
        "source_sha256": "ea139539772fa7bec96112db8e341dcbe6f51541d6f2aaa8cc9a94c15df6d4c9",
        "bytes": 1600,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-source-growth-bounds-formal-sol-r4/build/GrowthFinalCaterpillar.olean",
        "olean_sha256": "5bd088ffd8857f51b1ecda24df90f2f41f51be35617cb916108ced5d9f231cdd",
        "imports": [
          "GrowthFinalBounds"
        ]
      }
    },
    "GrowthFinalScalar": {
      "source": "src/GrowthFinalScalar.lean",
      "source_bytes": 1511,
      "source_sha256": "d0416897223297362d45b9e324a630672ef6b0a2bd14b44d97ea6f07d7597564",
      "olean": "build/GrowthFinalScalar.olean",
      "olean_sha256": "f6ed470d7f10a182e13f169d424e0a8162d466472078b7c6da3e7dc3fc3aff42",
      "imports": [
        "GrowthFinalBounds"
      ],
      "declarations_syntactic": [
        "merge_bound"
      ],
      "namespace": [
        "LiteralDL.GrowthStage"
      ],
      "provider": {
        "module": "GrowthFinalScalar",
        "owner": "dl-history-source-growth-bounds-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-source-growth-bounds-formal-sol-r4/src/GrowthFinalScalar.lean",
        "source_sha256": "d0416897223297362d45b9e324a630672ef6b0a2bd14b44d97ea6f07d7597564",
        "bytes": 1511,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-source-growth-bounds-formal-sol-r4/build/GrowthFinalScalar.olean",
        "olean_sha256": "f6ed470d7f10a182e13f169d424e0a8162d466472078b7c6da3e7dc3fc3aff42",
        "imports": [
          "GrowthFinalBounds"
        ]
      }
    },
    "StrictRotation": {
      "source": "src/StrictRotation.lean",
      "source_bytes": 2714,
      "source_sha256": "d116011ba13cd251dca5e1dd50f8c93bac4979eb7253928ffd05e347b47431bd",
      "olean": "build/StrictRotation.olean",
      "olean_sha256": "21012fd8e6bfb59f1cd830f5bd6404f070843a39509f4d476004133722c1e7a0",
      "imports": [
        "CaterpillarOrder"
      ],
      "declarations_syntactic": [
        "branch_node_gt_left",
        "branch_nonleaf_gt_leaf",
        "rho_rotation_le",
        "rho_rotation_lt"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "StrictRotation",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/StrictRotation.lean",
        "source_sha256": "d116011ba13cd251dca5e1dd50f8c93bac4979eb7253928ffd05e347b47431bd",
        "bytes": 2714,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/StrictRotation.olean",
        "olean_sha256": "21012fd8e6bfb59f1cd830f5bd6404f070843a39509f4d476004133722c1e7a0",
        "imports": [
          "CaterpillarOrder"
        ]
      }
    },
    "GrowthFinalBalanced": {
      "source": "src/GrowthFinalBalanced.lean",
      "source_bytes": 2577,
      "source_sha256": "3d5cf75a33baebcb3918712fed0cbe9a973a9b1464f4a30cfbb29a7f41c47dad",
      "olean": "build/GrowthFinalBalanced.olean",
      "olean_sha256": "24db2a1f56abd1a775ebe2e1d803e86a01fa1fdbe77f8fe5890d07c7e62bc102",
      "imports": [
        "GrowthFinalScalar"
      ],
      "declarations_syntactic": [
        "balanced_value_bound"
      ],
      "namespace": [
        "LiteralDL.GrowthStage"
      ],
      "provider": {
        "module": "GrowthFinalBalanced",
        "owner": "dl-history-source-growth-bounds-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-source-growth-bounds-formal-sol-r4/src/GrowthFinalBalanced.lean",
        "source_sha256": "3d5cf75a33baebcb3918712fed0cbe9a973a9b1464f4a30cfbb29a7f41c47dad",
        "bytes": 2577,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-source-growth-bounds-formal-sol-r4/build/GrowthFinalBalanced.olean",
        "olean_sha256": "24db2a1f56abd1a775ebe2e1d803e86a01fa1fdbe77f8fe5890d07c7e62bc102",
        "imports": [
          "GrowthFinalScalar"
        ]
      }
    },
    "StrictMerge": {
      "source": "src/StrictMerge.lean",
      "source_bytes": 2247,
      "source_sha256": "e12731420f4451b6aaaebbdf34441ca29d9fe531269c2f1808415030c4913bfb",
      "olean": "build/StrictMerge.olean",
      "olean_sha256": "cd0df614bfdca7226f053753cb7218f2d43d61c844f7073fba73fcd6538b5e75",
      "imports": [
        "StrictRotation"
      ],
      "declarations_syntactic": [
        "mergeValue_input_lt",
        "mergeValue_strict",
        "mergeValue_associator_lt"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "StrictMerge",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/StrictMerge.lean",
        "source_sha256": "e12731420f4451b6aaaebbdf34441ca29d9fe531269c2f1808415030c4913bfb",
        "bytes": 2247,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/StrictMerge.olean",
        "olean_sha256": "cd0df614bfdca7226f053753cb7218f2d43d61c844f7073fba73fcd6538b5e75",
        "imports": [
          "StrictRotation"
        ]
      }
    },
    "CaterpillarSplit": {
      "source": "src/CaterpillarSplit.lean",
      "source_bytes": 2508,
      "source_sha256": "eb62101fddf96ccccba2001a9cb39f3527ad3ffed1cacefeb57973198a08c15b",
      "olean": "build/CaterpillarSplit.olean",
      "olean_sha256": "8643f288bb1f67da28b188e9804fb5ad4604a216f081060499d210819babc9bc",
      "imports": [
        "StrictMerge"
      ],
      "declarations_syntactic": [
        "caterpillar_ne_leaf",
        "rho_caterpillar_split_lt",
        "caterpillar_merge_lt"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "CaterpillarSplit",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/CaterpillarSplit.lean",
        "source_sha256": "eb62101fddf96ccccba2001a9cb39f3527ad3ffed1cacefeb57973198a08c15b",
        "bytes": 2508,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/CaterpillarSplit.olean",
        "olean_sha256": "8643f288bb1f67da28b188e9804fb5ad4604a216f081060499d210819babc9bc",
        "imports": [
          "StrictMerge"
        ]
      }
    },
    "GrowthFinalAsymptotic": {
      "source": "src/GrowthFinalAsymptotic.lean",
      "source_bytes": 1497,
      "source_sha256": "7e9bb3c2b734972a4142313d5b9447b0dea8ecf1dd3eaf30a3740458259c8aac",
      "olean": "build/GrowthFinalAsymptotic.olean",
      "olean_sha256": "5dc24a5e18042b08b93d75a0b0082b45496ff6621c3b7ae3d5ed1f5c53a01cc3",
      "imports": [
        "GrowthFinalCaterpillar",
        "GrowthFinalBalanced"
      ],
      "declarations_syntactic": [
        "caterpillar_square_lower",
        "balanced_growth_upper"
      ],
      "namespace": [
        "LiteralDL.GrowthStage"
      ],
      "provider": {
        "module": "GrowthFinalAsymptotic",
        "owner": "dl-history-source-growth-bounds-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-source-growth-bounds-formal-sol-r4/src/GrowthFinalAsymptotic.lean",
        "source_sha256": "7e9bb3c2b734972a4142313d5b9447b0dea8ecf1dd3eaf30a3740458259c8aac",
        "bytes": 1497,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-source-growth-bounds-formal-sol-r4/build/GrowthFinalAsymptotic.olean",
        "olean_sha256": "5dc24a5e18042b08b93d75a0b0082b45496ff6621c3b7ae3d5ed1f5c53a01cc3",
        "imports": [
          "GrowthFinalCaterpillar",
          "GrowthFinalBalanced"
        ]
      }
    },
    "GrowthFinalLimit": {
      "source": "src/GrowthFinalLimit.lean",
      "source_bytes": 1408,
      "source_sha256": "72640daa6a5ffcf8a1b4c32e63c0ece819f37a2768c3a441ac7e28d3c069a8b2",
      "olean": "build/GrowthFinalLimit.olean",
      "olean_sha256": "97c021e56d5fd9b5be4bec611e645ebfb6b269a304b3e2215b48ec92601a942f",
      "imports": [
        "GrowthFinalAsymptotic"
      ],
      "declarations_syntactic": [
        "caterpillar_superlinear"
      ],
      "namespace": [
        "LiteralDL.GrowthStage"
      ],
      "provider": {
        "module": "GrowthFinalLimit",
        "owner": "dl-history-source-growth-bounds-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-source-growth-bounds-formal-sol-r4/src/GrowthFinalLimit.lean",
        "source_sha256": "72640daa6a5ffcf8a1b4c32e63c0ece819f37a2768c3a441ac7e28d3c069a8b2",
        "bytes": 1408,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-source-growth-bounds-formal-sol-r4/build/GrowthFinalLimit.olean",
        "olean_sha256": "97c021e56d5fd9b5be4bec611e645ebfb6b269a304b3e2215b48ec92601a942f",
        "imports": [
          "GrowthFinalAsymptotic"
        ]
      }
    },
    "StrictExtension": {
      "source": "src/StrictExtension.lean",
      "source_bytes": 2138,
      "source_sha256": "38e57abce07dbf9b4cafd8a128f2d8d823cabd45a86f3452f39fcfd2ead9cb26",
      "olean": "build/StrictExtension.olean",
      "olean_sha256": "a9950b466128a32b488068bcf2ee83dec859afe6a07d5dc37d582d200d9d9ca6",
      "imports": [
        "CaterpillarSplit"
      ],
      "declarations_syntactic": [
        "ShapeIso.branch_eq",
        "node_input_le_quarter",
        "strict_leaf_extension"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "StrictExtension",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/StrictExtension.lean",
        "source_sha256": "38e57abce07dbf9b4cafd8a128f2d8d823cabd45a86f3452f39fcfd2ead9cb26",
        "bytes": 2138,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/StrictExtension.olean",
        "olean_sha256": "a9950b466128a32b488068bcf2ee83dec859afe6a07d5dc37d582d200d9d9ca6",
        "imports": [
          "CaterpillarSplit"
        ]
      }
    },
    "GrowthFinalEndpoint": {
      "source": "src/GrowthFinalEndpoint.lean",
      "source_bytes": 2504,
      "source_sha256": "bbfa7accf40cc630bf8ac614f358dcda7e3396e6e080af1f1a85b88dc899fb92",
      "olean": "build/GrowthFinalEndpoint.olean",
      "olean_sha256": "494eb677ce221b4bcea1ddb4b4c1848746a2747ead21ac0cba02c9fa73ec597e",
      "imports": [
        "GrowthFinalLimit"
      ],
      "declarations_syntactic": [
        "source_growth_component",
        "auxiliary_conventions",
        "growth_shapeIso",
        "balanced_shape_growth",
        "caterpillar_family_superlinear"
      ],
      "namespace": [
        "LiteralDL.GrowthStage"
      ],
      "provider": {
        "module": "GrowthFinalEndpoint",
        "owner": "dl-history-source-growth-bounds-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-source-growth-bounds-formal-sol-r4/src/GrowthFinalEndpoint.lean",
        "source_sha256": "bbfa7accf40cc630bf8ac614f358dcda7e3396e6e080af1f1a85b88dc899fb92",
        "bytes": 2504,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-source-growth-bounds-formal-sol-r4/build/GrowthFinalEndpoint.olean",
        "olean_sha256": "494eb677ce221b4bcea1ddb4b4c1848746a2747ead21ac0cba02c9fa73ec597e",
        "imports": [
          "GrowthFinalLimit"
        ]
      }
    },
    "LeafExpansion": {
      "source": "src/LeafExpansion.lean",
      "source_bytes": 2321,
      "source_sha256": "419dbdf9c43cb6dd5096f311035930f0219b7aeced926fddf11d56cf29572ffb",
      "olean": "build/LeafExpansion.olean",
      "olean_sha256": "875b7fefcd01b50785773ffbd634786b1fc48d17ff2eb1d6089ffb1077794338",
      "imports": [
        "StrictExtension"
      ],
      "declarations_syntactic": [
        "LeafExpansion",
        "LeafExpansion.global_le",
        "LeafExpansion.strict_value",
        "LeafExpansion.rho_lt"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "LeafExpansion",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/LeafExpansion.lean",
        "source_sha256": "419dbdf9c43cb6dd5096f311035930f0219b7aeced926fddf11d56cf29572ffb",
        "bytes": 2321,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/LeafExpansion.olean",
        "olean_sha256": "875b7fefcd01b50785773ffbd634786b1fc48d17ff2eb1d6089ffb1077794338",
        "imports": [
          "StrictExtension"
        ]
      }
    },
    "StrictCaterpillar": {
      "source": "src/StrictCaterpillar.lean",
      "source_bytes": 2914,
      "source_sha256": "2db213a95a82e9b2211bfe0eba32bdd8e13d9a75a2c0d79e7d1d3bfdc2a113e4",
      "olean": "build/StrictCaterpillar.olean",
      "olean_sha256": "c529d20b87da1f8e7b357450d8b48821524d10fd600f9427307226223c921c4b",
      "imports": [
        "StrictExtension"
      ],
      "declarations_syntactic": [
        "leaves_ge_two_of_nonleaf",
        "caterpillar_dichotomy",
        "rho_caterpillar_strict"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "StrictCaterpillar",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/StrictCaterpillar.lean",
        "source_sha256": "2db213a95a82e9b2211bfe0eba32bdd8e13d9a75a2c0d79e7d1d3bfdc2a113e4",
        "bytes": 2914,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/StrictCaterpillar.olean",
        "olean_sha256": "c529d20b87da1f8e7b357450d8b48821524d10fd600f9427307226223c921c4b",
        "imports": [
          "StrictExtension"
        ]
      }
    },
    "BalancedExpansion": {
      "source": "src/BalancedExpansion.lean",
      "source_bytes": 1242,
      "source_sha256": "dd5831e68ca4948dbb67b25151466d1989b3a5365f6ee5ac7f90703afe066a4f",
      "olean": "build/BalancedExpansion.olean",
      "olean_sha256": "c5dde3a133c2a56dde9cb4fbad61baabd14098a7e40564e3043344d5e99502a3",
      "imports": [
        "LeafExpansion"
      ],
      "declarations_syntactic": [
        "balanced_node",
        "balanced_successor_expansion",
        "rho_balanced_successor_lt"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "BalancedExpansion",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/BalancedExpansion.lean",
        "source_sha256": "dd5831e68ca4948dbb67b25151466d1989b3a5365f6ee5ac7f90703afe066a4f",
        "bytes": 1242,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/BalancedExpansion.olean",
        "olean_sha256": "c5dde3a133c2a56dde9cb4fbad61baabd14098a7e40564e3043344d5e99502a3",
        "imports": [
          "LeafExpansion"
        ]
      }
    },
    "CaterpillarCounts": {
      "source": "src/CaterpillarCounts.lean",
      "source_bytes": 2159,
      "source_sha256": "b7712bb6a212b064edb9882cbc9bff233156b6736d9c8c338d9b34ccae8910df",
      "olean": "build/CaterpillarCounts.olean",
      "olean_sha256": "33510fe5c4559f885626601ddd30ef382b5d55f3d45189afb78333b18a02b3b8",
      "imports": [
        "StrictCaterpillar",
        "Mathlib.Order.Filter.Finite"
      ],
      "declarations_syntactic": [
        "eventual_count_lt_of_growth_lt",
        "eventual_count_lt_of_rho_lt",
        "eventual_caterpillar_maximum"
      ],
      "namespace": [
        "LiteralDL"
      ],
      "provider": {
        "module": "CaterpillarCounts",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/CaterpillarCounts.lean",
        "source_sha256": "b7712bb6a212b064edb9882cbc9bff233156b6736d9c8c338d9b34ccae8910df",
        "bytes": 2159,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/CaterpillarCounts.olean",
        "olean_sha256": "33510fe5c4559f885626601ddd30ef382b5d55f3d45189afb78333b18a02b3b8",
        "imports": [
          "StrictCaterpillar",
          "Mathlib.Order.Filter.Finite"
        ]
      }
    },
    "BalancedFinalDiscrete": {
      "source": "src/BalancedFinalDiscrete.lean",
      "source_bytes": 4179,
      "source_sha256": "e17d676a1f8c19a797ae3b600d3378007a413ec802db98cdc71d38c966ddd7e8",
      "olean": "build/BalancedFinalDiscrete.olean",
      "olean_sha256": "e63f58119855ffa4ac42dbf19c3db07f3e7b44d239b14b710d991ee1d9a06d36",
      "imports": [
        "LogConjugateExpansive",
        "BalancedExpansion"
      ],
      "declarations_syntactic": [
        "strict_midpoint",
        "discrete_convex"
      ],
      "namespace": [
        "LiteralDL.BalancedStage"
      ],
      "provider": {
        "module": "BalancedFinalDiscrete",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/BalancedFinalDiscrete.lean",
        "source_sha256": "e17d676a1f8c19a797ae3b600d3378007a413ec802db98cdc71d38c966ddd7e8",
        "bytes": 4179,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/BalancedFinalDiscrete.olean",
        "olean_sha256": "e63f58119855ffa4ac42dbf19c3db07f3e7b44d239b14b710d991ee1d9a06d36",
        "imports": [
          "LogConjugateExpansive",
          "BalancedExpansion"
        ]
      }
    },
    "ProgressAudit": {
      "source": "src/ProgressAudit.lean",
      "source_bytes": 682,
      "source_sha256": "4b698cacc31ee352c1d0e9c3ece0a922420bfa0f803dca9f79d30e9951733a3a",
      "olean": "build/ProgressAudit.olean",
      "olean_sha256": "118af8dbc22a701061b374420fd406473deb9f84cb637d87264e208f0a723a2f",
      "imports": [
        "ClosureAudit",
        "CaterpillarCounts",
        "BalancedExpansion",
        "LogConjugateExpansive"
      ],
      "declarations_syntactic": [],
      "namespace": [],
      "provider": {
        "module": "ProgressAudit",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/ProgressAudit.lean",
        "source_sha256": "4b698cacc31ee352c1d0e9c3ece0a922420bfa0f803dca9f79d30e9951733a3a",
        "bytes": 682,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/ProgressAudit.olean",
        "olean_sha256": "118af8dbc22a701061b374420fd406473deb9f84cb637d87264e208f0a723a2f",
        "imports": [
          "ClosureAudit",
          "CaterpillarCounts",
          "BalancedExpansion",
          "LogConjugateExpansive"
        ]
      }
    },
    "BalancedFinalSplit": {
      "source": "src/BalancedFinalSplit.lean",
      "source_bytes": 2813,
      "source_sha256": "c599a261ffcce4937f53268a1a7a1b16d0c0c5ffcf50488ea3024a46becb9908",
      "olean": "build/BalancedFinalSplit.olean",
      "olean_sha256": "4cb6d8e0b68fa98e2a8d5a588fefaeffd9b93f61cb1b0af347a7555c2f0557f7",
      "imports": [
        "BalancedFinalDiscrete"
      ],
      "declarations_syntactic": [
        "delta_lt",
        "split_ordered",
        "split_min"
      ],
      "namespace": [
        "LiteralDL.BalancedStage"
      ],
      "provider": {
        "module": "BalancedFinalSplit",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/BalancedFinalSplit.lean",
        "source_sha256": "c599a261ffcce4937f53268a1a7a1b16d0c0c5ffcf50488ea3024a46becb9908",
        "bytes": 2813,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/BalancedFinalSplit.olean",
        "olean_sha256": "4cb6d8e0b68fa98e2a8d5a588fefaeffd9b93f61cb1b0af347a7555c2f0557f7",
        "imports": [
          "BalancedFinalDiscrete"
        ]
      }
    },
    "GrowthFinalAudit": {
      "source": "src/GrowthFinalAudit.lean",
      "source_bytes": 10655,
      "source_sha256": "3286e0f2a23bf8d3afb67af7ef0ea0d5afe2a94bab6c9688fc6acd137f66b5fa",
      "olean": "build/GrowthFinalAudit.olean",
      "olean_sha256": "e167c47d8e0c05902d5d0ef368b1acf490aeb36a2791145dc5d77ee09d0dc248",
      "imports": [
        "ActualRootLimit",
        "ActualThreshold",
        "AtomMass",
        "BalancedExpansion",
        "BranchDomain",
        "BranchGlobal",
        "BranchRegularity",
        "CardinalRecurrence",
        "CatalanAssociator",
        "CatalanDerivative",
        "CaterpillarCounts",
        "CaterpillarOrder",
        "CaterpillarSplit",
        "ClippedCatalan",
        "ClosureAudit",
        "ConjugateSlope",
        "DuplicationSkeleton",
        "EndpointAudit",
        "FiniteShapes",
        "GeometricBridge",
        "GrowthFinalAsymptotic",
        "GrowthFinalBalanced",
        "GrowthFinalBounds",
        "GrowthFinalCaterpillar",
        "GrowthFinalEndpoint",
        "GrowthFinalLimit",
        "GrowthFinalScalar",
        "HistoryEvaluation",
        "HistoryOrder",
        "LeafExpansion",
        "LeastFixedPoint",
        "LiteralHistory",
        "LogConjugateConvex",
        "LogConjugateExpansive",
        "LogFekete",
        "ProgressAudit",
        "RealAssociator",
        "ScalarBranch",
        "ScalarEvaluation",
        "ShapeTransport",
        "SourceFiber",
        "SourceHistory",
        "SourceWeighted",
        "SpeciesShapes",
        "StrictCaterpillar",
        "StrictChildThreshold",
        "StrictExtension",
        "StrictMerge",
        "StrictRotation",
        "ThresholdFacts",
        "ThresholdIdentity",
        "ThresholdUniqueness",
        "WeightedSkeleton"
      ],
      "declarations_syntactic": [],
      "namespace": [],
      "provider": {
        "module": "GrowthFinalAudit",
        "owner": "dl-history-source-growth-bounds-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-source-growth-bounds-formal-sol-r4/src/GrowthFinalAudit.lean",
        "source_sha256": "3286e0f2a23bf8d3afb67af7ef0ea0d5afe2a94bab6c9688fc6acd137f66b5fa",
        "bytes": 10655,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-source-growth-bounds-formal-sol-r4/build/GrowthFinalAudit.olean",
        "olean_sha256": "e167c47d8e0c05902d5d0ef368b1acf490aeb36a2791145dc5d77ee09d0dc248",
        "imports": [
          "ActualRootLimit",
          "ActualThreshold",
          "AtomMass",
          "BalancedExpansion",
          "BranchDomain",
          "BranchGlobal",
          "BranchRegularity",
          "CardinalRecurrence",
          "CatalanAssociator",
          "CatalanDerivative",
          "CaterpillarCounts",
          "CaterpillarOrder",
          "CaterpillarSplit",
          "ClippedCatalan",
          "ClosureAudit",
          "ConjugateSlope",
          "DuplicationSkeleton",
          "EndpointAudit",
          "FiniteShapes",
          "GeometricBridge",
          "GrowthFinalAsymptotic",
          "GrowthFinalBalanced",
          "GrowthFinalBounds",
          "GrowthFinalCaterpillar",
          "GrowthFinalEndpoint",
          "GrowthFinalLimit",
          "GrowthFinalScalar",
          "HistoryEvaluation",
          "HistoryOrder",
          "LeafExpansion",
          "LeastFixedPoint",
          "LiteralHistory",
          "LogConjugateConvex",
          "LogConjugateExpansive",
          "LogFekete",
          "ProgressAudit",
          "RealAssociator",
          "ScalarBranch",
          "ScalarEvaluation",
          "ShapeTransport",
          "SourceFiber",
          "SourceHistory",
          "SourceWeighted",
          "SpeciesShapes",
          "StrictCaterpillar",
          "StrictChildThreshold",
          "StrictExtension",
          "StrictMerge",
          "StrictRotation",
          "ThresholdFacts",
          "ThresholdIdentity",
          "ThresholdUniqueness",
          "WeightedSkeleton"
        ]
      }
    },
    "BalancedFinalValues": {
      "source": "src/BalancedFinalValues.lean",
      "source_bytes": 2880,
      "source_sha256": "561f7ad0145ed7b55edef305989ca31cdeae0cea597cba01440b1aa139d1fa5b",
      "olean": "build/BalancedFinalValues.olean",
      "olean_sha256": "704d0e5c1bbed9622927cd5e37437f4ab5e677d80a1a8e038547f096dcd25470",
      "imports": [
        "BalancedFinalSplit"
      ],
      "declarations_syntactic": [
        "logValue",
        "logValue_nonneg",
        "logValue_pos",
        "exp_logValue",
        "exp_log_pair",
        "logValue_node",
        "logValue_input_mem",
        "balanced_radius_antitone",
        "balanced_log_discrete"
      ],
      "namespace": [
        "LiteralDL.BalancedStage"
      ],
      "provider": {
        "module": "BalancedFinalValues",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/BalancedFinalValues.lean",
        "source_sha256": "561f7ad0145ed7b55edef305989ca31cdeae0cea597cba01440b1aa139d1fa5b",
        "bytes": 2880,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/BalancedFinalValues.olean",
        "olean_sha256": "704d0e5c1bbed9622927cd5e37437f4ab5e677d80a1a8e038547f096dcd25470",
        "imports": [
          "BalancedFinalSplit"
        ]
      }
    },
    "BalancedFinalOrder": {
      "source": "src/BalancedFinalOrder.lean",
      "source_bytes": 4008,
      "source_sha256": "21a68d1ef7f945daaac46e0d9650b496c765bd5d64c6b5ccaa9797d823fb3010",
      "olean": "build/BalancedFinalOrder.olean",
      "olean_sha256": "60acbb84701cbd87bdf9c13f5e3903370606a1b4bda73dfea9b37f1eb2861d84",
      "imports": [
        "BalancedFinalValues"
      ],
      "declarations_syntactic": [
        "conjugate_le",
        "conjugate_eq_iff",
        "log_minimum"
      ],
      "namespace": [
        "LiteralDL.BalancedStage"
      ],
      "provider": {
        "module": "BalancedFinalOrder",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/BalancedFinalOrder.lean",
        "source_sha256": "21a68d1ef7f945daaac46e0d9650b496c765bd5d64c6b5ccaa9797d823fb3010",
        "bytes": 4008,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/BalancedFinalOrder.olean",
        "olean_sha256": "60acbb84701cbd87bdf9c13f5e3903370606a1b4bda73dfea9b37f1eb2861d84",
        "imports": [
          "BalancedFinalValues"
        ]
      }
    },
    "BalancedFinalExtremum": {
      "source": "src/BalancedFinalExtremum.lean",
      "source_bytes": 4070,
      "source_sha256": "02922a6c2a12abfefa648688eec377443533efd42dd45ddc25d0f7163105f9b6",
      "olean": "build/BalancedFinalExtremum.olean",
      "olean_sha256": "c4bcdca2d99490a63a1e649b795c7da390f23e8f5174474d23dd0aa330bdd70c",
      "imports": [
        "BalancedFinalOrder",
        "CaterpillarCounts"
      ],
      "declarations_syntactic": [
        "rho_balanced_strict",
        "rho_balanced_le",
        "rho_balanced_eq_iff",
        "eventual_balanced_minimum",
        "balanced_component"
      ],
      "namespace": [
        "LiteralDL.BalancedStage"
      ],
      "provider": {
        "module": "BalancedFinalExtremum",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/BalancedFinalExtremum.lean",
        "source_sha256": "02922a6c2a12abfefa648688eec377443533efd42dd45ddc25d0f7163105f9b6",
        "bytes": 4070,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/BalancedFinalExtremum.olean",
        "olean_sha256": "c4bcdca2d99490a63a1e649b795c7da390f23e8f5174474d23dd0aa330bdd70c",
        "imports": [
          "BalancedFinalOrder",
          "CaterpillarCounts"
        ]
      }
    },
    "BalancedFinalAudit": {
      "source": "src/BalancedFinalAudit.lean",
      "source_bytes": 11079,
      "source_sha256": "18f1016ece5fb51028d8450c0d1574c875b512bfa363562ad9ce8cad374a5d35",
      "olean": "build/BalancedFinalAudit.olean",
      "olean_sha256": "dd68ab0406cd0122b354ca6572f9d9a2695b686d42263862429f983e2a268e98",
      "imports": [
        "LiteralHistory",
        "SourceHistory",
        "SourceFiber",
        "CardinalRecurrence",
        "DuplicationSkeleton",
        "WeightedSkeleton",
        "LeastFixedPoint",
        "SourceWeighted",
        "EndpointAudit",
        "AtomMass",
        "ScalarBranch",
        "ScalarEvaluation",
        "HistoryEvaluation",
        "BranchRegularity",
        "HistoryOrder",
        "ActualThreshold",
        "ThresholdFacts",
        "LogFekete",
        "ActualRootLimit",
        "GeometricBridge",
        "ThresholdIdentity",
        "SpeciesShapes",
        "FiniteShapes",
        "StrictChildThreshold",
        "ThresholdUniqueness",
        "ClosureAudit",
        "ShapeTransport",
        "CatalanAssociator",
        "BranchDomain",
        "ClippedCatalan",
        "RealAssociator",
        "BranchGlobal",
        "CaterpillarOrder",
        "StrictRotation",
        "StrictMerge",
        "CaterpillarSplit",
        "StrictExtension",
        "StrictCaterpillar",
        "CatalanDerivative",
        "ConjugateSlope",
        "LogConjugateConvex",
        "CaterpillarCounts",
        "LeafExpansion",
        "BalancedExpansion",
        "LogConjugateExpansive",
        "ProgressAudit",
        "BalancedFinalDiscrete",
        "BalancedFinalSplit",
        "BalancedFinalValues",
        "BalancedFinalOrder",
        "BalancedFinalExtremum"
      ],
      "declarations_syntactic": [],
      "namespace": [],
      "provider": {
        "module": "BalancedFinalAudit",
        "owner": "dl-history-balanced-extremum-formal-sol-r4",
        "source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/src/BalancedFinalAudit.lean",
        "source_sha256": "18f1016ece5fb51028d8450c0d1574c875b512bfa363562ad9ce8cad374a5d35",
        "bytes": 11079,
        "olean": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-balanced-extremum-formal-sol-r4/build/BalancedFinalAudit.olean",
        "olean_sha256": "dd68ab0406cd0122b354ca6572f9d9a2695b686d42263862429f983e2a268e98",
        "imports": [
          "LiteralHistory",
          "SourceHistory",
          "SourceFiber",
          "CardinalRecurrence",
          "DuplicationSkeleton",
          "WeightedSkeleton",
          "LeastFixedPoint",
          "SourceWeighted",
          "EndpointAudit",
          "AtomMass",
          "ScalarBranch",
          "ScalarEvaluation",
          "HistoryEvaluation",
          "BranchRegularity",
          "HistoryOrder",
          "ActualThreshold",
          "ThresholdFacts",
          "LogFekete",
          "ActualRootLimit",
          "GeometricBridge",
          "ThresholdIdentity",
          "SpeciesShapes",
          "FiniteShapes",
          "StrictChildThreshold",
          "ThresholdUniqueness",
          "ClosureAudit",
          "ShapeTransport",
          "CatalanAssociator",
          "BranchDomain",
          "ClippedCatalan",
          "RealAssociator",
          "BranchGlobal",
          "CaterpillarOrder",
          "StrictRotation",
          "StrictMerge",
          "CaterpillarSplit",
          "StrictExtension",
          "StrictCaterpillar",
          "CatalanDerivative",
          "ConjugateSlope",
          "LogConjugateConvex",
          "CaterpillarCounts",
          "LeafExpansion",
          "BalancedExpansion",
          "LogConjugateExpansive",
          "ProgressAudit",
          "BalancedFinalDiscrete",
          "BalancedFinalSplit",
          "BalancedFinalValues",
          "BalancedFinalOrder",
          "BalancedFinalExtremum"
        ]
      }
    },
    "FinalSourceTransport": {
      "source": "src/FinalSourceTransport.lean",
      "source_bytes": 1522,
      "source_sha256": "f362114a263c563e6a260c6fd7a04f6dcd0533054c74330a1d1a1af4e65fe4f4",
      "olean": "build/FinalSourceTransport.olean",
      "olean_sha256": "8d97fd354d0162e61c8de0ae3d0fbd0fd9511775fd4399d3548066e111fd03aa",
      "imports": [
        "BalancedFinalExtremum",
        "GrowthFinalEndpoint"
      ],
      "declarations_syntactic": [
        "shapeSetoid",
        "Unranked",
        "shape",
        "shape_eq_iff",
        "unrankedLeaves",
        "unrankedCount",
        "unrankedGrowth",
        "unrankedRho",
        "sourceCard",
        "sourceCard_eq",
        "sourceCard_shape"
      ],
      "namespace": [
        "LiteralDL.FinalStage"
      ],
      "provider": {
        "owner": "this lane"
      }
    },
    "FinalAssembly": {
      "source": "src/FinalAssembly.lean",
      "source_bytes": 6144,
      "source_sha256": "a7cff8d930073705fcf766f77479935c1ff6501c588b53cb83bc6bc0bd16bf7f",
      "olean": "build/FinalAssembly.olean",
      "olean_sha256": "d6193199e343f03d7981500484a58c02bbceee34a59ce3fe67ea1ba5fa752ed6",
      "imports": [
        "FinalSourceTransport"
      ],
      "declarations_syntactic": [
        "uniform_extrema",
        "SourceTarget",
        "source_target",
        "unranked_extrema",
        "unranked_root_limit",
        "source_four_claims_expanded",
        "source_event_four_claims_expanded",
        "balanced_family_linear",
        "caterpillar_family_superlinear",
        "unranked_four_claims_expanded"
      ],
      "namespace": [
        "LiteralDL.FinalStage"
      ],
      "provider": {
        "owner": "this lane"
      }
    },
    "FinalExpandedAudit": {
      "source": "src/FinalExpandedAudit.lean",
      "source_bytes": 11869,
      "source_sha256": "a047ccae1ddfb414834ee6332e87d802a248c34155dd59de53a5d0764b643891",
      "olean": "build/FinalExpandedAudit.olean",
      "olean_sha256": "7876124f7c9a617aa7ee224ffe187c18a44c842bb77ef896ab778bf2c8023ba4",
      "imports": [
        "FinalAssembly",
        "BalancedFinalAudit",
        "GrowthFinalAudit"
      ],
      "declarations_syntactic": [],
      "namespace": [],
      "provider": {
        "owner": "this lane"
      }
    }
  },
  "pins": {
    "lean_version": "4.34.1",
    "mathlib_revision": "d13f23b723b8a846827a245b89c10fc7d3f11612",
    "lean_bin": "/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean",
    "lean_sha256": "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550",
    "leanchecker_bin": "/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/leanchecker",
    "leanchecker_sha256": "ccef1bfe9bfeecea65137d94a69033c1a89f360711f50fa3178e7ba3e696fcbe",
    "packages_root": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages",
    "upstream_lean_paths": [
      "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib/.lake/build/lib/lean",
      "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/batteries/.lake/build/lib/lean",
      "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/aesop/.lake/build/lib/lean",
      "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/Qq/.lake/build/lib/lean",
      "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/proofwidgets/.lake/build/lib/lean",
      "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/importGraph/.lake/build/lib/lean",
      "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/LeanSearchClient/.lake/build/lib/lean",
      "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/plausible/.lake/build/lib/lean"
    ],
    "mathlib_source": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib",
    "mathlib_metadata_sha256": {
      "Mathlib.lean": "61d699d8ace6240934a751f1b1951339090d6e380b505041632227dd7eb73a29",
      "lake-manifest.json": "8f67b2cf24143ac091cdb425e886c2164b2fc2d6fbccd6db9454b697f9541a67"
    },
    "pin_limits": "Root hashed binaries and available upstream source metadata, did NOT execute Lean/git or attest all upstream olean origins. Worker verifies runtime version/pin metadata before compilation; accepted pinned upstream oleans trusted. Never overwrite PINS.json; record discovered verification limits separately."
  },
  "axioms": {
    "LiteralDL.ActualThreshold": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.BalancedStage.balanced_component": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.BalancedStage.balanced_log_discrete": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.BalancedStage.balanced_radius_antitone": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.BalancedStage.conjugate_eq_iff": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.BalancedStage.conjugate_le": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.BalancedStage.delta_lt": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.BalancedStage.discrete_convex": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.BalancedStage.eventual_balanced_minimum": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.BalancedStage.exp_logValue": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.BalancedStage.exp_log_pair": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.BalancedStage.logValue": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.BalancedStage.logValue_input_mem": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.BalancedStage.logValue_node": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.BalancedStage.logValue_nonneg": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.BalancedStage.logValue_pos": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.BalancedStage.log_minimum": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.BalancedStage.rho_balanced_eq_iff": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.BalancedStage.rho_balanced_le": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.BalancedStage.rho_balanced_strict": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.BalancedStage.split_min": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.BalancedStage.split_ordered": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.BalancedStage.strict_midpoint": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.FinalStage.SourceTarget": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.FinalStage.balanced_family_linear": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.FinalStage.caterpillar_family_superlinear": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.FinalStage.shape_eq_iff": [
      "propext",
      "Quot.sound"
    ],
    "LiteralDL.FinalStage.sourceCard": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.FinalStage.sourceCard_eq": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.FinalStage.sourceCard_shape": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.FinalStage.source_event_four_claims_expanded": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.FinalStage.source_four_claims_expanded": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.FinalStage.source_target": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.FinalStage.uniform_extrema": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.FinalStage.unrankedCount": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.FinalStage.unrankedGrowth": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.FinalStage.unrankedLeaves": [
      "propext"
    ],
    "LiteralDL.FinalStage.unrankedRho": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.FinalStage.unranked_extrema": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.FinalStage.unranked_root_limit": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.GrowthStage.auxiliary_conventions": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.GrowthStage.balanced_growth_upper": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.GrowthStage.balanced_shape_growth": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.GrowthStage.balanced_value_bound": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.GrowthStage.caterpillar_cubic": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.GrowthStage.caterpillar_family_superlinear": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.GrowthStage.caterpillar_square_lower": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.GrowthStage.caterpillar_superlinear": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.GrowthStage.growth_lower": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.GrowthStage.growth_shapeIso": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.GrowthStage.leaf_mass": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.GrowthStage.leaf_quadratic": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.GrowthStage.merge_bound": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.GrowthStage.source_growth_component": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.LeafExpansion.global_le": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.LeafExpansion.rho_lt": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.LeafExpansion.strict_value": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.ShapeIso.branch_eq": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.ShapeIso.count_eq": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.ShapeIso.leaves_eq": [
      "propext"
    ],
    "LiteralDL.ShapeIso.rho_eq": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.actualThreshold": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.actual_root_limit": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.assemble_cut": [
      "propext"
    ],
    "LiteralDL.assemble_size": [
      "propext"
    ],
    "LiteralDL.atomMass_leaf": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.atomMass_node": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.balanced": [
      "propext",
      "Quot.sound"
    ],
    "LiteralDL.balanced_node": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.balanced_successor_expansion": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.branchValue": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.branchValue_continuous": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.branchValue_ge_leaf": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.branchValue_global_bounds": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.branchValue_le_caterpillar": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.branchValue_lt_half": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.branchValue_nonneg": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.branchValue_pos": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.branchValue_zero": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.branch_node_gt_left": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.branch_node_quadratic": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.branch_nonleaf_gt_leaf": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.catalanBranch": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.catalanBranch_global_bounds": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.catalanBranch_mono": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.catalanBranch_properties": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.catalanBranch_quarter": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.catalanBranch_saturated": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.catalanBranch_strictMono": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.catalanBranch_zero": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.catalan_associator_identity": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.catalan_associator_strict": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.caterpillar_dichotomy": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.caterpillar_merge_le": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.caterpillar_merge_lt": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.caterpillar_ne_leaf": [
      "propext",
      "Quot.sound"
    ],
    "LiteralDL.caterpillar_succ": [
      "propext",
      "Quot.sound"
    ],
    "LiteralDL.conjugateSlope": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.conjugateSlope_den_pos": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.conjugateSlope_gt_one": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.conjugateSlope_strictMono": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.conjugate_branch_interior": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.conjugate_input_lt": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.conjugate_input_nonneg": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.continuous_catalanBranch": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.count": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.count_cast_pos": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.count_exponential_bound": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.count_le_growth_pow": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.count_leaf": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.count_node": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.count_node_congr": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.count_node_convolution": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.count_pos": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.count_swap": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.count_zero": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.cutTotal": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.cutTotal_bound": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.cutTotal_succ": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.cutTotal_zero": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.cutWeight": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.cutWeight_fork": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.cut_assemble": [
      "propext"
    ],
    "LiteralDL.depth_bound": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.deriv_logConjugate": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.duplicate": [
      "propext"
    ],
    "LiteralDL.duplicate_injective": [
      "propext"
    ],
    "LiteralDL.encode_injective": [
      "propext"
    ],
    "LiteralDL.encode_ne_loss": [
      "propext"
    ],
    "LiteralDL.encode_size": [
      "propext"
    ],
    "LiteralDL.eventual_caterpillar_maximum": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.eventual_count_lt_of_growth_lt": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.eventual_count_lt_of_rho_lt": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.extantCount": [
      "propext"
    ],
    "LiteralDL.fiberFintype": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.fiber_zero_empty": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.finite_below_growth": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.fixedLeavesFintype": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.growth": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.growth_eq_inv_rho": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.growth_mul_rho_ge": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.growth_mul_rho_le": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.growth_pos": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.hasDerivAt_catalanBranch": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.hasDerivAt_logConjugate": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.historySum": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.historySum_at_rho": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.historySum_coeff": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.historySum_finite_iff": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.historySum_le_of_atom_prefixed": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.historySum_leaf_infinite": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.historySum_leaf_principal": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.historySum_mono": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.historySum_node_ge_left": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.historySum_node_ge_right": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.historySum_node_infinite": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.historySum_node_principal": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.historySum_node_quadratic": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.historySum_skeleton": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.leafThreshold": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.leaves_balanced": [
      "propext",
      "Quot.sound"
    ],
    "LiteralDL.leaves_caterpillar": [
      "propext",
      "Quot.sound"
    ],
    "LiteralDL.leaves_ge_two_of_nonleaf": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.leaves_pos": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.logConjugate": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.logConjugate_continuousOn": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.logConjugate_expansive": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.logConjugate_minus_id_strictMono": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.logConjugate_strictConvex": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.logConjugate_zero": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.mass_le_total": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.mem_pool": [
      "propext",
      "Quot.sound"
    ],
    "LiteralDL.mem_speciesPool": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.mergeValue": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.mergeValue_associator": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.mergeValue_associator_lt": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.mergeValue_comm": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.mergeValue_ge_left": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.mergeValue_half": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.mergeValue_input_lt": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.mergeValue_mono": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.mergeValue_nonneg": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.mergeValue_strict": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.negativeLogCount": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.negativeLogCount_bddBelow": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.negativeLogCount_subadditive": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.negativeLogCount_tendsto": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.nodeThreshold": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.node_input_le_quarter": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.pairCount": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.pairCount_eq": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.pairFintype": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.positiveFiber": [
      "propext"
    ],
    "LiteralDL.rho": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.rho_balanced_successor_lt": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.rho_caterpillar_le": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.rho_caterpillar_split_lt": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.rho_caterpillar_strict": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.rho_eq_of_historySum_eq": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.rho_le_of_global_branch_le": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.rho_node_lt_left": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.rho_node_lt_right": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.rho_pos": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.rho_rotation_le": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.rho_rotation_lt": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.rho_swap": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.size_pos": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.skWeight": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.skWeight_pow": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.skeletonEquiv": [
      "propext"
    ],
    "LiteralDL.sourceEquiv": [
      "propext",
      "Classical.choice"
    ],
    "LiteralDL.sourceFiberEquiv": [
      "propext",
      "Classical.choice"
    ],
    "LiteralDL.splitEquiv": [
      "propext",
      "Quot.sound"
    ],
    "LiteralDL.strict_leaf_extension": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.supermultiplicative": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.swapFiber": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.swapRoot": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.swapRoot_size": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.swapRoot_twice": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.total": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.total_eq_of_mass_eq": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.total_infinite_above": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.total_le_of_prefixed": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.total_principal": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.total_quadratic": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.weight_pos": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.FinalStage.unranked_four_claims_expanded": [
      "propext",
      "Classical.choice",
      "Quot.sound"
    ],
    "LiteralDL.Atom": [],
    "LiteralDL.Event": [],
    "LiteralDL.EventTree": [],
    "LiteralDL.Fiber": [],
    "LiteralDL.FinalStage.Unranked": [],
    "LiteralDL.FinalStage.shape": [],
    "LiteralDL.FinalStage.shapeSetoid": [],
    "LiteralDL.Hist": [],
    "LiteralDL.LeafExpansion": [],
    "LiteralDL.LeafRoot": [],
    "LiteralDL.NodeRoot": [],
    "LiteralDL.PairFiber": [],
    "LiteralDL.ShapeIso": [],
    "LiteralDL.ShapeIso.refl": [],
    "LiteralDL.ShapeIso.symm": [],
    "LiteralDL.ShapeIso.trans": [],
    "LiteralDL.Skeleton": [],
    "LiteralDL.Species": [],
    "LiteralDL.Split": [],
    "LiteralDL.Valid": [],
    "LiteralDL.assemble": [],
    "LiteralDL.atomHist": [],
    "LiteralDL.atomNodeEquiv": [],
    "LiteralDL.caterpillar": [],
    "LiteralDL.cutSkeleton": [],
    "LiteralDL.depth": [],
    "LiteralDL.encode": [],
    "LiteralDL.encode_valid": [],
    "LiteralDL.leafCut": [],
    "LiteralDL.leafEquiv": [],
    "LiteralDL.leafJoin": [],
    "LiteralDL.leaves": [],
    "LiteralDL.nodeCut": [],
    "LiteralDL.nodeEquiv": [],
    "LiteralDL.nodeJoin": [],
    "LiteralDL.one": [],
    "LiteralDL.pool": [],
    "LiteralDL.rootEquiv": [],
    "LiteralDL.size": [],
    "LiteralDL.sizeEquiv": [],
    "LiteralDL.skHeight": [],
    "LiteralDL.skeletonSize": [],
    "LiteralDL.speciesPool": [],
    "LiteralDL.valid_has_history": [],
    "LiteralDL.weight": []
  },
  "notes": "60 cached providers reused unchanged; 3 new modules. Author checks only.",
  "scientific_sources": {
    "inputs/1905.04971v1.pdf": {
      "sha256": "26ab46cbf18e79ac1af23b50a34a8a14a51c9fa59bc294d0053299eded69f99b",
      "bytes": 1664214
    },
    "inputs/1905.04971v1.txt": {
      "sha256": "5497dcbb9e3fa96ce906ed21031def487ad1e889533dc62ddacd13389e0b953d",
      "bytes": 104473
    },
    "inputs/PMC7052048.txt": {
      "sha256": "85ecaaaac3e1cad8660fa24861e351a517f4bc87bd77a9558d2cc2ff716227f8",
      "bytes": 93434
    },
    "inputs/mathdb-342705.raw.jsonl": {
      "sha256": "9209561e49f595ec22fe9f2feed20206094001bec60fc2103aeb309814c1db4e",
      "bytes": 2550
    },
    "inputs/live342705-statement-field-release-20261115-v1.json": {
      "sha256": "1a105c85ac0a6a1beb346465520c3424745cbca3e5c772ccbc88735d0a33b0d8",
      "bytes": 3799
    }
  },
  "endpoint_types": {
    "LiteralDL.FinalStage.source_target": "theorem source_target : SourceTarget",
    "LiteralDL.FinalStage.source_four_claims_expanded": "theorem source_four_claims_expanded :\n  (\u2200 k : Nat, 0 < k \u2192 \u2203 N : Nat, 1 \u2264 N \u2227\n    \u2200 s : Species, leaves s = k \u2192 \u2200 n : Nat, N \u2264 n \u2192\n      count (balanced k) n \u2264 count s n \u2227 count s n \u2264 count (caterpillar k) n \u2227\n      (count (balanced k) n = count s n \u2194 ShapeIso s (balanced k)) \u2227\n      (count s n = count (caterpillar k) n \u2194 ShapeIso s (caterpillar k))) \u2227\n  (\u2200 s : Species, 0 < growth s \u2227\n    Tendsto (fun n : Nat => (count s n : \u211d) ^ (1/(n:\u211d))) atTop (nhds (growth s)) \u2227\n    growth s = (rho s)\u207b\u00b9) \u2227\n  Tendsto (fun k : Nat => growth (caterpillar k)/(k:\u211d)) atTop atTop \u2227\n  (\u2200 k : Nat, 0 < k \u2192 2*(k:\u211d) \u2264 growth (balanced k) \u2227\n    growth (balanced k) \u2264 1000*(k:\u211d))\n",
    "LiteralDL.FinalStage.source_event_four_claims_expanded": "theorem source_event_four_claims_expanded :\n  (\u2200 k : Nat, 0 < k \u2192 \u2203 N : Nat, 1 \u2264 N \u2227\n    \u2200 s : Species, leaves s = k \u2192 \u2200 n : Nat, N \u2264 n \u2192\n      sourceCard (balanced k) n \u2264 sourceCard s n \u2227 sourceCard s n \u2264 sourceCard (caterpillar k) n \u2227\n      (sourceCard (balanced k) n = sourceCard s n \u2194 ShapeIso s (balanced k)) \u2227\n      (sourceCard s n = sourceCard (caterpillar k) n \u2194 ShapeIso s (caterpillar k))) \u2227\n  (\u2200 s : Species, 0 < growth s \u2227\n    Tendsto (fun n : Nat => (sourceCard s n : \u211d) ^ (1/(n:\u211d))) atTop (nhds (growth s)) \u2227\n    growth s = (rho s)\u207b\u00b9) \u2227\n  Tendsto (fun k : Nat => growth (caterpillar k)/(k:\u211d)) atTop atTop \u2227\n  (\u2200 k : Nat, 0 < k \u2192 2*(k:\u211d) \u2264 growth (balanced k) \u2227\n    growth (balanced k) \u2264 1000*(k:\u211d))\n",
    "LiteralDL.FinalStage.unranked_four_claims_expanded": "theorem unranked_four_claims_expanded :\n    (\u2200 k : Nat, 0 < k \u2192 \u2203 N : Nat, 1 \u2264 N \u2227\n      \u2200 q : Unranked, unrankedLeaves q = k \u2192 \u2200 n : Nat, N \u2264 n \u2192\n        unrankedCount (shape (balanced k)) n \u2264 unrankedCount q n \u2227\n        unrankedCount q n \u2264 unrankedCount (shape (caterpillar k)) n \u2227\n        (unrankedCount (shape (balanced k)) n = unrankedCount q n \u2194\n          q = shape (balanced k)) \u2227\n        (unrankedCount q n = unrankedCount (shape (caterpillar k)) n \u2194\n          q = shape (caterpillar k))) \u2227\n    (\u2200 q : Unranked, 0 < unrankedGrowth q \u2227\n      Tendsto (fun n : Nat => (unrankedCount q n : \u211d) ^ (1/(n:\u211d)))\n        atTop (nhds (unrankedGrowth q)) \u2227 unrankedGrowth q = (unrankedRho q)\u207b\u00b9) \u2227\n    Tendsto (fun k : Nat => unrankedGrowth (shape (caterpillar k))/(k:\u211d))\n      atTop atTop \u2227\n    (\u2200 k : Nat, 0 < k \u2192 2*(k:\u211d) \u2264 unrankedGrowth (shape (balanced k)) \u2227\n      unrankedGrowth (shape (balanced k)) \u2264 1000*(k:\u211d))"
  },
  "resource_receipt_map": "FORMAL-RESOURCES-v1.json",
  "prefix_match_map": "PREFIX-HASH-MATCH-v1.json",
  "source_urls": {
    "v1": "https://arxiv.org/abs/1905.04971v1",
    "final_owned": "https://pmc.ncbi.nlm.nih.gov/articles/PMC7052048/",
    "target": "https://mathdb.com/p/342705/caterpillar-and-balanced-species-tree-growth-factor-conjectu"
  }
}
```

## Complete PREFIX-HASH-MATCH-v1.json

```json
{
  "paper_source_hashes": {
    "inputs/BALANCED-PAPER-v1.md": {
      "LiteralHistory": "c40f422055fb4dce20d15df8871f649a2e98e1a26ab7b6f9856015eb7e73a97c",
      "SourceHistory": "b7df492ce4f3049440b665cfd106a52127b54247863226220151a484591a9e13",
      "CardinalRecurrence": "410eb8a7ff37d70df547f84c705de81e78fccd5a8b49819a2b3d0cfb114fe977",
      "SourceFiber": "06c19bc61776a55a41d4d37870213de34ca94722181953024d9e5f9a6819c748",
      "DuplicationSkeleton": "99169772c17e784b3a61538feb7ffd50a73ed7157c199a7aeb3f860cb5abc497",
      "WeightedSkeleton": "ac7cdbbd7f1f70dc59380e1fca6f5993c6e03def31787d8800a40ca2e4c49309",
      "LeastFixedPoint": "6c5d6b8fb1c9b5eff6d906ff3c8811d2035ca653d1d846c82f2980af20252904",
      "SourceWeighted": "515af092f29045a8f72d60929c699e934ebd7ffad7a71065031efbb548bba240",
      "EndpointAudit": "e432baead9010f2c89502100283a0283551c9528eb049dddc26bd9811d1ce713",
      "AtomMass": "14b9c6e105c9b771aa225ae4ac6758539d9c7f31551f312766dc9e0cab1eba33",
      "ScalarBranch": "c78303497a7380e33a8b6d16e04f4e84526b5247430fc71794523d5c0ae4e65a",
      "ScalarEvaluation": "98ae402407c7160787ae036fffd0ead5cdb0db8a19b83ca799ca5e4d0fe149b3",
      "HistoryEvaluation": "8c04464ad6eed77805e9d8d884f9c62d94a5de483e3c431dbae0fffcc43c6eca",
      "BranchRegularity": "7ca57947772b15de3737bc28c07ef62616cb91b1172a956fb46ca9458fc63b3f",
      "HistoryOrder": "f2969071f4489d94a5c91f978fe54c9793c9f1cc13ef1b68ab070db68b713852",
      "ActualThreshold": "ee2377e55440b4aeaf494d2d5bc85164d8641e7e35405bd4e3f4d6fd218bd8d0",
      "ThresholdFacts": "d10d2af7884d5f715c6b7f1d08eb4f007e807af97c6fc22808fedf5b16a55be5",
      "LogFekete": "15d54f9d7b83b58fe82acabf7a38886c156f9ae7108619f821795c51c6e72095",
      "ActualRootLimit": "2991e373022b7ff7a9d20b1fbd19bac939b7d2470d3758fbf7f10ba00253ada4",
      "GeometricBridge": "e6fd52f129ea9915ee33243a906bf4a79ff2cf7f40a3eea9ca4feb89b75cd755",
      "ThresholdIdentity": "d8ca6bb8d48881e89fb7f06f1661d72e0317c2c33b64468884790688e377e9bc",
      "SpeciesShapes": "5fc19e0d5318e6e3c7aac98c60c45002847b0d4400e9537b6adeb909fa761a28",
      "FiniteShapes": "311e58b8603450f8347e21c68d935f8c30fb7f2c333dfc12c56b2349eaa4b16c",
      "StrictChildThreshold": "928790d737670955732c6f55f34256e0565c0a85f3e291774aae21110829f451",
      "ThresholdUniqueness": "4bcceca20683bd6db0a2c65aeb3eee64d4f3512c4cf184c55088c70ca36f09fe",
      "ClosureAudit": "630ce8302045fafd7c9bc55eda311822fb6f71cf610b0cdde60dbf9529644c07",
      "ShapeTransport": "b7ab47e12db46b1b9cbdeb67696e1a4d94c957509326a121b10bb44192b0b218",
      "CatalanAssociator": "9558b44afc6a606019328be98a17e0096e89a128306ed1c75f8156df2b88ddf8",
      "BranchDomain": "e18b14b5411d660e2462491a406e3f457560f93ba95ba1caf965f8b8fd5e1ad7",
      "ClippedCatalan": "af77c1f426ed8226fd29a83b872eb0ba7054e5988f711fc022ec5cc18ca49298",
      "RealAssociator": "c18e24444937abda69bea7466d9dfa3566ff48821dd29b1fcb1aea098d88c94c",
      "BranchGlobal": "fad4cb732022a2cac389675409bdc280e9febe4b87b223e0d80b9eef48d65ac1",
      "CaterpillarOrder": "88ec591cc6516889d9bd570a95b958ea90a7dc95d73f33c1a47a95f37cb1b715",
      "StrictRotation": "d116011ba13cd251dca5e1dd50f8c93bac4979eb7253928ffd05e347b47431bd",
      "StrictMerge": "e12731420f4451b6aaaebbdf34441ca29d9fe531269c2f1808415030c4913bfb",
      "CaterpillarSplit": "eb62101fddf96ccccba2001a9cb39f3527ad3ffed1cacefeb57973198a08c15b",
      "StrictExtension": "38e57abce07dbf9b4cafd8a128f2d8d823cabd45a86f3452f39fcfd2ead9cb26",
      "StrictCaterpillar": "2db213a95a82e9b2211bfe0eba32bdd8e13d9a75a2c0d79e7d1d3bfdc2a113e4",
      "CatalanDerivative": "04019b62d0775ec340e97c2459555d12522c5f16a9709e725ae2e2e416ee61cf",
      "ConjugateSlope": "3644958867104896feea7f8b5c163200a14c65c72ffebe7883db445f1c217adb",
      "LogConjugateConvex": "8f13c8201b3f86ff2bbc991b5bef32424058f8194c39dc733fa5312f230f3235",
      "CaterpillarCounts": "b7712bb6a212b064edb9882cbc9bff233156b6736d9c8c338d9b34ccae8910df",
      "LeafExpansion": "419dbdf9c43cb6dd5096f311035930f0219b7aeced926fddf11d56cf29572ffb",
      "BalancedExpansion": "dd5831e68ca4948dbb67b25151466d1989b3a5365f6ee5ac7f90703afe066a4f",
      "LogConjugateExpansive": "65ff16048e4059e7fc83d81c9160130d33a93f36ec147c1373d25e38a9c38c4c",
      "ProgressAudit": "4b698cacc31ee352c1d0e9c3ece0a922420bfa0f803dca9f79d30e9951733a3a",
      "BalancedFinalDiscrete": "e17d676a1f8c19a797ae3b600d3378007a413ec802db98cdc71d38c966ddd7e8",
      "BalancedFinalSplit": "c599a261ffcce4937f53268a1a7a1b16d0c0c5ffcf50488ea3024a46becb9908",
      "BalancedFinalValues": "561f7ad0145ed7b55edef305989ca31cdeae0cea597cba01440b1aa139d1fa5b",
      "BalancedFinalOrder": "21a68d1ef7f945daaac46e0d9650b496c765bd5d64c6b5ccaa9797d823fb3010",
      "BalancedFinalExtremum": "02922a6c2a12abfefa648688eec377443533efd42dd45ddc25d0f7163105f9b6",
      "BalancedFinalAudit": "18f1016ece5fb51028d8450c0d1574c875b512bfa363562ad9ce8cad374a5d35"
    },
    "inputs/GROWTH-PAPER-v1.md": {
      "LiteralHistory": "c40f422055fb4dce20d15df8871f649a2e98e1a26ab7b6f9856015eb7e73a97c",
      "SourceHistory": "b7df492ce4f3049440b665cfd106a52127b54247863226220151a484591a9e13",
      "CardinalRecurrence": "410eb8a7ff37d70df547f84c705de81e78fccd5a8b49819a2b3d0cfb114fe977",
      "SourceFiber": "06c19bc61776a55a41d4d37870213de34ca94722181953024d9e5f9a6819c748",
      "DuplicationSkeleton": "99169772c17e784b3a61538feb7ffd50a73ed7157c199a7aeb3f860cb5abc497",
      "WeightedSkeleton": "ac7cdbbd7f1f70dc59380e1fca6f5993c6e03def31787d8800a40ca2e4c49309",
      "LeastFixedPoint": "6c5d6b8fb1c9b5eff6d906ff3c8811d2035ca653d1d846c82f2980af20252904",
      "SourceWeighted": "515af092f29045a8f72d60929c699e934ebd7ffad7a71065031efbb548bba240",
      "AtomMass": "14b9c6e105c9b771aa225ae4ac6758539d9c7f31551f312766dc9e0cab1eba33",
      "ScalarBranch": "c78303497a7380e33a8b6d16e04f4e84526b5247430fc71794523d5c0ae4e65a",
      "ScalarEvaluation": "98ae402407c7160787ae036fffd0ead5cdb0db8a19b83ca799ca5e4d0fe149b3",
      "HistoryEvaluation": "8c04464ad6eed77805e9d8d884f9c62d94a5de483e3c431dbae0fffcc43c6eca",
      "BranchRegularity": "7ca57947772b15de3737bc28c07ef62616cb91b1172a956fb46ca9458fc63b3f",
      "HistoryOrder": "f2969071f4489d94a5c91f978fe54c9793c9f1cc13ef1b68ab070db68b713852",
      "ActualThreshold": "ee2377e55440b4aeaf494d2d5bc85164d8641e7e35405bd4e3f4d6fd218bd8d0",
      "ThresholdFacts": "d10d2af7884d5f715c6b7f1d08eb4f007e807af97c6fc22808fedf5b16a55be5",
      "LogFekete": "15d54f9d7b83b58fe82acabf7a38886c156f9ae7108619f821795c51c6e72095",
      "ActualRootLimit": "2991e373022b7ff7a9d20b1fbd19bac939b7d2470d3758fbf7f10ba00253ada4",
      "GeometricBridge": "e6fd52f129ea9915ee33243a906bf4a79ff2cf7f40a3eea9ca4feb89b75cd755",
      "ThresholdIdentity": "d8ca6bb8d48881e89fb7f06f1661d72e0317c2c33b64468884790688e377e9bc",
      "SpeciesShapes": "5fc19e0d5318e6e3c7aac98c60c45002847b0d4400e9537b6adeb909fa761a28",
      "FiniteShapes": "311e58b8603450f8347e21c68d935f8c30fb7f2c333dfc12c56b2349eaa4b16c",
      "StrictChildThreshold": "928790d737670955732c6f55f34256e0565c0a85f3e291774aae21110829f451",
      "ThresholdUniqueness": "4bcceca20683bd6db0a2c65aeb3eee64d4f3512c4cf184c55088c70ca36f09fe",
      "ShapeTransport": "b7ab47e12db46b1b9cbdeb67696e1a4d94c957509326a121b10bb44192b0b218",
      "BranchDomain": "e18b14b5411d660e2462491a406e3f457560f93ba95ba1caf965f8b8fd5e1ad7",
      "CatalanAssociator": "9558b44afc6a606019328be98a17e0096e89a128306ed1c75f8156df2b88ddf8",
      "ClippedCatalan": "af77c1f426ed8226fd29a83b872eb0ba7054e5988f711fc022ec5cc18ca49298",
      "RealAssociator": "c18e24444937abda69bea7466d9dfa3566ff48821dd29b1fcb1aea098d88c94c",
      "BranchGlobal": "fad4cb732022a2cac389675409bdc280e9febe4b87b223e0d80b9eef48d65ac1",
      "CaterpillarOrder": "88ec591cc6516889d9bd570a95b958ea90a7dc95d73f33c1a47a95f37cb1b715",
      "StrictRotation": "d116011ba13cd251dca5e1dd50f8c93bac4979eb7253928ffd05e347b47431bd",
      "StrictMerge": "e12731420f4451b6aaaebbdf34441ca29d9fe531269c2f1808415030c4913bfb",
      "CaterpillarSplit": "eb62101fddf96ccccba2001a9cb39f3527ad3ffed1cacefeb57973198a08c15b",
      "StrictExtension": "38e57abce07dbf9b4cafd8a128f2d8d823cabd45a86f3452f39fcfd2ead9cb26",
      "LeafExpansion": "419dbdf9c43cb6dd5096f311035930f0219b7aeced926fddf11d56cf29572ffb",
      "BalancedExpansion": "dd5831e68ca4948dbb67b25151466d1989b3a5365f6ee5ac7f90703afe066a4f",
      "CatalanDerivative": "04019b62d0775ec340e97c2459555d12522c5f16a9709e725ae2e2e416ee61cf",
      "StrictCaterpillar": "2db213a95a82e9b2211bfe0eba32bdd8e13d9a75a2c0d79e7d1d3bfdc2a113e4",
      "CaterpillarCounts": "b7712bb6a212b064edb9882cbc9bff233156b6736d9c8c338d9b34ccae8910df",
      "ClosureAudit": "630ce8302045fafd7c9bc55eda311822fb6f71cf610b0cdde60dbf9529644c07",
      "ConjugateSlope": "3644958867104896feea7f8b5c163200a14c65c72ffebe7883db445f1c217adb",
      "EndpointAudit": "e432baead9010f2c89502100283a0283551c9528eb049dddc26bd9811d1ce713",
      "GrowthFinalBounds": "12bfccfaa2c9422929e4744a958bac1ea838a5002ffc212dea7d9199fa42fbe0",
      "GrowthFinalCaterpillar": "ea139539772fa7bec96112db8e341dcbe6f51541d6f2aaa8cc9a94c15df6d4c9",
      "GrowthFinalScalar": "d0416897223297362d45b9e324a630672ef6b0a2bd14b44d97ea6f07d7597564",
      "GrowthFinalBalanced": "3d5cf75a33baebcb3918712fed0cbe9a973a9b1464f4a30cfbb29a7f41c47dad",
      "GrowthFinalAsymptotic": "7e9bb3c2b734972a4142313d5b9447b0dea8ecf1dd3eaf30a3740458259c8aac",
      "GrowthFinalLimit": "72640daa6a5ffcf8a1b4c32e63c0ece819f37a2768c3a441ac7e28d3c069a8b2",
      "GrowthFinalEndpoint": "bbfa7accf40cc630bf8ac614f358dcda7e3396e6e080af1f1a85b88dc899fb92",
      "LogConjugateConvex": "8f13c8201b3f86ff2bbc991b5bef32424058f8194c39dc733fa5312f230f3235",
      "LogConjugateExpansive": "65ff16048e4059e7fc83d81c9160130d33a93f36ec147c1373d25e38a9c38c4c",
      "ProgressAudit": "4b698cacc31ee352c1d0e9c3ece0a922420bfa0f803dca9f79d30e9951733a3a",
      "GrowthFinalAudit": "3286e0f2a23bf8d3afb67af7ef0ea0d5afe2a94bab6c9688fc6acd137f66b5fa"
    }
  },
  "common46": [
    "ActualRootLimit",
    "ActualThreshold",
    "AtomMass",
    "BalancedExpansion",
    "BranchDomain",
    "BranchGlobal",
    "BranchRegularity",
    "CardinalRecurrence",
    "CatalanAssociator",
    "CatalanDerivative",
    "CaterpillarCounts",
    "CaterpillarOrder",
    "CaterpillarSplit",
    "ClippedCatalan",
    "ClosureAudit",
    "ConjugateSlope",
    "DuplicationSkeleton",
    "EndpointAudit",
    "FiniteShapes",
    "GeometricBridge",
    "HistoryEvaluation",
    "HistoryOrder",
    "LeafExpansion",
    "LeastFixedPoint",
    "LiteralHistory",
    "LogConjugateConvex",
    "LogConjugateExpansive",
    "LogFekete",
    "ProgressAudit",
    "RealAssociator",
    "ScalarBranch",
    "ScalarEvaluation",
    "ShapeTransport",
    "SourceFiber",
    "SourceHistory",
    "SourceWeighted",
    "SpeciesShapes",
    "StrictCaterpillar",
    "StrictChildThreshold",
    "StrictExtension",
    "StrictMerge",
    "StrictRotation",
    "ThresholdFacts",
    "ThresholdIdentity",
    "ThresholdUniqueness",
    "WeightedSkeleton"
  ],
  "status": "exact bytes match; not independent reading attestation"
}
```

## Complete FORMAL-RESOURCES-v1.json

```json
{
  "used": 11,
  "limit": 32,
  "remaining": 21,
  "no_scientific_prototypes": true,
  "calls": [
    {
      "receipt": "f01-transport.receipt.json",
      "receipt_sha256": "03c422ab96c417ccb53ec8caf4ec3b991aecb2efee676b4604a07f156d9afd1b",
      "stdout": "f01-transport.output.txt",
      "stdout_sha256": "fb48ef4834c5beca85a001521c9136f616a515d77f995526f7c583ff9cdd760b",
      "resource": {
        "utc": "2026-11-15T23:10:28.710169+00:00",
        "name": "f01-transport",
        "cwd": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-four-claim-final-assembly-formal-sol-r5",
        "command": [
          "/usr/bin/python3",
          "-I",
          "-B",
          "-c",
          "import os,resource; os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(115,115)); resource.setrlimit(resource.RLIMIT_AS,(32*1024**3,32*1024**3));\nimport os,runpy\nrunpy.run_path(os.path.join(os.environ[\"FORMAL_ROOT\"],\"formal_command.py\"),run_name=\"__main__\")\n"
        ],
        "env_overrides": {
          "MALLOC_ARENA_MAX": "2"
        },
        "affinity": [
          4,
          5
        ],
        "cpu_limit_s": 115,
        "as_limit_bytes": 34359738368,
        "group_rss_guard_bytes": 6442450944,
        "deadline_s": 130,
        "wall_s": 1.1506358109181747,
        "sampled_group_rss_peak_bytes": 2842894336,
        "sampled_max_process_vmpeak_bytes": 7678930944,
        "samples": 13,
        "exit": 1,
        "killed": null,
        "child_cpu_cumulative_s": 1.145274,
        "stderr": ""
      },
      "stage": {
        "stage": "compile",
        "module": "FinalSourceTransport",
        "argv": [
          "/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean",
          "-j1",
          "-M3500",
          "-DwarningAsError=true",
          "-o",
          "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-four-claim-final-assembly-formal-sol-r5/build/FinalSourceTransport.olean",
          "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-four-claim-final-assembly-formal-sol-r5/src/FinalSourceTransport.lean"
        ],
        "exit": 1,
        "source_sha256_before": "ecd061f775f25320085c33211987700e7e628c3d6b8f3c38ba0cbe638e848b5e",
        "source_sha256_after": "ecd061f775f25320085c33211987700e7e628c3d6b8f3c38ba0cbe638e848b5e",
        "olean_sha256_before": null,
        "olean_sha256_after": null,
        "LEAN_PATH": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-four-claim-final-assembly-formal-sol-r5/build:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/batteries/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/aesop/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/Qq/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/importGraph/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/plausible/.lake/build/lib/lean",
        "LEAN_NUM_THREADS": 1
      }
    },
    {
      "receipt": "f02-transport.receipt.json",
      "receipt_sha256": "545b7e3e0ad91780a9984697478fc582604e0e256e2eae409be965fd3dc2c560",
      "stdout": "f02-transport.output.txt",
      "stdout_sha256": "a81fd7b8c2fcb0310ad348a392f21c215332d315fa5d68f1910303eec257837d",
      "resource": {
        "utc": "2026-11-15T23:10:55.829633+00:00",
        "name": "f02-transport",
        "cwd": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-four-claim-final-assembly-formal-sol-r5",
        "command": [
          "/usr/bin/python3",
          "-I",
          "-B",
          "-c",
          "import os,resource; os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(115,115)); resource.setrlimit(resource.RLIMIT_AS,(32*1024**3,32*1024**3));\nimport os,runpy\nrunpy.run_path(os.path.join(os.environ[\"FORMAL_ROOT\"],\"formal_command.py\"),run_name=\"__main__\")\n"
        ],
        "env_overrides": {
          "MALLOC_ARENA_MAX": "2"
        },
        "affinity": [
          4,
          5
        ],
        "cpu_limit_s": 115,
        "as_limit_bytes": 34359738368,
        "group_rss_guard_bytes": 6442450944,
        "deadline_s": 130,
        "wall_s": 1.1805979830678552,
        "sampled_group_rss_peak_bytes": 2843230208,
        "sampled_max_process_vmpeak_bytes": 7678930944,
        "samples": 14,
        "exit": 0,
        "killed": null,
        "child_cpu_cumulative_s": 1.17388,
        "stderr": ""
      },
      "stage": {
        "stage": "compile",
        "module": "FinalSourceTransport",
        "argv": [
          "/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean",
          "-j1",
          "-M3500",
          "-DwarningAsError=true",
          "-o",
          "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-four-claim-final-assembly-formal-sol-r5/build/FinalSourceTransport.olean",
          "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-four-claim-final-assembly-formal-sol-r5/src/FinalSourceTransport.lean"
        ],
        "exit": 0,
        "source_sha256_before": "f362114a263c563e6a260c6fd7a04f6dcd0533054c74330a1d1a1af4e65fe4f4",
        "source_sha256_after": "f362114a263c563e6a260c6fd7a04f6dcd0533054c74330a1d1a1af4e65fe4f4",
        "olean_sha256_before": null,
        "olean_sha256_after": "8d97fd354d0162e61c8de0ae3d0fbd0fd9511775fd4399d3548066e111fd03aa",
        "LEAN_PATH": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-four-claim-final-assembly-formal-sol-r5/build:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/batteries/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/aesop/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/Qq/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/importGraph/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/plausible/.lake/build/lib/lean",
        "LEAN_NUM_THREADS": 1
      }
    },
    {
      "receipt": "f03-assembly.receipt.json",
      "receipt_sha256": "136dbc5cb70cc76e15fe21aae762554dd381b4ebf02a1f56ee2e9e0f6831107d",
      "stdout": "f03-assembly.output.txt",
      "stdout_sha256": "20bd1941779852f421576d2b46f788729a2852f8db17c68299cf688d202ba47f",
      "resource": {
        "utc": "2026-11-15T23:11:46.519359+00:00",
        "name": "f03-assembly",
        "cwd": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-four-claim-final-assembly-formal-sol-r5",
        "command": [
          "/usr/bin/python3",
          "-I",
          "-B",
          "-c",
          "import os,resource; os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(115,115)); resource.setrlimit(resource.RLIMIT_AS,(32*1024**3,32*1024**3));\nimport os,runpy\nrunpy.run_path(os.path.join(os.environ[\"FORMAL_ROOT\"],\"formal_command.py\"),run_name=\"__main__\")\n"
        ],
        "env_overrides": {
          "MALLOC_ARENA_MAX": "2"
        },
        "affinity": [
          4,
          5
        ],
        "cpu_limit_s": 115,
        "as_limit_bytes": 34359738368,
        "group_rss_guard_bytes": 6442450944,
        "deadline_s": 130,
        "wall_s": 1.2440142889972776,
        "sampled_group_rss_peak_bytes": 2839044096,
        "sampled_max_process_vmpeak_bytes": 7678967808,
        "samples": 14,
        "exit": 0,
        "killed": null,
        "child_cpu_cumulative_s": 1.2361909999999998,
        "stderr": ""
      },
      "stage": {
        "stage": "compile",
        "module": "FinalAssembly",
        "argv": [
          "/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean",
          "-j1",
          "-M3500",
          "-DwarningAsError=true",
          "-o",
          "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-four-claim-final-assembly-formal-sol-r5/build/FinalAssembly.olean",
          "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-four-claim-final-assembly-formal-sol-r5/src/FinalAssembly.lean"
        ],
        "exit": 0,
        "source_sha256_before": "563fa30dd88bc86ee9aa155f21bbc6ee02bf81e946e03433ac0caa4d5f832417",
        "source_sha256_after": "563fa30dd88bc86ee9aa155f21bbc6ee02bf81e946e03433ac0caa4d5f832417",
        "olean_sha256_before": null,
        "olean_sha256_after": "7b2c0f17b7e32bbd36fd12d2fe36c5a69f67f4cc60b7ea6cf2a45954fc3cc1cf",
        "LEAN_PATH": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-four-claim-final-assembly-formal-sol-r5/build:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/batteries/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/aesop/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/Qq/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/importGraph/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/plausible/.lake/build/lib/lean",
        "LEAN_NUM_THREADS": 1
      }
    },
    {
      "receipt": "f04-audit.receipt.json",
      "receipt_sha256": "09ce44c8d71594c9cc04bf82f502731b67b5937b4e34de8bfaf8948504da1d18",
      "stdout": "f04-audit.output.txt",
      "stdout_sha256": "75c59d7cd3e798dbf946d979af56d95cf431911eb59ca19605ad5f6bf2baac83",
      "resource": {
        "utc": "2026-11-15T23:12:25.055977+00:00",
        "name": "f04-audit",
        "cwd": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-four-claim-final-assembly-formal-sol-r5",
        "command": [
          "/usr/bin/python3",
          "-I",
          "-B",
          "-c",
          "import os,resource; os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(115,115)); resource.setrlimit(resource.RLIMIT_AS,(32*1024**3,32*1024**3));\nimport os,runpy\nrunpy.run_path(os.path.join(os.environ[\"FORMAL_ROOT\"],\"formal_command.py\"),run_name=\"__main__\")\n"
        ],
        "env_overrides": {
          "MALLOC_ARENA_MAX": "2"
        },
        "affinity": [
          4,
          5
        ],
        "cpu_limit_s": 115,
        "as_limit_bytes": 34359738368,
        "group_rss_guard_bytes": 6442450944,
        "deadline_s": 130,
        "wall_s": 1.2642319860169664,
        "sampled_group_rss_peak_bytes": 2833866752,
        "sampled_max_process_vmpeak_bytes": 7679090688,
        "samples": 15,
        "exit": 0,
        "killed": null,
        "child_cpu_cumulative_s": 1.2514159999999999,
        "stderr": ""
      },
      "stage": {
        "stage": "compile",
        "module": "FinalExpandedAudit",
        "argv": [
          "/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean",
          "-j1",
          "-M3500",
          "-DwarningAsError=true",
          "-o",
          "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-four-claim-final-assembly-formal-sol-r5/build/FinalExpandedAudit.olean",
          "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-four-claim-final-assembly-formal-sol-r5/src/FinalExpandedAudit.lean"
        ],
        "exit": 0,
        "source_sha256_before": "1df56f9ef320b414ae4e22231f0b210d234e65faa73da6f6df8210fc01cdd79b",
        "source_sha256_after": "1df56f9ef320b414ae4e22231f0b210d234e65faa73da6f6df8210fc01cdd79b",
        "olean_sha256_before": null,
        "olean_sha256_after": "7876124f7c9a617aa7ee224ffe187c18a44c842bb77ef896ab778bf2c8023ba4",
        "LEAN_PATH": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-four-claim-final-assembly-formal-sol-r5/build:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/batteries/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/aesop/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/Qq/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/importGraph/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/plausible/.lake/build/lib/lean",
        "LEAN_NUM_THREADS": 1
      }
    },
    {
      "receipt": "f05-transport-kernel.receipt.json",
      "receipt_sha256": "ce5528aef493a39d5a98f224446ecbd1c0ac113b6bdd6d23e064497967ff8db7",
      "stdout": "f05-transport-kernel.output.txt",
      "stdout_sha256": "0673eb57e3488388f178378e2a1670a10fd4a0ce63ca71320f5275b5cb9d3f87",
      "resource": {
        "utc": "2026-11-15T23:12:57.454236+00:00",
        "name": "f05-transport-kernel",
        "cwd": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-four-claim-final-assembly-formal-sol-r5",
        "command": [
          "/usr/bin/python3",
          "-I",
          "-B",
          "-c",
          "import os,resource; os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(115,115)); resource.setrlimit(resource.RLIMIT_AS,(32*1024**3,32*1024**3));\nimport os,runpy\nrunpy.run_path(os.path.join(os.environ[\"FORMAL_ROOT\"],\"formal_command.py\"),run_name=\"__main__\")\n"
        ],
        "env_overrides": {
          "MALLOC_ARENA_MAX": "2"
        },
        "affinity": [
          4,
          5
        ],
        "cpu_limit_s": 115,
        "as_limit_bytes": 34359738368,
        "group_rss_guard_bytes": 6442450944,
        "deadline_s": 130,
        "wall_s": 1.5328158050542697,
        "sampled_group_rss_peak_bytes": 2483519488,
        "sampled_max_process_vmpeak_bytes": 7638208512,
        "samples": 18,
        "exit": 0,
        "killed": null,
        "child_cpu_cumulative_s": 1.5214089999999998,
        "stderr": ""
      },
      "stage": {
        "stage": "check",
        "module": "FinalSourceTransport",
        "argv": [
          "/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/leanchecker",
          "FinalSourceTransport"
        ],
        "exit": 0,
        "source_sha256_before": "f362114a263c563e6a260c6fd7a04f6dcd0533054c74330a1d1a1af4e65fe4f4",
        "source_sha256_after": "f362114a263c563e6a260c6fd7a04f6dcd0533054c74330a1d1a1af4e65fe4f4",
        "olean_sha256_before": "8d97fd354d0162e61c8de0ae3d0fbd0fd9511775fd4399d3548066e111fd03aa",
        "olean_sha256_after": "8d97fd354d0162e61c8de0ae3d0fbd0fd9511775fd4399d3548066e111fd03aa",
        "LEAN_PATH": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-four-claim-final-assembly-formal-sol-r5/build:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/batteries/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/aesop/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/Qq/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/importGraph/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/plausible/.lake/build/lib/lean",
        "LEAN_NUM_THREADS": 1
      }
    },
    {
      "receipt": "f06-assembly-kernel.receipt.json",
      "receipt_sha256": "ffe016d8b5d48833ea1241167ccd95354ddacdc50a4e27782b1a699a23a59a2f",
      "stdout": "f06-assembly-kernel.output.txt",
      "stdout_sha256": "4af2e25eb41c5092613b4ed62adec9fcb7de60a69e53120e0268275b9c59835b",
      "resource": {
        "utc": "2026-11-15T23:13:16.512407+00:00",
        "name": "f06-assembly-kernel",
        "cwd": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-four-claim-final-assembly-formal-sol-r5",
        "command": [
          "/usr/bin/python3",
          "-I",
          "-B",
          "-c",
          "import os,resource; os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(115,115)); resource.setrlimit(resource.RLIMIT_AS,(32*1024**3,32*1024**3));\nimport os,runpy\nrunpy.run_path(os.path.join(os.environ[\"FORMAL_ROOT\"],\"formal_command.py\"),run_name=\"__main__\")\n"
        ],
        "env_overrides": {
          "MALLOC_ARENA_MAX": "2"
        },
        "affinity": [
          4,
          5
        ],
        "cpu_limit_s": 115,
        "as_limit_bytes": 34359738368,
        "group_rss_guard_bytes": 6442450944,
        "deadline_s": 130,
        "wall_s": 1.517079437035136,
        "sampled_group_rss_peak_bytes": 2483736576,
        "sampled_max_process_vmpeak_bytes": 7638302720,
        "samples": 18,
        "exit": 0,
        "killed": null,
        "child_cpu_cumulative_s": 1.5083199999999999,
        "stderr": ""
      },
      "stage": {
        "stage": "check",
        "module": "FinalAssembly",
        "argv": [
          "/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/leanchecker",
          "FinalAssembly"
        ],
        "exit": 0,
        "source_sha256_before": "563fa30dd88bc86ee9aa155f21bbc6ee02bf81e946e03433ac0caa4d5f832417",
        "source_sha256_after": "563fa30dd88bc86ee9aa155f21bbc6ee02bf81e946e03433ac0caa4d5f832417",
        "olean_sha256_before": "7b2c0f17b7e32bbd36fd12d2fe36c5a69f67f4cc60b7ea6cf2a45954fc3cc1cf",
        "olean_sha256_after": "7b2c0f17b7e32bbd36fd12d2fe36c5a69f67f4cc60b7ea6cf2a45954fc3cc1cf",
        "LEAN_PATH": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-four-claim-final-assembly-formal-sol-r5/build:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/batteries/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/aesop/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/Qq/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/importGraph/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/plausible/.lake/build/lib/lean",
        "LEAN_NUM_THREADS": 1
      }
    },
    {
      "receipt": "f07-audit-kernel.receipt.json",
      "receipt_sha256": "324b6489b7562262ed77577560dc6b262c7c897c3043da2b863821d766e46371",
      "stdout": "f07-audit-kernel.output.txt",
      "stdout_sha256": "b5c22223b6720864dde7e830b6a959f41372255f32698910e99ce0c57c7520a7",
      "resource": {
        "utc": "2026-11-15T23:13:49.351024+00:00",
        "name": "f07-audit-kernel",
        "cwd": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-four-claim-final-assembly-formal-sol-r5",
        "command": [
          "/usr/bin/python3",
          "-I",
          "-B",
          "-c",
          "import os,resource; os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(115,115)); resource.setrlimit(resource.RLIMIT_AS,(32*1024**3,32*1024**3));\nimport os,runpy\nrunpy.run_path(os.path.join(os.environ[\"FORMAL_ROOT\"],\"formal_command.py\"),run_name=\"__main__\")\n"
        ],
        "env_overrides": {
          "MALLOC_ARENA_MAX": "2"
        },
        "affinity": [
          4,
          5
        ],
        "cpu_limit_s": 115,
        "as_limit_bytes": 34359738368,
        "group_rss_guard_bytes": 6442450944,
        "deadline_s": 130,
        "wall_s": 1.5644788789795712,
        "sampled_group_rss_peak_bytes": 2483576832,
        "sampled_max_process_vmpeak_bytes": 7638335488,
        "samples": 17,
        "exit": 0,
        "killed": null,
        "child_cpu_cumulative_s": 1.553284,
        "stderr": ""
      },
      "stage": {
        "stage": "check",
        "module": "FinalExpandedAudit",
        "argv": [
          "/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/leanchecker",
          "FinalExpandedAudit"
        ],
        "exit": 0,
        "source_sha256_before": "1df56f9ef320b414ae4e22231f0b210d234e65faa73da6f6df8210fc01cdd79b",
        "source_sha256_after": "1df56f9ef320b414ae4e22231f0b210d234e65faa73da6f6df8210fc01cdd79b",
        "olean_sha256_before": "7876124f7c9a617aa7ee224ffe187c18a44c842bb77ef896ab778bf2c8023ba4",
        "olean_sha256_after": "7876124f7c9a617aa7ee224ffe187c18a44c842bb77ef896ab778bf2c8023ba4",
        "LEAN_PATH": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-four-claim-final-assembly-formal-sol-r5/build:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/batteries/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/aesop/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/Qq/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/importGraph/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/plausible/.lake/build/lib/lean",
        "LEAN_NUM_THREADS": 1
      }
    },
    {
      "receipt": "f08-assembly-final.receipt.json",
      "receipt_sha256": "39db7ae84f7abf2991901c2ee0d89bd69188e8ac29187109e6b5733b56f3c04c",
      "stdout": "f08-assembly-final.output.txt",
      "stdout_sha256": "a1267fee64d8c088ea249d101a50b2da8940e913d803f25b3dace074ba9a0458",
      "resource": {
        "utc": "2026-11-15T23:14:20.019311+00:00",
        "name": "f08-assembly-final",
        "cwd": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-four-claim-final-assembly-formal-sol-r5",
        "command": [
          "/usr/bin/python3",
          "-I",
          "-B",
          "-c",
          "import os,resource; os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(115,115)); resource.setrlimit(resource.RLIMIT_AS,(32*1024**3,32*1024**3));\nimport os,runpy\nrunpy.run_path(os.path.join(os.environ[\"FORMAL_ROOT\"],\"formal_command.py\"),run_name=\"__main__\")\n"
        ],
        "env_overrides": {
          "MALLOC_ARENA_MAX": "2"
        },
        "affinity": [
          4,
          5
        ],
        "cpu_limit_s": 115,
        "as_limit_bytes": 34359738368,
        "group_rss_guard_bytes": 6442450944,
        "deadline_s": 130,
        "wall_s": 1.2638918979791924,
        "sampled_group_rss_peak_bytes": 2843082752,
        "sampled_max_process_vmpeak_bytes": 7678967808,
        "samples": 15,
        "exit": 0,
        "killed": null,
        "child_cpu_cumulative_s": 1.25101,
        "stderr": ""
      },
      "stage": {
        "stage": "compile",
        "module": "FinalAssembly",
        "argv": [
          "/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean",
          "-j1",
          "-M3500",
          "-DwarningAsError=true",
          "-o",
          "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-four-claim-final-assembly-formal-sol-r5/build/FinalAssembly.olean",
          "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-four-claim-final-assembly-formal-sol-r5/src/FinalAssembly.lean"
        ],
        "exit": 0,
        "source_sha256_before": "a7cff8d930073705fcf766f77479935c1ff6501c588b53cb83bc6bc0bd16bf7f",
        "source_sha256_after": "a7cff8d930073705fcf766f77479935c1ff6501c588b53cb83bc6bc0bd16bf7f",
        "olean_sha256_before": "7b2c0f17b7e32bbd36fd12d2fe36c5a69f67f4cc60b7ea6cf2a45954fc3cc1cf",
        "olean_sha256_after": "d6193199e343f03d7981500484a58c02bbceee34a59ce3fe67ea1ba5fa752ed6",
        "LEAN_PATH": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-four-claim-final-assembly-formal-sol-r5/build:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/batteries/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/aesop/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/Qq/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/importGraph/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/plausible/.lake/build/lib/lean",
        "LEAN_NUM_THREADS": 1
      }
    },
    {
      "receipt": "f09-audit-final.receipt.json",
      "receipt_sha256": "536b0b9a92a030514eaffb4e4246c60a70122f0174a088101ae9a9b0f869b13e",
      "stdout": "f09-audit-final.output.txt",
      "stdout_sha256": "a9696784ef8de2ae37cd0be7d69865cb119d17afc4e3244d4fe33c14aa34571d",
      "resource": {
        "utc": "2026-11-15T23:14:50.726591+00:00",
        "name": "f09-audit-final",
        "cwd": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-four-claim-final-assembly-formal-sol-r5",
        "command": [
          "/usr/bin/python3",
          "-I",
          "-B",
          "-c",
          "import os,resource; os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(115,115)); resource.setrlimit(resource.RLIMIT_AS,(32*1024**3,32*1024**3));\nimport os,runpy\nrunpy.run_path(os.path.join(os.environ[\"FORMAL_ROOT\"],\"formal_command.py\"),run_name=\"__main__\")\n"
        ],
        "env_overrides": {
          "MALLOC_ARENA_MAX": "2"
        },
        "affinity": [
          4,
          5
        ],
        "cpu_limit_s": 115,
        "as_limit_bytes": 34359738368,
        "group_rss_guard_bytes": 6442450944,
        "deadline_s": 130,
        "wall_s": 1.2632200870430097,
        "sampled_group_rss_peak_bytes": 2839568384,
        "sampled_max_process_vmpeak_bytes": 8702566400,
        "samples": 15,
        "exit": 0,
        "killed": null,
        "child_cpu_cumulative_s": 1.250225,
        "stderr": ""
      },
      "stage": {
        "stage": "compile",
        "module": "FinalExpandedAudit",
        "argv": [
          "/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean",
          "-j1",
          "-M3500",
          "-DwarningAsError=true",
          "-o",
          "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-four-claim-final-assembly-formal-sol-r5/build/FinalExpandedAudit.olean",
          "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-four-claim-final-assembly-formal-sol-r5/src/FinalExpandedAudit.lean"
        ],
        "exit": 0,
        "source_sha256_before": "a047ccae1ddfb414834ee6332e87d802a248c34155dd59de53a5d0764b643891",
        "source_sha256_after": "a047ccae1ddfb414834ee6332e87d802a248c34155dd59de53a5d0764b643891",
        "olean_sha256_before": "7876124f7c9a617aa7ee224ffe187c18a44c842bb77ef896ab778bf2c8023ba4",
        "olean_sha256_after": "7876124f7c9a617aa7ee224ffe187c18a44c842bb77ef896ab778bf2c8023ba4",
        "LEAN_PATH": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-four-claim-final-assembly-formal-sol-r5/build:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/batteries/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/aesop/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/Qq/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/importGraph/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/plausible/.lake/build/lib/lean",
        "LEAN_NUM_THREADS": 1
      }
    },
    {
      "receipt": "f10-assembly-final-kernel.receipt.json",
      "receipt_sha256": "c65290bfec777380884bf173c312177cc52f5985fca66fc3f3cd6c6b1e93507b",
      "stdout": "f10-assembly-final-kernel.output.txt",
      "stdout_sha256": "21647af9c88898d2be3fbc30e60337ffe91fc618ba8f4f529912d81a6ed0e238",
      "resource": {
        "utc": "2026-11-15T23:15:42.255594+00:00",
        "name": "f10-assembly-final-kernel",
        "cwd": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-four-claim-final-assembly-formal-sol-r5",
        "command": [
          "/usr/bin/python3",
          "-I",
          "-B",
          "-c",
          "import os,resource; os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(115,115)); resource.setrlimit(resource.RLIMIT_AS,(32*1024**3,32*1024**3));\nimport os,runpy\nrunpy.run_path(os.path.join(os.environ[\"FORMAL_ROOT\"],\"formal_command.py\"),run_name=\"__main__\")\n"
        ],
        "env_overrides": {
          "MALLOC_ARENA_MAX": "2"
        },
        "affinity": [
          4,
          5
        ],
        "cpu_limit_s": 115,
        "as_limit_bytes": 34359738368,
        "group_rss_guard_bytes": 6442450944,
        "deadline_s": 130,
        "wall_s": 1.587306021945551,
        "sampled_group_rss_peak_bytes": 2483671040,
        "sampled_max_process_vmpeak_bytes": 7638306816,
        "samples": 18,
        "exit": 0,
        "killed": null,
        "child_cpu_cumulative_s": 1.571037,
        "stderr": ""
      },
      "stage": {
        "stage": "check",
        "module": "FinalAssembly",
        "argv": [
          "/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/leanchecker",
          "FinalAssembly"
        ],
        "exit": 0,
        "source_sha256_before": "a7cff8d930073705fcf766f77479935c1ff6501c588b53cb83bc6bc0bd16bf7f",
        "source_sha256_after": "a7cff8d930073705fcf766f77479935c1ff6501c588b53cb83bc6bc0bd16bf7f",
        "olean_sha256_before": "d6193199e343f03d7981500484a58c02bbceee34a59ce3fe67ea1ba5fa752ed6",
        "olean_sha256_after": "d6193199e343f03d7981500484a58c02bbceee34a59ce3fe67ea1ba5fa752ed6",
        "LEAN_PATH": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-four-claim-final-assembly-formal-sol-r5/build:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/batteries/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/aesop/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/Qq/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/importGraph/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/plausible/.lake/build/lib/lean",
        "LEAN_NUM_THREADS": 1
      }
    },
    {
      "receipt": "f11-audit-final-kernel.receipt.json",
      "receipt_sha256": "35bf51f82cf191c926f437673290ff83fe418a9428a8ed130e93882383102e77",
      "stdout": "f11-audit-final-kernel.output.txt",
      "stdout_sha256": "2fc9979b577373e63756f9c7e29569df72a50bec7575a7bd43229eb2ef0bf9a5",
      "resource": {
        "utc": "2026-11-15T23:16:49.024809+00:00",
        "name": "f11-audit-final-kernel",
        "cwd": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-four-claim-final-assembly-formal-sol-r5",
        "command": [
          "/usr/bin/python3",
          "-I",
          "-B",
          "-c",
          "import os,resource; os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(115,115)); resource.setrlimit(resource.RLIMIT_AS,(32*1024**3,32*1024**3));\nimport os,runpy\nrunpy.run_path(os.path.join(os.environ[\"FORMAL_ROOT\"],\"formal_command.py\"),run_name=\"__main__\")\n"
        ],
        "env_overrides": {
          "MALLOC_ARENA_MAX": "2"
        },
        "affinity": [
          4,
          5
        ],
        "cpu_limit_s": 115,
        "as_limit_bytes": 34359738368,
        "group_rss_guard_bytes": 6442450944,
        "deadline_s": 130,
        "wall_s": 1.5451608899747953,
        "sampled_group_rss_peak_bytes": 2483589120,
        "sampled_max_process_vmpeak_bytes": 7638339584,
        "samples": 18,
        "exit": 0,
        "killed": null,
        "child_cpu_cumulative_s": 1.533548,
        "stderr": ""
      },
      "stage": {
        "stage": "check",
        "module": "FinalExpandedAudit",
        "argv": [
          "/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/leanchecker",
          "FinalExpandedAudit"
        ],
        "exit": 0,
        "source_sha256_before": "a047ccae1ddfb414834ee6332e87d802a248c34155dd59de53a5d0764b643891",
        "source_sha256_after": "a047ccae1ddfb414834ee6332e87d802a248c34155dd59de53a5d0764b643891",
        "olean_sha256_before": "7876124f7c9a617aa7ee224ffe187c18a44c842bb77ef896ab778bf2c8023ba4",
        "olean_sha256_after": "7876124f7c9a617aa7ee224ffe187c18a44c842bb77ef896ab778bf2c8023ba4",
        "LEAN_PATH": "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/dl-history-four-claim-final-assembly-formal-sol-r5/build:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/batteries/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/aesop/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/Qq/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/importGraph/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/plausible/.lake/build/lib/lean",
        "LEAN_NUM_THREADS": 1
      }
    }
  ],
  "max_sampled_RSS": 2843230208,
  "cpu_total": 14.995593999999999
}
```

## Literal extraction and build harness

### extract_final_paper.py

SHA256 1c1b021d30da734162d9ae7543586de7c138b79257cccc8a39fa94f2a559ce56

```text
import pathlib,sys,json,re,hashlib
paper=pathlib.Path(sys.argv[1]).read_bytes()
out=pathlib.Path(sys.argv[2]);out.mkdir(parents=True,exist_ok=True)
pattern=rb'<!-- SOURCE (\{[^\n]+\}) -->\n```lean\n'
entries=[];seen=set()
for match in re.finditer(pattern,paper):
    e=json.loads(match.group(1));name=e['module']
    assert re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',name) and name not in seen
    seen.add(name);body=paper[match.end():match.end()+e['bytes']]
    assert hashlib.sha256(body).hexdigest()==e['sha256'],name
    assert paper[match.end()+e['bytes']:].startswith(b'```\n<!-- END SOURCE -->'),name
    imports=re.findall(rb'^import (\S+)',body,re.M)
    e['imports']=[i.decode() for i in imports]
    entries.append((e,body))
assert len(entries)==63
order=[e['module'] for e,b in entries]
for e,b in entries:
    assert all(i not in order or order.index(i)<order.index(e['module']) for i in e['imports'])
    dest=out/(e['module']+'.lean')
    if dest.exists():assert dest.read_bytes()==b
    else:dest.write_bytes(b)
(out/'EXTRACTED-SOURCES.json').write_text(json.dumps([e for e,b in entries],indent=2))
print(json.dumps({'sources':len(entries),'bytes':sum(len(b) for e,b in entries),'status':'all literal bytes and hashes verified; no Lean invocation'}))

```

### check32.sh

SHA256 4706b93c28ab6885f257d458726e87b36e5ca56192575593b07529cc18a56d7c

```text
#!/bin/bash
set -eu
export FORMAL_OPERATION=compile
export FORMAL_MODULE="${1:?module name required}"
export FORMAL_ROOT="$(cd "$(dirname "$0")" && pwd)"
exec timeout 140 python3 -I -B "$FORMAL_ROOT/run_lean_32g.py" "${2:?unique receipt label required}" <<'PY'
import os,runpy
runpy.run_path(os.path.join(os.environ["FORMAL_ROOT"],"formal_command.py"),run_name="__main__")
PY

```

### checker32.sh

SHA256 b6366a53972ea147ec8a8dfffea2d156b21fb2fec71aa708742881e6ec465f76

```text
#!/bin/bash
set -eu
export FORMAL_OPERATION=check
export FORMAL_MODULE="${1:?module name required}"
export FORMAL_ROOT="$(cd "$(dirname "$0")" && pwd)"
exec timeout 140 python3 -I -B "$FORMAL_ROOT/run_lean_32g.py" "${2:?unique receipt label required}" <<'PY'
import os,runpy
runpy.run_path(os.path.join(os.environ["FORMAL_ROOT"],"formal_command.py"),run_name="__main__")
PY

```

### formal_command.py

SHA256 f0af4db06cefea766d2702f50b9513256d2f0233d62e87f8093d46e500e66059

```text
import os,re,json,hashlib,subprocess,sys,shutil
from pathlib import Path
p=Path(__file__).resolve().parent
pins=json.loads((p/'PINS.json').read_text())
mode=os.environ['FORMAL_OPERATION'];module=os.environ['FORMAL_MODULE']
assert mode in ['compile','check'] and re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',module)
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(Path(pins['lean_bin']))==pins['lean_sha256'] and sha(Path(pins['leanchecker_bin']))==pins['leanchecker_sha256']
source=p/'src'/(module+'.lean');olean=p/'build'/(module+'.olean')
assert source.is_file();before=sha(source)
env=dict(os.environ);env['PATH']=str(Path(pins['lean_bin']).parent)+os.pathsep+env.get('PATH','');env['LEAN_PATH']=os.pathsep.join([str(p/'build')]+pins['upstream_lean_paths']);env['LEAN_NUM_THREADS']='1'
prior=sha(olean) if olean.exists() else None
if mode=='compile':
 if olean.exists():
  archive=p/'cache'/(module+'.'+prior+'.olean')
  if not archive.exists():shutil.copyfile(olean,archive)
  olean.unlink()
 args=[pins['lean_bin'],'-j1','-M3500','-DwarningAsError=true','-o',str(olean),str(source)]
else:
 assert olean.is_file(),'Kernel checker requires actual production olean'
 args=[pins['leanchecker_bin'],module]
r=subprocess.run(args,cwd=p,env=env,text=True,capture_output=True)
sys.stdout.write(r.stdout);sys.stderr.write(r.stderr)
after=sha(source);out=sha(olean) if olean.exists() else None
print(json.dumps(dict(stage=mode,module=module,argv=args,exit=r.returncode,source_sha256_before=before,source_sha256_after=after,olean_sha256_before=prior,olean_sha256_after=out,LEAN_PATH=env['LEAN_PATH'],LEAN_NUM_THREADS=1)))
assert before==after,'Source changed during compile/check'
if r.returncode==0:
 assert out is not None,'No fresh olean produced'
 if mode=='check':assert prior==out,'Checker changed olean'
raise SystemExit(r.returncode)

```

### run_lean_32g.py

SHA256 dd826a8e5bcdc01f7dd46022a5a1a06dda1507e56a0dcf82624790c9befc7388

```text
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(32*1024**3,32*1024**3))
import sys,subprocess,time,json,pathlib,datetime,signal
lane=pathlib.Path(__file__).resolve().parent
assert os.environ.get('FORMAL_OPERATION') in ('compile','check') and os.environ.get('FORMAL_MODULE'),'This runner is only for Lean compile and kernel-check runs'
name=sys.argv[1]; code=sys.stdin.read(); start=time.monotonic(); utc=datetime.datetime.now(datetime.timezone.utc).isoformat()
env=dict(os.environ,MALLOC_ARENA_MAX='2')
prefix='import os,resource; os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(115,115)); resource.setrlimit(resource.RLIMIT_AS,(32*1024**3,32*1024**3));\n'
p=subprocess.Popen([sys.executable,'-I','-B','-c',prefix+code],cwd=lane,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
peak=0; samples=0; killed=None; vm=0
while p.poll() is None:
 rss=0
 for ent in pathlib.Path('/proc').iterdir():
  if not ent.name.isdigit(): continue
  try:
   s=(ent/'stat').read_text().split(') ',1)[1].split()
   if int(s[2])==p.pid:
    rss+=int((ent/'statm').read_text().split()[1])*os.sysconf('SC_PAGE_SIZE')
    vm=max(vm,max([int(l.split()[1])*1024 for l in (ent/'status').read_text().splitlines() if l.startswith('VmPeak:')] or [0]))
  except (OSError,ValueError,IndexError): pass
 peak=max(peak,rss); samples+=1
 if rss>6*1024**3 or time.monotonic()-start>130:
  killed='rss' if rss>6*1024**3 else 'deadline'; os.killpg(p.pid,signal.SIGKILL); break
 try: out,err=p.communicate(timeout=.08); break
 except subprocess.TimeoutExpired: pass
out,err=p.communicate(); wall=time.monotonic()-start
r={'utc':utc,'name':name,'cwd':str(lane),'command':[sys.executable,'-I','-B','-c',prefix+code],'env_overrides':{'MALLOC_ARENA_MAX':'2'},'affinity':sorted(os.sched_getaffinity(0)),'cpu_limit_s':115,'as_limit_bytes':32*1024**3,'group_rss_guard_bytes':6*1024**3,'deadline_s':130,'wall_s':wall,'sampled_group_rss_peak_bytes':peak,'sampled_max_process_vmpeak_bytes':vm,'samples':samples,'exit':p.returncode,'killed':killed,'child_cpu_cumulative_s':resource.getrusage(resource.RUSAGE_CHILDREN).ru_utime+resource.getrusage(resource.RUSAGE_CHILDREN).ru_stime,'stderr':err.decode(errors='replace')}
def write(n,s):
 z=subprocess.run([sys.executable,'-I','-B',str(lane/'write_lane.py'),n],input=s,text=True,capture_output=True,env=env,timeout=10); assert z.returncode==0,z.stderr
write(name+'.receipt.json',json.dumps(r,indent=2)); write(name+'.output.txt',out.decode(errors='replace'))
print(out.decode(errors='replace')); print(json.dumps(r)); sys.exit(p.returncode)

```

### write_lane.py

SHA256 b45b49e99f75e73c33b03852587f95e61b502476adaa69d9a10a6619827fe636

```text
import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(10,10))
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
import pathlib,sys
lane=pathlib.Path(__file__).resolve().parent
rel=pathlib.PurePath(sys.argv[1])
assert not rel.is_absolute() and ".." not in rel.parts
target=(lane/rel).resolve()
assert target.is_relative_to(lane) and target!=lane and not target.is_symlink()
text=sys.stdin.read()
target.parent.mkdir(parents=True,exist_ok=True)

if len(sys.argv)>2 and sys.argv[2]=='--base64':
 import base64
 target.write_bytes(base64.b64decode(text))
else:
 target.write_text(text)
print(str(target))

```

## Complete literal production sources, true dependency order

### LiteralHistory

<!-- SOURCE {"module": "LiteralHistory", "bytes": 5556, "sha256": "c40f422055fb4dce20d15df8871f649a2e98e1a26ab7b6f9856015eb7e73a97c"} -->
```lean
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Linarith

namespace LiteralDL
inductive Species where
  | leaf : Species
  | node : Species → Species → Species
  deriving DecidableEq

def weight : Species → Nat
  | .leaf => 1
  | .node a b => weight a + weight b + 1

theorem weight_pos (s : Species) : 0 < weight s := by cases s <;> simp [weight]

/-- Actual ordered event syntax: keep constructors retain a loss on the other side. -/
inductive Hist : Species → Type where
  | extant : Hist .leaf
  | dup {s} : Hist s → Hist s → Hist s
  | both {a b} : Hist a → Hist b → Hist (.node a b)
  | keepLeft {a b} : Hist a → Hist (.node a b)
  | keepRight {a b} : Hist b → Hist (.node a b)
  deriving DecidableEq

def size : {s : Species} → Hist s → Nat
  | _, .extant => 1
  | _, .dup x y => size x + size y
  | _, .both x y => size x + size y
  | _, .keepLeft x => size x
  | _, .keepRight x => size x

theorem size_pos {s} (h : Hist s) : 0 < size h := by
  induction h <;> simp_all [size]

def depth : {s : Species} → Hist s → Nat
  | _, .extant => 1
  | _, .dup x y => max (depth x) (depth y) + 1
  | _, .both x y => max (depth x) (depth y) + 1
  | _, .keepLeft x => depth x + 1
  | _, .keepRight x => depth x + 1

theorem depth_bound {s} (h : Hist s) : depth h ≤ size h * weight s := by
  induction h with
  | extant => simp [depth, size, weight]
  | @dup s x y ix iy =>
    have px := size_pos x
    have py := size_pos y
    have pw := weight_pos s
    simp only [depth, size]
    have hx : depth x + 1 ≤ (size x + size y) * weight s := by nlinarith
    have hy : depth y + 1 ≤ (size x + size y) * weight s := by nlinarith
    omega
  | @both a b x y ix iy =>
    have px := size_pos x
    have py := size_pos y
    have pa := weight_pos a
    have pb := weight_pos b
    simp only [depth, size, weight]
    have hx : depth x + 1 ≤ (size x + size y) * (weight a + weight b + 1) := by nlinarith
    have hy : depth y + 1 ≤ (size x + size y) * (weight a + weight b + 1) := by nlinarith
    omega
  | @keepLeft a b x ix =>
    have px := size_pos x
    have pb := weight_pos b
    simp only [depth, size, weight]
    nlinarith
  | @keepRight a b x ix =>
    have px := size_pos x
    have pa := weight_pos a
    simp only [depth, size, weight]
    nlinarith

def pool : Nat → (s : Species) → List (Hist s)
  | 0, _ => []
  | d+1, .leaf => .extant :: ((pool d .leaf).product (pool d .leaf)).map
      (fun xy => .dup xy.1 xy.2)
  | d+1, .node a b =>
      (((pool d (.node a b)).product (pool d (.node a b))).map
        (fun xy => .dup xy.1 xy.2)) ++
      (((pool d a).product (pool d b)).map (fun xy => .both xy.1 xy.2)) ++
      ((pool d a).map (fun x => .keepLeft x)) ++
      ((pool d b).map (fun x => .keepRight x))

theorem mem_pool {s} (h : Hist s) (d : Nat) (hd : depth h ≤ d) : h ∈ pool d s := by
  induction d generalizing s with
  | zero => cases h <;> simp_all [depth]
  | succ d ih =>
    cases h with
    | extant => simp [pool]
    | dup x y =>
      have hx := ih x (by simp only [depth] at hd; omega)
      have hy := ih y (by simp only [depth] at hd; omega)
      cases s <;> simp only [pool, List.mem_cons, List.mem_append, List.mem_map]
      all_goals aesop
    | both x y =>
      have hx := ih x (by simp only [depth] at hd; omega)
      have hy := ih y (by simp only [depth] at hd; omega)
      simp only [pool, List.mem_append, List.mem_map]
      aesop
    | keepLeft x =>
      have hx := ih x (by simp only [depth] at hd; omega)
      simp only [pool, List.mem_append, List.mem_map]
      aesop
    | keepRight x =>
      have hx := ih x (by simp only [depth] at hd; omega)
      simp only [pool, List.mem_append, List.mem_map]
      aesop

abbrev Fiber (s : Species) (n : Nat) := {h : Hist s // size h = n}

instance fiberFintype (s : Species) (n : Nat) : Fintype (Fiber s n) :=
  Fintype.ofFinset ((pool (n * weight s) s).toFinset.filter (fun h => size h = n))
    (by intro h; simp only [Finset.mem_filter, List.mem_toFinset]
        exact ⟨fun q => q.2, fun q => ⟨mem_pool h _ (q ▸ depth_bound h), q⟩⟩)

def count (s : Species) (n : Nat) : Nat := Fintype.card (Fiber s n)

def duplicate {s i j} (x : Fiber s i × Fiber s j) : Fiber s (i+j) :=
  ⟨.dup x.1.1 x.2.1, by simp [size, x.1.2, x.2.2]⟩

theorem duplicate_injective {s i j} : Function.Injective (@duplicate s i j) := by
  intro x y h
  have hh := congrArg Subtype.val h
  cases x with
  | mk x1 x2 =>
    cases y with
    | mk y1 y2 =>
      simp only [duplicate, Hist.dup.injEq] at hh
      exact Prod.ext (Subtype.ext hh.1) (Subtype.ext hh.2)

theorem supermultiplicative (s : Species) (i j : Nat) :
    count s i * count s j ≤ count s (i+j) := by
  simpa [count, Fintype.card_prod] using Fintype.card_le_of_injective
    (@duplicate s i j) duplicate_injective

theorem fiber_zero_empty (s : Species) : IsEmpty (Fiber s 0) :=
  ⟨fun h => by have hp := size_pos h.1; omega⟩

def one : (s : Species) → Fiber s 1
  | .leaf => ⟨.extant, rfl⟩
  | .node a _ => ⟨.keepLeft (one a).1, (one a).2⟩

def positiveFiber (s : Species) : (n : Nat) → Fiber s (n+1)
  | 0 => one s
  | n+1 => duplicate (positiveFiber s n, one s)

theorem count_pos (s : Species) (n : Nat) : 0 < count s (n+1) := by
  have : Nonempty (Fiber s (n+1)) := ⟨positiveFiber s n⟩
  exact Fintype.card_pos_iff.mpr this

#print axioms depth_bound
#print axioms fiberFintype
#print axioms supermultiplicative
end LiteralDL
```
<!-- END SOURCE -->

### SourceHistory

<!-- SOURCE {"module": "SourceHistory", "bytes": 3518, "sha256": "b7df492ce4f3049440b665cfd106a52127b54247863226220151a484591a9e13"} -->
```lean
import LiteralHistory
namespace LiteralDL
inductive Event where
  | extant | loss | duplication | speciation
  deriving DecidableEq
inductive EventTree where
  | tip : List Bool → Event → EventTree
  | fork : List Bool → Event → EventTree → EventTree → EventTree
  deriving DecidableEq

/-- Species addresses record the source map at every event, including losses. -/
def encode {s} (p : List Bool) : Hist s → EventTree
  | .extant => .tip p .extant
  | .dup x y => .fork p .duplication (encode p x) (encode p y)
  | .both x y => .fork p .speciation (encode (p ++ [false]) x) (encode (p ++ [true]) y)
  | .keepLeft x => .fork p .speciation (encode (p ++ [false]) x) (.tip (p ++ [true]) .loss)
  | .keepRight y => .fork p .speciation (.tip (p ++ [false]) .loss) (encode (p ++ [true]) y)

/-- Explicit source grammar with labels, ordered children and species map. -/
inductive Valid : Species → List Bool → EventTree → Prop where
  | extant (p) : Valid .leaf p (.tip p .extant)
  | dup {s p x y} : Valid s p x → Valid s p y →
      Valid s p (.fork p .duplication x y)
  | both {a b p x y} : Valid a (p ++ [false]) x → Valid b (p ++ [true]) y →
      Valid (.node a b) p (.fork p .speciation x y)
  | keepLeft {a b p x} : Valid a (p ++ [false]) x →
      Valid (.node a b) p (.fork p .speciation x (.tip (p ++ [true]) .loss))
  | keepRight {a b p y} : Valid b (p ++ [true]) y →
      Valid (.node a b) p (.fork p .speciation (.tip (p ++ [false]) .loss) y)

theorem encode_valid {s} (h : Hist s) (p) : Valid s p (encode p h) := by
  induction h generalizing p with
  | extant => exact .extant p
  | dup x y ix iy => exact .dup (ix p) (iy p)
  | both x y ix iy => exact .both (ix _) (iy _)
  | keepLeft x ix => exact .keepLeft (ix _)
  | keepRight x ix => exact .keepRight (ix _)

theorem valid_has_history {s p t} (v : Valid s p t) : ∃ h : Hist s, encode p h = t := by
  induction v with
  | extant p => exact ⟨.extant, rfl⟩
  | dup vx vy ix iy =>
    obtain ⟨x, rfl⟩ := ix
    obtain ⟨y, rfl⟩ := iy
    exact ⟨.dup x y, rfl⟩
  | both vx vy ix iy =>
    obtain ⟨x, rfl⟩ := ix
    obtain ⟨y, rfl⟩ := iy
    exact ⟨.both x y, rfl⟩
  | keepLeft vx ix =>
    obtain ⟨x, rfl⟩ := ix
    exact ⟨.keepLeft x, rfl⟩
  | keepRight vy iy =>
    obtain ⟨y, rfl⟩ := iy
    exact ⟨.keepRight y, rfl⟩

theorem encode_ne_loss {s} (h : Hist s) (p q) : encode p h ≠ .tip q .loss := by
  cases h <;> simp [encode]

theorem encode_injective {s} (p) : Function.Injective (@encode s p) := by
  intro x
  induction x generalizing p with
  | extant => intro y h; cases y <;> simp_all [encode]
  | dup x y ix iy =>
    intro z h
    cases z <;> simp_all [encode]
    exact ⟨ix _ h.1, iy _ h.2⟩
  | both x y ix iy =>
    intro z h
    cases z <;> simp_all [encode, encode_ne_loss]
    exact ⟨ix _ h.1, iy _ h.2⟩
  | keepLeft x ix =>
    intro z h
    cases z <;> simp_all [encode, encode_ne_loss, Ne.symm (encode_ne_loss _ _ _)]
    exact ix _ h
  | keepRight y iy =>
    intro z h
    cases z <;> simp_all [encode, encode_ne_loss, Ne.symm (encode_ne_loss _ _ _)]
    exact iy _ h

noncomputable def sourceEquiv (s : Species) (p : List Bool) :
    Hist s ≃ {t : EventTree // Valid s p t} :=
  Equiv.ofBijective (fun h => ⟨encode p h, encode_valid h p⟩)
    ⟨fun _ _ h => encode_injective p (congrArg Subtype.val h),
     fun t => by obtain ⟨h, hh⟩ := valid_has_history t.2; exact ⟨h, Subtype.ext hh⟩⟩

#print axioms sourceEquiv
end LiteralDL
```
<!-- END SOURCE -->

### CardinalRecurrence

<!-- SOURCE {"module": "CardinalRecurrence", "bytes": 4086, "sha256": "410eb8a7ff37d70df547f84c705de81e78fccd5a8b49819a2b3d0cfb114fe977"} -->
```lean
import SourceHistory
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.BigOperators
namespace LiteralDL
abbrev PairFiber (a b : Species) (n : Nat) :=
  {xy : Hist a × Hist b // size xy.1 + size xy.2 = n}
abbrev Split (a b : Species) (n : Nat) :=
  (i : Fin (n+1)) × (Fiber a i × Fiber b (n-i))

def splitEquiv (a b : Species) (n : Nat) : PairFiber a b n ≃ Split a b n where
  toFun x := ⟨⟨size x.1.1, by have := x.2; omega⟩,
    ⟨⟨x.1.1, rfl⟩, ⟨x.1.2, by have := x.2; dsimp; omega⟩⟩⟩
  invFun x := ⟨(x.2.1.1, x.2.2.1), by
    have h := x.1.2
    have h1 := x.2.1.2
    have h2 := x.2.2.2
    dsimp at h h1 h2 ⊢
    omega⟩
  left_inv x := by rfl
  right_inv x := by
    rcases x with ⟨⟨i, hi⟩, ⟨⟨x, hx⟩, ⟨y, hy⟩⟩⟩
    dsimp at hx
    subst i
    rfl

instance pairFintype (a b : Species) (n : Nat) : Fintype (PairFiber a b n) :=
  Fintype.ofEquiv (Split a b n) (splitEquiv a b n).symm

def pairCount (a b : Species) (n : Nat) := Fintype.card (PairFiber a b n)

/-- Root alternatives before translating the finite pair fibers to convolution. -/
abbrev NodeRoot (a b : Species) (n : Nat) :=
  PairFiber (.node a b) (.node a b) n ⊕
    (PairFiber a b n ⊕ (Fiber a n ⊕ Fiber b n))

def nodeJoin {a b n} : NodeRoot a b n → Fiber (.node a b) n
  | .inl xy => ⟨.dup xy.1.1 xy.1.2, xy.2⟩
  | .inr (.inl xy) => ⟨.both xy.1.1 xy.1.2, xy.2⟩
  | .inr (.inr (.inl x)) => ⟨.keepLeft x.1, x.2⟩
  | .inr (.inr (.inr y)) => ⟨.keepRight y.1, y.2⟩

def nodeCut {a b n} (h : Fiber (.node a b) n) : NodeRoot a b n :=
  match h with
  | ⟨.dup x y, hn⟩ => .inl ⟨(x,y), hn⟩
  | ⟨.both x y, hn⟩ => .inr (.inl ⟨(x,y), hn⟩)
  | ⟨.keepLeft x, hn⟩ => .inr (.inr (.inl ⟨x, hn⟩))
  | ⟨.keepRight y, hn⟩ => .inr (.inr (.inr ⟨y, hn⟩))

def nodeEquiv (a b : Species) (n : Nat) : NodeRoot a b n ≃ Fiber (.node a b) n where
  toFun := nodeJoin
  invFun := nodeCut
  left_inv x := by rcases x with x | (x | (x | x)) <;> rfl
  right_inv x := by rcases x with ⟨x,h⟩; cases x <;> rfl

theorem count_node (a b : Species) (n : Nat) :
    count (.node a b) n = pairCount (.node a b) (.node a b) n +
      pairCount a b n + count a n + count b n := by
  have h := Fintype.card_congr (nodeEquiv a b n)
  simp only [Fintype.card_sum] at h
  unfold count pairCount
  omega

theorem pairCount_eq (a b : Species) (n : Nat) :
    pairCount a b n = ∑ i : Fin (n+1), count a i * count b (n-i) := by
  simpa [pairCount, Split, count, Fintype.card_sigma, Fintype.card_prod] using
    Fintype.card_congr (splitEquiv a b n)

abbrev LeafRoot (n : Nat) := {_u : Unit // 1 = n} ⊕ PairFiber .leaf .leaf n

def leafJoin {n} : LeafRoot n → Fiber .leaf n
  | .inl u => ⟨.extant, u.2⟩
  | .inr xy => ⟨.dup xy.1.1 xy.1.2, xy.2⟩

def leafCut {n} (h : Fiber .leaf n) : LeafRoot n :=
  match h with
  | ⟨.extant, hn⟩ => .inl ⟨(), hn⟩
  | ⟨.dup x y, hn⟩ => .inr ⟨(x,y), hn⟩

def leafEquiv (n : Nat) : LeafRoot n ≃ Fiber .leaf n where
  toFun := leafJoin
  invFun := leafCut
  left_inv x := by rcases x with ⟨⟨⟩,h⟩ | x <;> rfl
  right_inv x := by rcases x with ⟨x,h⟩; cases x <;> rfl

theorem count_leaf (n : Nat) : count .leaf n = (if n = 1 then 1 else 0) +
    ∑ i : Fin (n+1), count .leaf i * count .leaf (n-i) := by
  have h := Fintype.card_congr (leafEquiv n)
  simp only [Fintype.card_sum] at h
  rw [← pairCount_eq]
  unfold count pairCount
  by_cases hn : n = 1
  · subst n
    simpa using h.symm
  · have : IsEmpty {_u : Unit // 1 = n} := ⟨fun x => hn x.2.symm⟩
    simpa [hn, Fintype.card_of_isEmpty] using h.symm

theorem count_node_convolution (a b : Species) (n : Nat) :
    count (.node a b) n =
      (∑ i : Fin (n+1), count (.node a b) i * count (.node a b) (n-i)) +
      (∑ i : Fin (n+1), count a i * count b (n-i)) + count a n + count b n := by
  simpa only [pairCount_eq] using count_node a b n

#print axioms count_leaf
#print axioms count_node_convolution
#print axioms splitEquiv
#print axioms count_node
end LiteralDL
```
<!-- END SOURCE -->

### SourceFiber

<!-- SOURCE {"module": "SourceFiber", "bytes": 2303, "sha256": "06c19bc61776a55a41d4d37870213de34ca94722181953024d9e5f9a6819c748"} -->
```lean
import CardinalRecurrence
namespace LiteralDL

def extantCount : EventTree → Nat
  | .tip _ .extant => 1
  | .tip _ _ => 0
  | .fork _ _ x y => extantCount x + extantCount y

theorem encode_size {s} (h : Hist s) (p) : extantCount (encode p h) = size h := by
  induction h generalizing p <;> simp_all [encode, extantCount, size]

noncomputable def sourceFiberEquiv (s : Species) (n : Nat) (p : List Bool) :
    Fiber s n ≃ {t : EventTree // Valid s p t ∧ extantCount t = n} :=
  Equiv.ofBijective (fun h => ⟨encode p h.1, encode_valid h.1 p,
    (encode_size h.1 p).trans h.2⟩)
    ⟨fun _ _ h => Subtype.ext (encode_injective p (congrArg Subtype.val h)),
     fun t => by
       obtain ⟨h, hh⟩ := valid_has_history t.2.1
       refine ⟨⟨h, ?_⟩, Subtype.ext hh⟩
       rw [← encode_size h p, hh]
       exact t.2.2⟩

def swapRoot {a b} : Hist (.node a b) → Hist (.node b a)
  | .dup x y => .dup (swapRoot x) (swapRoot y)
  | .both x y => .both y x
  | .keepLeft x => .keepRight x
  | .keepRight y => .keepLeft y

theorem swapRoot_size {a b} (h : Hist (.node a b)) : size (swapRoot h) = size h := by
  cases h with
  | dup x y => simp [swapRoot, size, swapRoot_size x, swapRoot_size y]
  | both x y => simp [swapRoot, size, Nat.add_comm]
  | keepLeft x => simp [swapRoot, size]
  | keepRight y => simp [swapRoot, size]

theorem swapRoot_twice {a b} (h : Hist (.node a b)) : swapRoot (swapRoot h) = h := by
  cases h with
  | dup x y => simp [swapRoot, swapRoot_twice x, swapRoot_twice y]
  | both x y => simp [swapRoot]
  | keepLeft x => simp [swapRoot]
  | keepRight y => simp [swapRoot]

def swapFiber (a b : Species) (n : Nat) : Fiber (.node a b) n ≃ Fiber (.node b a) n where
  toFun h := ⟨swapRoot h.1, (swapRoot_size h.1).trans h.2⟩
  invFun h := ⟨swapRoot h.1, (swapRoot_size h.1).trans h.2⟩
  left_inv h := Subtype.ext (swapRoot_twice h.1)
  right_inv h := Subtype.ext (swapRoot_twice h.1)

theorem count_swap (a b : Species) (n : Nat) : count (.node a b) n = count (.node b a) n :=
  Fintype.card_congr (swapFiber a b n)

theorem count_zero (s : Species) : count s 0 = 0 := by
  let := fiber_zero_empty s
  exact Fintype.card_of_isEmpty

#print axioms sourceFiberEquiv
#print axioms count_swap
#print axioms count_zero
#print axioms count_pos
end LiteralDL
```
<!-- END SOURCE -->

### DuplicationSkeleton

<!-- SOURCE {"module": "DuplicationSkeleton", "bytes": 1762, "sha256": "99169772c17e784b3a61538feb7ffd50a73ed7157c199a7aeb3f860cb5abc497"} -->
```lean
import SourceFiber
namespace LiteralDL
inductive Skeleton (α : Type) where
  | atom : α → Skeleton α
  | fork : Skeleton α → Skeleton α → Skeleton α

inductive Atom : Species → Type where
  | extant : Atom .leaf
  | both {a b} : Hist a → Hist b → Atom (.node a b)
  | keepLeft {a b} : Hist a → Atom (.node a b)
  | keepRight {a b} : Hist b → Atom (.node a b)

def atomHist {s} : Atom s → Hist s
  | .extant => .extant
  | .both x y => .both x y
  | .keepLeft x => .keepLeft x
  | .keepRight y => .keepRight y

def assemble {s} : Skeleton (Atom s) → Hist s
  | .atom a => atomHist a
  | .fork x y => .dup (assemble x) (assemble y)

def cutSkeleton {s} : Hist s → Skeleton (Atom s)
  | .extant => .atom .extant
  | .dup x y => .fork (cutSkeleton x) (cutSkeleton y)
  | .both x y => .atom (.both x y)
  | .keepLeft x => .atom (.keepLeft x)
  | .keepRight y => .atom (.keepRight y)

theorem assemble_cut {s} (h : Hist s) : assemble (cutSkeleton h) = h := by
  induction h <;> simp_all [cutSkeleton, assemble, atomHist]

theorem cut_assemble {s} (t : Skeleton (Atom s)) : cutSkeleton (assemble t) = t := by
  induction t with
  | atom a => cases a <;> rfl
  | fork x y ix iy => simp [assemble, cutSkeleton, ix, iy]

def skeletonEquiv (s : Species) : Hist s ≃ Skeleton (Atom s) where
  toFun := cutSkeleton
  invFun := assemble
  left_inv := assemble_cut
  right_inv := cut_assemble

def skeletonSize {s} : Skeleton (Atom s) → Nat
  | .atom a => size (atomHist a)
  | .fork x y => skeletonSize x + skeletonSize y

theorem assemble_size {s} (t : Skeleton (Atom s)) : size (assemble t) = skeletonSize t := by
  induction t <;> simp_all [assemble, skeletonSize, size]

#print axioms skeletonEquiv
#print axioms assemble_size
end LiteralDL
```
<!-- END SOURCE -->

### WeightedSkeleton

<!-- SOURCE {"module": "WeightedSkeleton", "bytes": 2041, "sha256": "ac7cdbbd7f1f70dc59380e1fca6f5993c6e03def31787d8800a40ca2e4c49309"} -->
```lean
import DuplicationSkeleton
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
open scoped ENNReal
namespace LiteralDL

def rootEquiv (α : Type) : Skeleton α ≃ α ⊕ (Skeleton α × Skeleton α) where
  toFun t := match t with | .atom a => .inl a | .fork x y => .inr (x,y)
  invFun t := match t with | .inl a => .atom a | .inr xy => .fork xy.1 xy.2
  left_inv t := by cases t <;> rfl
  right_inv t := by rcases t with a | ⟨x,y⟩ <;> rfl

noncomputable def skWeight {α : Type} (f : α → ℝ≥0∞) : Skeleton α → ℝ≥0∞
  | .atom a => f a
  | .fork x y => skWeight f x * skWeight f y

noncomputable def total {α : Type} (f : α → ℝ≥0∞) : ℝ≥0∞ := ∑' t, skWeight f t

theorem total_quadratic {α : Type} (f : α → ℝ≥0∞) :
    total f = (∑' a, f a) + total f * total f := by
  calc
    total f = ∑' u : α ⊕ (Skeleton α × Skeleton α), skWeight f ((rootEquiv α).symm u) :=
      ((rootEquiv α).symm.tsum_eq (skWeight f)).symm
    _ = (∑' a, f a) + total f * total f := by
      rw [ENNReal.summable.tsum_sum ENNReal.summable]
      change (∑' a, f a) + (∑' xy : Skeleton α × Skeleton α,
        skWeight f xy.1 * skWeight f xy.2) = _
      congr 1
      rw [ENNReal.tsum_prod']
      simp_rw [ENNReal.tsum_mul_left]
      exact ENNReal.tsum_mul_right

noncomputable def historySum (s : Species) (z : ℝ≥0∞) : ℝ≥0∞ :=
  ∑' h : Hist s, z ^ size h

theorem skWeight_pow {s} (z : ℝ≥0∞) (t : Skeleton (Atom s)) :
    skWeight (fun a => z ^ size (atomHist a)) t = z ^ size (assemble t) := by
  induction t with
  | atom a => rfl
  | fork x y ix iy => simp [skWeight, assemble, size, pow_add, ix, iy]

theorem historySum_skeleton (s : Species) (z : ℝ≥0∞) :
    historySum s z = total (fun a : Atom s => z ^ size (atomHist a)) := by
  unfold historySum total
  rw [← (skeletonEquiv s).symm.tsum_eq (fun h : Hist s => z ^ size h)]
  exact tsum_congr (fun t => (skWeight_pow z t).symm)

#print axioms total_quadratic
#print axioms historySum_skeleton
end LiteralDL
```
<!-- END SOURCE -->

### LeastFixedPoint

<!-- SOURCE {"module": "LeastFixedPoint", "bytes": 2881, "sha256": "6c5d6b8fb1c9b5eff6d906ff3c8811d2035ca653d1d846c82f2980af20252904"} -->
```lean
import WeightedSkeleton
open scoped ENNReal
namespace LiteralDL

def skHeight {α : Type} : Skeleton α → Nat
  | .atom _ => 1
  | .fork x y => max (skHeight x) (skHeight y) + 1

noncomputable def cutWeight {α : Type} (d : Nat) (f : α → ℝ≥0∞) (t : Skeleton α) :=
  if skHeight t ≤ d then skWeight f t else 0
noncomputable def cutTotal {α : Type} (d : Nat) (f : α → ℝ≥0∞) := ∑' t, cutWeight d f t

theorem cutWeight_fork {α : Type} (d : Nat) (f : α → ℝ≥0∞) (x y : Skeleton α) :
    cutWeight (d+1) f (.fork x y) = cutWeight d f x * cutWeight d f y := by
  simp only [cutWeight, skHeight, skWeight]
  by_cases hx : skHeight x ≤ d <;> by_cases hy : skHeight y ≤ d <;>
    simp [hx, hy]

theorem cutTotal_succ {α : Type} (d : Nat) (f : α → ℝ≥0∞) :
    cutTotal (d+1) f = (∑' a, f a) + cutTotal d f * cutTotal d f := by
  calc
    cutTotal (d+1) f = ∑' u : α ⊕ (Skeleton α × Skeleton α),
        cutWeight (d+1) f ((rootEquiv α).symm u) :=
      ((rootEquiv α).symm.tsum_eq (cutWeight (d+1) f)).symm
    _ = (∑' a, f a) + cutTotal d f * cutTotal d f := by
      rw [ENNReal.summable.tsum_sum ENNReal.summable]
      change (∑' a, cutWeight (d+1) f (.atom a)) +
        (∑' xy : Skeleton α × Skeleton α, cutWeight (d+1) f (.fork xy.1 xy.2)) = _
      simp only [cutWeight_fork]
      have ha : ∀ a : α, cutWeight (d+1) f (.atom a) = f a := by
        intro a
        simp [cutWeight, skHeight, skWeight]
      simp_rw [ha]
      congr 1
      rw [ENNReal.tsum_prod']
      simp_rw [ENNReal.tsum_mul_left]
      exact ENNReal.tsum_mul_right

theorem cutTotal_zero {α : Type} (f : α → ℝ≥0∞) : cutTotal 0 f = 0 := by
  have hh : ∀ t : Skeleton α, ¬ skHeight t ≤ 0 := by
    intro t
    cases t <;> simp [skHeight]
  simp [cutTotal, cutWeight, hh]

theorem cutTotal_bound {α : Type} (f : α → ℝ≥0∞) (r : ℝ≥0∞)
    (hr : (∑' a, f a) + r*r ≤ r) (d : Nat) : cutTotal d f ≤ r := by
  induction d with
  | zero => rw [cutTotal_zero]; exact zero_le
  | succ d ih =>
    rw [cutTotal_succ]
    exact le_trans (add_le_add le_rfl (mul_le_mul' ih ih)) hr

/-- The nonnegative total is below every prefixed scalar bound. -/
theorem total_le_of_prefixed {α : Type} (f : α → ℝ≥0∞) (r : ℝ≥0∞)
    (hr : (∑' a, f a) + r*r ≤ r) : total f ≤ r := by
  classical
  unfold total
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro F
  let d := ∑ t ∈ F, skHeight t
  have hd : ∀ t ∈ F, skHeight t ≤ d := by
    intro t ht
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) ht
  have he : (∑ t ∈ F, skWeight f t) = ∑ t ∈ F, cutWeight d f t := by
    apply Finset.sum_congr rfl
    intro t ht
    simp [cutWeight, hd t ht]
  rw [he]
  exact le_trans (ENNReal.sum_le_tsum F) (cutTotal_bound f r hr d)

#print axioms total_le_of_prefixed
end LiteralDL
```
<!-- END SOURCE -->

### SourceWeighted

<!-- SOURCE {"module": "SourceWeighted", "bytes": 1218, "sha256": "515af092f29045a8f72d60929c699e934ebd7ffad7a71065031efbb548bba240"} -->
```lean
import LeastFixedPoint
open scoped ENNReal
namespace LiteralDL

def sizeEquiv (s : Species) : Hist s ≃ (n : Nat) × Fiber s n where
  toFun h := ⟨size h, ⟨h,rfl⟩⟩
  invFun h := h.2.1
  left_inv _ := rfl
  right_inv h := by rcases h with ⟨n,h,hn⟩; cases hn; rfl

theorem historySum_coeff (s : Species) (z : ℝ≥0∞) :
    historySum s z = ∑' n : Nat, (count s n : ℝ≥0∞) * z^n := by
  calc
    historySum s z = ∑' h : (n : Nat) × Fiber s n,
        z ^ size h.2.1 := ((sizeEquiv s).symm.tsum_eq _).symm
    _ = ∑' n : Nat, (count s n : ℝ≥0∞) * z^n := by
      rw [ENNReal.tsum_sigma']
      apply tsum_congr
      intro n
      have he : (fun h : Fiber s n => z ^ size h.1) = (fun _ : Fiber s n => z^n) := by
        funext h
        rw [h.2]
      rw [he]
      simp [count]

/-- A source-specific prefix bound, obtained without a recurrence-defined count. -/
theorem historySum_le_of_atom_prefixed (s : Species) (z r : ℝ≥0∞)
    (hr : (∑' a : Atom s, z ^ size (atomHist a)) + r*r ≤ r) :
    historySum s z ≤ r := by
  rw [historySum_skeleton]
  exact total_le_of_prefixed _ r hr

#print axioms historySum_coeff
#print axioms historySum_le_of_atom_prefixed
end LiteralDL
```
<!-- END SOURCE -->

### AtomMass

<!-- SOURCE {"module": "AtomMass", "bytes": 1619, "sha256": "14b9c6e105c9b771aa225ae4ac6758539d9c7f31551f312766dc9e0cab1eba33"} -->
```lean
import SourceWeighted
open scoped ENNReal
namespace LiteralDL

def atomNodeEquiv (a b : Species) : Atom (.node a b) ≃
    (Hist a ⊕ (Hist b ⊕ (Hist a × Hist b))) where
  toFun q := match q with
    | .keepLeft x => .inl x
    | .keepRight y => .inr (.inl y)
    | .both x y => .inr (.inr (x,y))
  invFun q := match q with
    | .inl x => .keepLeft x
    | .inr (.inl y) => .keepRight y
    | .inr (.inr xy) => .both xy.1 xy.2
  left_inv q := by cases q <;> rfl
  right_inv q := by rcases q with x | (y | ⟨x,y⟩) <;> rfl

theorem atomMass_node (a b : Species) (z : ℝ≥0∞) :
    (∑' q : Atom (.node a b), z ^ size (atomHist q)) =
      historySum a z + historySum b z + historySum a z * historySum b z := by
  rw [← (atomNodeEquiv a b).symm.tsum_eq (fun q => z ^ size (atomHist q))]
  rw [ENNReal.summable.tsum_sum ENNReal.summable]
  rw [ENNReal.summable.tsum_sum ENNReal.summable]
  change (∑' x : Hist a, z ^ size x) +
    ((∑' y : Hist b, z ^ size y) + (∑' xy : Hist a × Hist b, z ^ (size xy.1 + size xy.2))) = _
  simp_rw [pow_add]
  rw [ENNReal.tsum_prod']
  simp_rw [ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_mul_right]
  exact (add_assoc _ _ _).symm

theorem total_eq_of_mass_eq {α β : Type} (f : α → ℝ≥0∞) (g : β → ℝ≥0∞)
    (h : (∑' a, f a) = ∑' b, g b) : total f = total g := by
  apply le_antisymm
  · apply total_le_of_prefixed
    rw [h]
    exact (total_quadratic g).ge
  · apply total_le_of_prefixed
    rw [← h]
    exact (total_quadratic f).ge

#print axioms atomNodeEquiv
#print axioms atomMass_node
#print axioms total_eq_of_mass_eq
end LiteralDL
```
<!-- END SOURCE -->

### EndpointAudit

<!-- SOURCE {"module": "EndpointAudit", "bytes": 2806, "sha256": "e432baead9010f2c89502100283a0283551c9528eb049dddc26bd9811d1ce713"} -->
```lean
import SourceWeighted
#print axioms LiteralDL.Species
#print axioms LiteralDL.weight
#print axioms LiteralDL.weight_pos
#print axioms LiteralDL.Hist
#print axioms LiteralDL.size
#print axioms LiteralDL.size_pos
#print axioms LiteralDL.depth
#print axioms LiteralDL.depth_bound
#print axioms LiteralDL.pool
#print axioms LiteralDL.mem_pool
#print axioms LiteralDL.fiberFintype
#print axioms LiteralDL.count
#print axioms LiteralDL.duplicate
#print axioms LiteralDL.duplicate_injective
#print axioms LiteralDL.supermultiplicative
#print axioms LiteralDL.fiber_zero_empty
#print axioms LiteralDL.one
#print axioms LiteralDL.positiveFiber
#print axioms LiteralDL.count_pos
#print axioms LiteralDL.Event
#print axioms LiteralDL.EventTree
#print axioms LiteralDL.encode
#print axioms LiteralDL.Valid
#print axioms LiteralDL.encode_valid
#print axioms LiteralDL.valid_has_history
#print axioms LiteralDL.encode_ne_loss
#print axioms LiteralDL.encode_injective
#print axioms LiteralDL.sourceEquiv
#print axioms LiteralDL.splitEquiv
#print axioms LiteralDL.pairFintype
#print axioms LiteralDL.pairCount
#print axioms LiteralDL.nodeJoin
#print axioms LiteralDL.nodeCut
#print axioms LiteralDL.nodeEquiv
#print axioms LiteralDL.count_node
#print axioms LiteralDL.pairCount_eq
#print axioms LiteralDL.leafJoin
#print axioms LiteralDL.leafCut
#print axioms LiteralDL.leafEquiv
#print axioms LiteralDL.count_leaf
#print axioms LiteralDL.count_node_convolution
#print axioms LiteralDL.extantCount
#print axioms LiteralDL.encode_size
#print axioms LiteralDL.sourceFiberEquiv
#print axioms LiteralDL.swapRoot
#print axioms LiteralDL.swapRoot_size
#print axioms LiteralDL.swapRoot_twice
#print axioms LiteralDL.swapFiber
#print axioms LiteralDL.count_swap
#print axioms LiteralDL.count_zero
#print axioms LiteralDL.Skeleton
#print axioms LiteralDL.Atom
#print axioms LiteralDL.atomHist
#print axioms LiteralDL.assemble
#print axioms LiteralDL.cutSkeleton
#print axioms LiteralDL.assemble_cut
#print axioms LiteralDL.cut_assemble
#print axioms LiteralDL.skeletonEquiv
#print axioms LiteralDL.skeletonSize
#print axioms LiteralDL.assemble_size
#print axioms LiteralDL.rootEquiv
#print axioms LiteralDL.skWeight
#print axioms LiteralDL.total
#print axioms LiteralDL.total_quadratic
#print axioms LiteralDL.historySum
#print axioms LiteralDL.skWeight_pow
#print axioms LiteralDL.historySum_skeleton
#print axioms LiteralDL.skHeight
#print axioms LiteralDL.cutWeight
#print axioms LiteralDL.cutTotal
#print axioms LiteralDL.cutWeight_fork
#print axioms LiteralDL.cutTotal_succ
#print axioms LiteralDL.cutTotal_zero
#print axioms LiteralDL.cutTotal_bound
#print axioms LiteralDL.total_le_of_prefixed
#print axioms LiteralDL.sizeEquiv
#print axioms LiteralDL.historySum_coeff
#print axioms LiteralDL.historySum_le_of_atom_prefixed
```
<!-- END SOURCE -->

### ScalarBranch

<!-- SOURCE {"module": "ScalarBranch", "bytes": 687, "sha256": "c78303497a7380e33a8b6d16e04f4e84526b5247430fc71794523d5c0ae4e65a"} -->
```lean
import AtomMass
import Mathlib.Analysis.Real.Sqrt
namespace LiteralDL
noncomputable def catalanBranch (t : ℝ) : ℝ := (1 - Real.sqrt (1 - 4*t))/2

theorem catalanBranch_properties {t : ℝ} (ht : 0 ≤ t) (hq : t ≤ 1/4) :
    0 ≤ catalanBranch t ∧ catalanBranch t ≤ 1/2 ∧
      t + catalanBranch t * catalanBranch t = catalanBranch t := by
  have ha : 0 ≤ 1 - 4*t := by linarith
  have hb := Real.sqrt_nonneg (1 - 4*t)
  have hc : Real.sqrt (1 - 4*t) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have hd := Real.sq_sqrt ha
  unfold catalanBranch
  constructor
  · linarith
  constructor
  · linarith
  · nlinarith

#print axioms catalanBranch_properties
end LiteralDL
```
<!-- END SOURCE -->

### ScalarEvaluation

<!-- SOURCE {"module": "ScalarEvaluation", "bytes": 1644, "sha256": "98ae402407c7160787ae036fffd0ead5cdb0db8a19b83ca799ca5e4d0fe149b3"} -->
```lean
import ScalarBranch
open scoped ENNReal
namespace LiteralDL

theorem total_principal {α : Type} (f : α → ℝ≥0∞) {t : ℝ}
    (ht : 0 ≤ t) (hq : t ≤ 1/4) (hm : (∑' a, f a) = ENNReal.ofReal t) :
    total f = ENNReal.ofReal (catalanBranch t) := by
  obtain ⟨hr0, hrh, hroot⟩ := catalanBranch_properties ht hq
  have hb : total f ≤ ENNReal.ofReal (catalanBranch t) := by
    apply total_le_of_prefixed
    rw [hm, ← ENNReal.ofReal_mul hr0, ← ENNReal.ofReal_add ht (mul_nonneg hr0 hr0), hroot]
  have hf : total f ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb
  have he := congrArg ENNReal.toReal (total_quadratic f)
  rw [hm, ENNReal.toReal_add ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hf hf),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal ht] at he
  have hs : 0 ≤ (total f).toReal := ENNReal.toReal_nonneg
  have hsr : (total f).toReal ≤ catalanBranch t := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    simpa only [ENNReal.toReal_ofReal hr0] using this
  have hx : (total f).toReal = catalanBranch t := by nlinarith
  rw [← ENNReal.ofReal_toReal hf, hx]

theorem total_infinite_above {α : Type} (f : α → ℝ≥0∞) {t : ℝ}
    (ht : 1/4 < t) (hm : (∑' a, f a) = ENNReal.ofReal t) : total f = ⊤ := by
  by_contra hf
  have ht0 : 0 ≤ t := by linarith
  have he := congrArg ENNReal.toReal (total_quadratic f)
  rw [hm, ENNReal.toReal_add ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hf hf),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal ht0] at he
  nlinarith [sq_nonneg ((total f).toReal - 1/2)]

#print axioms total_principal
#print axioms total_infinite_above
end LiteralDL
```
<!-- END SOURCE -->

### HistoryEvaluation

<!-- SOURCE {"module": "HistoryEvaluation", "bytes": 1402, "sha256": "8c04464ad6eed77805e9d8d884f9c62d94a5de483e3c431dbae0fffcc43c6eca"} -->
```lean
import ScalarEvaluation
open scoped ENNReal
namespace LiteralDL

theorem atomMass_leaf (z : ℝ≥0∞) :
    (∑' q : Atom .leaf, z ^ size (atomHist q)) = z := by
  rw [tsum_eq_single Atom.extant]
  · simp [atomHist, size]
  · intro q h
    cases q
    exact (h rfl).elim

theorem historySum_leaf_principal {z : ℝ} (hz : 0 ≤ z) (hq : z ≤ 1/4) :
    historySum .leaf (ENNReal.ofReal z) = ENNReal.ofReal (catalanBranch z) := by
  rw [historySum_skeleton]
  exact total_principal _ hz hq (atomMass_leaf _)

theorem historySum_leaf_infinite {z : ℝ} (hz : 1/4 < z) :
    historySum .leaf (ENNReal.ofReal z) = ⊤ := by
  rw [historySum_skeleton]
  exact total_infinite_above _ hz (atomMass_leaf _)

theorem historySum_node_principal (a b : Species) (z : ℝ≥0∞) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (ha : historySum a z = ENNReal.ofReal x)
    (hb : historySum b z = ENNReal.ofReal y)
    (hq : x+y+x*y ≤ 1/4) :
    historySum (.node a b) z = ENNReal.ofReal (catalanBranch (x+y+x*y)) := by
  rw [historySum_skeleton]
  apply total_principal _ (by positivity) hq
  rw [atomMass_node, ha, hb, ← ENNReal.ofReal_mul hx,
    ← ENNReal.ofReal_add hx hy, ← ENNReal.ofReal_add (add_nonneg hx hy) (mul_nonneg hx hy)]

#print axioms atomMass_leaf
#print axioms historySum_leaf_principal
#print axioms historySum_leaf_infinite
#print axioms historySum_node_principal
end LiteralDL
```
<!-- END SOURCE -->

### BranchRegularity

<!-- SOURCE {"module": "BranchRegularity", "bytes": 1484, "sha256": "7ca57947772b15de3737bc28c07ef62616cb91b1172a956fb46ca9458fc63b3f"} -->
```lean
import HistoryEvaluation
import Mathlib.Topology.Order.IntermediateValue
namespace LiteralDL

noncomputable def branchValue : Species → ℝ → ℝ
  | .leaf, z => catalanBranch z
  | .node a b, z => catalanBranch (branchValue a z + branchValue b z + branchValue a z * branchValue b z)

theorem continuous_catalanBranch : Continuous catalanBranch := by
  unfold catalanBranch
  fun_prop

theorem branchValue_continuous (s : Species) : Continuous (branchValue s) := by
  induction s with
  | leaf => exact continuous_catalanBranch
  | node a b ia ib => exact continuous_catalanBranch.comp ((ia.add ib).add (ia.mul ib))

theorem catalanBranch_zero : catalanBranch 0 = 0 := by simp [catalanBranch]
theorem catalanBranch_quarter : catalanBranch (1/4) = 1/2 := by norm_num [catalanBranch]

theorem branchValue_zero (s : Species) : branchValue s 0 = 0 := by
  induction s <;> simp_all [branchValue, catalanBranch_zero]

theorem catalanBranch_strictMono : StrictMonoOn catalanBranch (Set.Icc 0 (1/4)) := by
  intro x hx y hy hxy
  obtain ⟨hx0,hxh,hxe⟩ := catalanBranch_properties hx.1 hx.2
  obtain ⟨hy0,hyh,hye⟩ := catalanBranch_properties hy.1 hy.2
  by_contra h
  have hle : catalanBranch y ≤ catalanBranch x := le_of_not_gt h
  have hprod := mul_nonneg (sub_nonneg.mpr hle)
    (show 0 ≤ 1 - catalanBranch x - catalanBranch y by linarith)
  nlinarith

#print axioms branchValue_continuous
#print axioms branchValue_zero
#print axioms catalanBranch_strictMono
end LiteralDL
```
<!-- END SOURCE -->

### CatalanAssociator

<!-- SOURCE {"module": "CatalanAssociator", "bytes": 852, "sha256": "9558b44afc6a606019328be98a17e0096e89a128306ed1c75f8156df2b88ddf8"} -->
```lean
import BranchRegularity
import Mathlib.Tactic.LinearCombination
namespace LiteralDL

theorem catalan_associator_identity {a b c x y : ℝ}
    (hx : a+b+a*b+x*x=x) (hy : c+b+c*b+y*y=y) :
    ((1+c)*x+c-((1+a)*y+a))*(1-x-y) = (a-c)*(x+y+x*y) := by
  linear_combination (1+a)*hy - (1+c)*hx

theorem catalan_associator_strict {a b c x y : ℝ}
    (hx : a+b+a*b+x*x=x) (hy : c+b+c*b+y*y=y)
    (hac : c < a) (hx0 : 0 < x) (hy0 : 0 ≤ y) (hxy : x+y < 1) :
    (1+a)*y+a < (1+c)*x+c := by
  have hid := catalan_associator_identity hx hy
  have hp : 0 < (a-c)*(x+y+x*y) :=
    mul_pos (sub_pos.mpr hac) (by positivity)
  have hd : 0 < 1-x-y := by linarith
  have : 0 < (1+c)*x+c-((1+a)*y+a) :=
    (mul_pos_iff_of_pos_right hd).mp (hid.symm ▸ hp)
  linarith

#print axioms catalan_associator_identity
#print axioms catalan_associator_strict
end LiteralDL
```
<!-- END SOURCE -->

### HistoryOrder

<!-- SOURCE {"module": "HistoryOrder", "bytes": 1705, "sha256": "f2969071f4489d94a5c91f978fe54c9793c9f1cc13ef1b68ab070db68b713852"} -->
```lean
import BranchRegularity
open scoped ENNReal
namespace LiteralDL

theorem mass_le_total {α : Type} (f : α → ℝ≥0∞) : (∑' a, f a) ≤ total f := by
  calc
    (∑' a, f a) ≤ (∑' a, f a) + total f * total f := le_self_add
    _ = total f := (total_quadratic f).symm

theorem historySum_node_ge_left (a b : Species) (z : ℝ≥0∞) :
    historySum a z ≤ historySum (.node a b) z := by
  rw [historySum_skeleton (.node a b)]
  have h := mass_le_total (fun q : Atom (.node a b) => z ^ size (atomHist q))
  rw [atomMass_node] at h
  exact le_trans (le_trans le_self_add le_self_add) h

theorem historySum_node_ge_right (a b : Species) (z : ℝ≥0∞) :
    historySum b z ≤ historySum (.node a b) z := by
  rw [historySum_skeleton (.node a b)]
  have h := mass_le_total (fun q : Atom (.node a b) => z ^ size (atomHist q))
  rw [atomMass_node] at h
  exact le_trans (le_trans le_add_self le_self_add) h

theorem historySum_mono (s : Species) : Monotone (historySum s) := by
  intro z w h
  exact ENNReal.tsum_le_tsum (fun _ => pow_le_pow_left' h _)

theorem historySum_node_infinite (a b : Species) (z : ℝ≥0∞) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (ha : historySum a z = ENNReal.ofReal x)
    (hb : historySum b z = ENNReal.ofReal y)
    (hq : 1/4 < x+y+x*y) : historySum (.node a b) z = ⊤ := by
  rw [historySum_skeleton]
  apply total_infinite_above _ hq
  rw [atomMass_node, ha, hb, ← ENNReal.ofReal_mul hx,
    ← ENNReal.ofReal_add hx hy, ← ENNReal.ofReal_add (add_nonneg hx hy) (mul_nonneg hx hy)]

#print axioms historySum_node_ge_left
#print axioms historySum_node_ge_right
#print axioms historySum_mono
#print axioms historySum_node_infinite
end LiteralDL
```
<!-- END SOURCE -->

### ActualThreshold

<!-- SOURCE {"module": "ActualThreshold", "bytes": 5409, "sha256": "ee2377e55440b4aeaf494d2d5bc85164d8641e7e35405bd4e3f4d6fd218bd8d0"} -->
```lean
import HistoryOrder
open scoped ENNReal
namespace LiteralDL
/-- A property of the actual source sum, constructed below, never postulated. -/
structure ActualThreshold (s : Species) where
  radius : ℝ
  positive : 0 < radius
  quarter : radius ≤ 1/4
  representation : ∀ z ∈ Set.Icc 0 radius,
    historySum s (ENNReal.ofReal z) = ENNReal.ofReal (branchValue s z)
  bounds : ∀ z ∈ Set.Icc 0 radius, 0 ≤ branchValue s z ∧ branchValue s z ≤ 1/2
  increasing : StrictMonoOn (branchValue s) (Set.Icc 0 radius)
  endpoint : branchValue s radius = 1/2
  infinite : ∀ z, radius < z → historySum s (ENNReal.ofReal z) = ⊤

noncomputable def leafThreshold : ActualThreshold .leaf where
  radius := 1/4
  positive := by norm_num
  quarter := le_rfl
  representation := by intro z hz; exact historySum_leaf_principal hz.1 hz.2
  bounds := by
    intro z hz
    obtain ⟨h0,h1,_⟩ := catalanBranch_properties hz.1 hz.2
    exact ⟨h0,h1⟩
  increasing := catalanBranch_strictMono
  endpoint := catalanBranch_quarter
  infinite := by intro z hz; exact historySum_leaf_infinite hz

noncomputable def nodeThreshold {a b : Species}
    (A : ActualThreshold a) (B : ActualThreshold b) : ActualThreshold (.node a b) := by
  let R := min A.radius B.radius
  let q := fun z => branchValue a z + branchValue b z + branchValue a z * branchValue b z
  have hR : 0 < R := lt_min A.positive B.positive
  have hRa : R ≤ A.radius := min_le_left _ _
  have hRb : R ≤ B.radius := min_le_right _ _
  have hq0 : q 0 = 0 := by simp [q, branchValue_zero]
  have hqc : Continuous q := ((branchValue_continuous a).add (branchValue_continuous b)).add
    ((branchValue_continuous a).mul (branchValue_continuous b))
  have hqm : StrictMonoOn q (Set.Icc 0 R) := by
    intro x hx y hy hxy
    have hax := A.increasing ⟨hx.1, hx.2.trans hRa⟩ ⟨hy.1, hy.2.trans hRa⟩ hxy
    have hby := B.increasing ⟨hx.1, hx.2.trans hRb⟩ ⟨hy.1, hy.2.trans hRb⟩ hxy
    have hx0 := (B.bounds x ⟨hx.1,hx.2.trans hRb⟩).1
    have hy0 := (A.bounds y ⟨hy.1,hy.2.trans hRa⟩).1
    exact add_lt_add_of_lt_of_le (add_lt_add hax hby) (mul_le_mul hax.le hby.le hx0 hy0)
  have hqR : 1/2 ≤ q R := by
    have ha := A.bounds R ⟨hR.le,hRa⟩
    have hb := B.bounds R ⟨hR.le,hRb⟩
    have hab := mul_nonneg ha.1 hb.1
    rcases le_total A.radius B.radius with h | h
    · have he : R = A.radius := min_eq_left h
      have hv : branchValue a R = 1/2 := he ▸ A.endpoint
      dsimp [q]; linarith
    · have he : R = B.radius := min_eq_right h
      have hv : branchValue b R = 1/2 := he ▸ B.endpoint
      dsimp [q]; linarith
  have hex : ∃ r ∈ Set.Icc 0 R, q r = 1/4 := intermediate_value_Icc hR.le hqc.continuousOn
    (show (1/4 : ℝ) ∈ Set.Icc (q 0) (q R) from ⟨by rw [hq0]; norm_num, by linarith⟩)
  let r := Classical.choose hex
  have hr : r ∈ Set.Icc 0 R := (Classical.choose_spec hex).1
  have he : q r = 1/4 := (Classical.choose_spec hex).2
  have hr0 : 0 < r := by
    have : r ≠ 0 := by intro hz; rw [hz,hq0] at he; norm_num at he
    exact lt_of_le_of_ne hr.1 (Ne.symm this)
  have hrR : r < R := by
    have : r ≠ R := by intro hz; rw [hz] at he; linarith
    exact lt_of_le_of_ne hr.2 this
  have hi : ∀ z ∈ Set.Icc 0 r, 0 ≤ q z ∧ q z ≤ 1/4 := by
    intro z hz
    have ha := A.bounds z ⟨hz.1,hz.2.trans (hrR.le.trans hRa)⟩
    have hb := B.bounds z ⟨hz.1,hz.2.trans (hrR.le.trans hRb)⟩
    constructor
    · exact add_nonneg (add_nonneg ha.1 hb.1) (mul_nonneg ha.1 hb.1)
    · rw [← he]
      exact hqm.monotoneOn ⟨hz.1,hz.2.trans hrR.le⟩ hr hz.2
  have hdiv : ∀ z, r < z → z ≤ R → historySum (.node a b) (ENNReal.ofReal z) = ⊤ := by
    intro z hz hzR
    have hz0 := hr0.le.trans hz.le
    have ha := A.bounds z ⟨hz0,hzR.trans hRa⟩
    have hb := B.bounds z ⟨hz0,hzR.trans hRb⟩
    apply historySum_node_infinite a b _ ha.1 hb.1
      (A.representation z ⟨hz0,hzR.trans hRa⟩) (B.representation z ⟨hz0,hzR.trans hRb⟩)
    change 1/4 < q z
    rw [← he]
    exact hqm hr ⟨hz0,hzR⟩ hz
  refine ⟨r,hr0,hrR.le.trans (hRa.trans A.quarter),?_,?_,?_,?_,?_⟩
  · intro z hz
    exact historySum_node_principal a b _
      (A.bounds z ⟨hz.1,hz.2.trans (hrR.le.trans hRa)⟩).1
      (B.bounds z ⟨hz.1,hz.2.trans (hrR.le.trans hRb)⟩).1
      (A.representation z ⟨hz.1,hz.2.trans (hrR.le.trans hRa)⟩)
      (B.representation z ⟨hz.1,hz.2.trans (hrR.le.trans hRb)⟩) (hi z hz).2
  · intro z hz
    obtain ⟨h0,h1,_⟩ := catalanBranch_properties (hi z hz).1 (hi z hz).2
    exact ⟨h0,h1⟩
  · intro x hx y hy hxy
    exact catalanBranch_strictMono (hi x hx) (hi y hy)
      (hqm ⟨hx.1,hx.2.trans hrR.le⟩ ⟨hy.1,hy.2.trans hrR.le⟩ hxy)
  · change catalanBranch (q r) = 1/2
    rw [he, catalanBranch_quarter]
  · intro z hz
    by_cases hzR : z ≤ R
    · exact hdiv z hz hzR
    · have hw : r < (r+R)/2 := by linarith
      have hwR : (r+R)/2 ≤ R := by linarith
      have hd := hdiv ((r+R)/2) hw hwR
      apply top_unique
      rw [← hd]
      apply historySum_mono
      apply ENNReal.ofReal_le_ofReal
      linarith

noncomputable def actualThreshold : (s : Species) → ActualThreshold s
  | .leaf => leafThreshold
  | .node a b => nodeThreshold (actualThreshold a) (actualThreshold b)

#print axioms leafThreshold
#print axioms nodeThreshold
#print axioms actualThreshold
end LiteralDL
```
<!-- END SOURCE -->

### ClippedCatalan

<!-- SOURCE {"module": "ClippedCatalan", "bytes": 1948, "sha256": "af77c1f426ed8226fd29a83b872eb0ba7054e5988f711fc022ec5cc18ca49298"} -->
```lean
import CatalanAssociator
namespace LiteralDL

theorem catalanBranch_global_bounds {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ catalanBranch q ∧ catalanBranch q ≤ 1/2 := by
  have hs := Real.sqrt_nonneg (1-4*q)
  have ht : Real.sqrt (1-4*q) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  constructor <;> unfold catalanBranch <;> linarith

theorem catalanBranch_saturated {q : ℝ} (hq : 1/4 ≤ q) : catalanBranch q = 1/2 := by
  have hs : Real.sqrt (1-4*q) = 0 := Real.sqrt_eq_zero_of_nonpos (by linarith)
  simp [catalanBranch, hs]

theorem catalanBranch_mono : Monotone catalanBranch := by
  intro x y h
  have hs : Real.sqrt (1-4*y) ≤ Real.sqrt (1-4*x) := Real.sqrt_le_sqrt (by linarith)
  unfold catalanBranch
  linarith

noncomputable def mergeValue (a b : ℝ) : ℝ := catalanBranch (a+b+a*b)

theorem mergeValue_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ mergeValue a b := (catalanBranch_global_bounds (by positivity)).1

theorem mergeValue_half {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    mergeValue a b ≤ 1/2 := (catalanBranch_global_bounds (by positivity)).2

theorem mergeValue_mono {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hac : a ≤ c) (hbd : b ≤ d) : mergeValue a b ≤ mergeValue c d := by
  apply catalanBranch_mono
  have hc := ha.trans hac
  have hm := mul_le_mul hac hbd hb hc
  linarith

theorem mergeValue_comm (a b : ℝ) : mergeValue a b = mergeValue b a := by
  unfold mergeValue
  congr 1
  ring

theorem mergeValue_ge_left {a b : ℝ} (ha : 0 ≤ a) (hh : a ≤ 1/2) (hb : 0 ≤ b) :
    a ≤ mergeValue a b := by
  by_cases hq : a+b+a*b ≤ 1/4
  · obtain ⟨hx0,hxh,hxe⟩ := catalanBranch_properties (by positivity : 0 ≤ a+b+a*b) hq
    change a ≤ catalanBranch (a+b+a*b)
    nlinarith [mul_nonneg ha hb, sq_nonneg (catalanBranch (a+b+a*b))]
  · unfold mergeValue
    rw [catalanBranch_saturated (le_of_not_ge hq)]
    exact hh

#print axioms mergeValue_ge_left
end LiteralDL
```
<!-- END SOURCE -->

### CatalanDerivative

<!-- SOURCE {"module": "CatalanDerivative", "bytes": 1575, "sha256": "04019b62d0775ec340e97c2459555d12522c5f16a9709e725ae2e2e416ee61cf"} -->
```lean
import ClippedCatalan
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
namespace LiteralDL

theorem hasDerivAt_catalanBranch {q : ℝ} (hq : q < 1/4) :
    HasDerivAt catalanBranch (1 / Real.sqrt (1-4*q)) q := by
  have hp : 0 < 1-4*q := by linarith
  have hs : Real.sqrt (1-4*q) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have hd := ((hasDerivAt_const q (1:ℝ)).sub
    ((hasDerivAt_id q).const_mul 4)).sqrt hp.ne'
  have hc := ((hasDerivAt_const q (1:ℝ)).sub hd).div_const 2
  dsimp at hc
  convert hc using 1
  · rfl
  · field_simp [hs]
    ring

noncomputable def logConjugate (x : ℝ) : ℝ :=
  Real.log (1+catalanBranch (Real.exp x-1))

theorem hasDerivAt_logConjugate {x : ℝ} (hx : 0 ≤ x)
    (hxu : x < Real.log (5/4)) :
    HasDerivAt logConjugate
      (Real.exp x / ((1+catalanBranch (Real.exp x-1))*Real.sqrt (1-4*(Real.exp x-1)))) x := by
  have he0 : 0 ≤ Real.exp x-1 := by have := Real.one_le_exp hx; linarith
  have he1 : Real.exp x-1 < 1/4 := by
    have h : Real.exp x < (5/4:ℝ) := (Real.exp_lt_exp.mpr hxu).trans_eq (Real.exp_log (by norm_num))
    linarith
  have hc := catalanBranch_global_bounds he0
  have hn : 1+catalanBranch (Real.exp x-1) ≠ 0 := by linarith
  have hd := (hasDerivAt_catalanBranch he1).comp x ((Real.hasDerivAt_exp x).sub_const 1)
  have hl := ((hasDerivAt_const x (1:ℝ)).add hd).log hn
  convert hl using 1
  · rfl
  · dsimp
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

#print axioms hasDerivAt_logConjugate
end LiteralDL
```
<!-- END SOURCE -->

### RealAssociator

<!-- SOURCE {"module": "RealAssociator", "bytes": 1776, "sha256": "c18e24444937abda69bea7466d9dfa3566ff48821dd29b1fcb1aea098d88c94c"} -->
```lean
import ClippedCatalan
namespace LiteralDL

theorem mergeValue_associator {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hac : c ≤ a) :
    mergeValue a (mergeValue b c) ≤ mergeValue (mergeValue a b) c := by
  rw [mergeValue_comm b c]
  by_cases hq : 1/4 ≤ a+b+a*b
  · have hx : mergeValue a b = 1/2 := catalanBranch_saturated hq
    rw [hx]
    have hs : mergeValue (1/2) c = 1/2 := by
      apply catalanBranch_saturated
      nlinarith
    rw [hs]
    exact mergeValue_half ha (mergeValue_nonneg hc hb)
  · have hqab : a+b+a*b < 1/4 := lt_of_not_ge hq
    have hqcb : c+b+c*b ≤ a+b+a*b := by
      have hm := mul_le_mul_of_nonneg_right hac hb
      linarith
    obtain ⟨hx0,hxh,hxe⟩ := catalanBranch_properties (by positivity : 0 ≤ a+b+a*b) hqab.le
    obtain ⟨hy0,hyh,hye⟩ := catalanBranch_properties (by positivity : 0 ≤ c+b+c*b) (hqcb.trans hqab.le)
    have hxlt : catalanBranch (a+b+a*b) < 1/2 := by
      have h := catalanBranch_strictMono
        (show a+b+a*b ∈ Set.Icc 0 (1/4) from ⟨by positivity,hqab.le⟩)
        (show (1/4:ℝ) ∈ Set.Icc 0 (1/4) from ⟨by norm_num,le_rfl⟩) hqab
      simpa only [catalanBranch_quarter] using h
    have hd : 0 < 1-catalanBranch (a+b+a*b)-catalanBranch (c+b+c*b) := by linarith
    have hid := catalan_associator_identity hxe hye
    have hp : 0 ≤ (a-c)*(catalanBranch (a+b+a*b)+catalanBranch (c+b+c*b)+
        catalanBranch (a+b+a*b)*catalanBranch (c+b+c*b)) := by positivity
    have hdiff := (mul_nonneg_iff_of_pos_right hd).mp (hid.symm ▸ hp)
    apply catalanBranch_mono
    change a + catalanBranch (c+b+c*b) + a*catalanBranch (c+b+c*b) ≤
      catalanBranch (a+b+a*b) + c + catalanBranch (a+b+a*b)*c
    nlinarith

#print axioms mergeValue_associator
end LiteralDL
```
<!-- END SOURCE -->

### ThresholdFacts

<!-- SOURCE {"module": "ThresholdFacts", "bytes": 1561, "sha256": "d10d2af7884d5f715c6b7f1d08eb4f007e807af97c6fc22808fedf5b16a55be5"} -->
```lean
import ActualThreshold
open scoped ENNReal
namespace LiteralDL
noncomputable def rho (s : Species) : ℝ := (actualThreshold s).radius

theorem rho_pos (s : Species) : 0 < rho s := (actualThreshold s).positive

theorem historySum_at_rho (s : Species) :
    historySum s (ENNReal.ofReal (rho s)) = ENNReal.ofReal (1/2) := by
  rw [(actualThreshold s).representation (rho s) ⟨(rho_pos s).le,le_rfl⟩]
  exact congrArg ENNReal.ofReal (actualThreshold s).endpoint

theorem historySum_finite_iff (s : Species) {z : ℝ} (hz : 0 ≤ z) :
    historySum s (ENNReal.ofReal z) < ⊤ ↔ z ≤ rho s := by
  constructor
  · intro h
    by_contra hn
    rw [(actualThreshold s).infinite z (lt_of_not_ge hn)] at h
    exact (lt_irrefl _ h)
  · intro h
    rw [(actualThreshold s).representation z ⟨hz,h⟩]
    exact ENNReal.ofReal_lt_top

theorem count_exponential_bound (s : Species) (n : Nat) :
    (count s n : ℝ) * rho s ^ n ≤ 1/2 := by
  have h : (count s n : ℝ≥0∞) * (ENNReal.ofReal (rho s)) ^ n ≤ ENNReal.ofReal (1/2) := by
    calc
      _ ≤ ∑' m : Nat, (count s m : ℝ≥0∞) * (ENNReal.ofReal (rho s)) ^ m := ENNReal.le_tsum n
      _ = historySum s (ENNReal.ofReal (rho s)) := (historySum_coeff _ _).symm
      _ = _ := historySum_at_rho s
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  simpa [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (rho_pos s).le] using hr

#print axioms rho_pos
#print axioms historySum_at_rho
#print axioms historySum_finite_iff
#print axioms count_exponential_bound
end LiteralDL
```
<!-- END SOURCE -->

### ConjugateSlope

<!-- SOURCE {"module": "ConjugateSlope", "bytes": 2108, "sha256": "3644958867104896feea7f8b5c163200a14c65c72ffebe7883db445f1c217adb"} -->
```lean
import CatalanDerivative
namespace LiteralDL
noncomputable def conjugateSlope (u : ℝ) : ℝ := (1+u-u*u)/(1-u-2*u*u)

theorem conjugateSlope_den_pos {u : ℝ} (hu : 0 ≤ u) (hh : u < 1/2) :
    0 < 1-u-2*u*u := by
  have h : 0 < (1+u)*(1-2*u) := mul_pos (by linarith) (by linarith)
  nlinarith

theorem conjugateSlope_gt_one {u : ℝ} (hu : 0 < u) (hh : u < 1/2) :
    1 < conjugateSlope u := by
  unfold conjugateSlope
  apply (lt_div_iff₀ (conjugateSlope_den_pos hu.le hh)).mpr
  nlinarith [sq_nonneg u]

theorem conjugateSlope_strictMono : StrictMonoOn conjugateSlope (Set.Ico 0 (1/2)) := by
  intro u hu v hv huv
  unfold conjugateSlope
  apply (div_lt_div_iff₀ (conjugateSlope_den_pos hu.1 hu.2)
    (conjugateSlope_den_pos hv.1 hv.2)).mpr
  have hu0 : 0 ≤ u := hu.1
  have hv0 : 0 ≤ v := hv.1
  have hp : 0 < (v-u)*(2+u+v+3*u*v) :=
    mul_pos (sub_pos.mpr huv) (by positivity)
  nlinarith

theorem deriv_logConjugate {x : ℝ} (hx : 0 ≤ x) (hxu : x < Real.log (5/4)) :
    deriv logConjugate x = conjugateSlope (catalanBranch (Real.exp x-1)) := by
  rw [(hasDerivAt_logConjugate hx hxu).deriv]
  have he0 : 0 ≤ Real.exp x-1 := by have := Real.one_le_exp hx; linarith
  have he1 : Real.exp x-1 < 1/4 := by
    have h := (Real.exp_lt_exp.mpr hxu).trans_eq (Real.exp_log (by norm_num : (0:ℝ) < 5/4))
    linarith
  have he := (catalanBranch_properties he0 he1.le).2.2
  have hs : Real.sqrt (1-4*(Real.exp x-1)) = 1-2*catalanBranch (Real.exp x-1) := by
    unfold catalanBranch
    ring
  unfold conjugateSlope
  rw [hs]
  have hn : Real.exp x = 1+catalanBranch (Real.exp x-1)-
      catalanBranch (Real.exp x-1)*catalanBranch (Real.exp x-1) := by linarith
  have hden : (1+catalanBranch (Real.exp x-1))*(1-2*catalanBranch (Real.exp x-1)) =
      1-catalanBranch (Real.exp x-1)-2*catalanBranch (Real.exp x-1)*catalanBranch (Real.exp x-1) := by ring
  rw [hden]
  exact congrArg (fun v : ℝ => v / (1-catalanBranch (Real.exp x-1)-
    2*catalanBranch (Real.exp x-1)*catalanBranch (Real.exp x-1))) hn

#print axioms conjugateSlope_strictMono
#print axioms deriv_logConjugate
end LiteralDL
```
<!-- END SOURCE -->

### LogFekete

<!-- SOURCE {"module": "LogFekete", "bytes": 2416, "sha256": "15d54f9d7b83b58fe82acabf7a38886c156f9ae7108619f821795c51c6e72095"} -->
```lean
import ThresholdFacts
import Mathlib.Analysis.Subadditive
import Mathlib.Analysis.SpecialFunctions.Log.Basic
namespace LiteralDL
noncomputable def negativeLogCount (s : Species) (n : Nat) : ℝ :=
  if n = 0 then 0 else -Real.log (count s n)

theorem count_cast_pos {s : Species} {n : Nat} (hn : n ≠ 0) : 0 < (count s n : ℝ) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact_mod_cast count_pos s m

theorem negativeLogCount_subadditive (s : Species) : Subadditive (negativeLogCount s) := by
  intro m n
  by_cases hm : m = 0
  · simp [hm, negativeLogCount]
  by_cases hn : n = 0
  · simp [hn, negativeLogCount]
  have hm0 : 0 < (count s m : ℝ) := count_cast_pos hm
  have hn0 : 0 < (count s n : ℝ) := count_cast_pos hn
  have hmul : (count s m : ℝ) * count s n ≤ count s (m+n) := by
    exact_mod_cast supermultiplicative s m n
  have hl := Real.log_le_log (mul_pos hm0 hn0) hmul
  rw [Real.log_mul hm0.ne' hn0.ne'] at hl
  have hmn : m+n ≠ 0 := by omega
  simp only [negativeLogCount, ite_eq_right hm, ite_eq_right hn, ite_eq_right hmn]
  linarith

theorem negativeLogCount_bddBelow (s : Species) :
    BddBelow (Set.range (fun n : Nat => negativeLogCount s n / n)) := by
  refine ⟨Real.log (rho s), ?_⟩
  intro y hy
  obtain ⟨n,rfl⟩ := hy
  by_cases hn : n = 0
  · simp only [hn, negativeLogCount, Nat.cast_zero, div_zero]
    exact Real.log_nonpos (rho_pos s).le (by have := (actualThreshold s).quarter; change rho s ≤ 1/4 at this; linarith)
  have hc := count_cast_pos (s := s) hn
  have hr := rho_pos s
  have hb : (count s n : ℝ) * rho s ^ n ≤ 1 := le_trans (count_exponential_bound s n) (by norm_num)
  have hl := Real.log_le_log (mul_pos hc (pow_pos hr n)) hb
  rw [Real.log_mul hc.ne' (pow_pos hr n).ne', Real.log_pow, Real.log_one] at hl
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  change Real.log (rho s) ≤ negativeLogCount s n / (n : ℝ)
  simp only [negativeLogCount, ite_eq_right hn]
  apply (le_div_iff₀ hn0).mpr
  nlinarith

theorem negativeLogCount_tendsto (s : Species) :
    Filter.Tendsto (fun n : Nat => negativeLogCount s n / n) Filter.atTop
      (nhds (negativeLogCount_subadditive s).lim) :=
  (negativeLogCount_subadditive s).tendsto_lim (negativeLogCount_bddBelow s)

#print axioms negativeLogCount_subadditive
#print axioms negativeLogCount_bddBelow
#print axioms negativeLogCount_tendsto
end LiteralDL
```
<!-- END SOURCE -->

### ActualRootLimit

<!-- SOURCE {"module": "ActualRootLimit", "bytes": 958, "sha256": "2991e373022b7ff7a9d20b1fbd19bac939b7d2470d3758fbf7f10ba00253ada4"} -->
```lean
import LogFekete
import Mathlib.Analysis.SpecialFunctions.Pow.Real
namespace LiteralDL
noncomputable def growth (s : Species) : ℝ := Real.exp (-(negativeLogCount_subadditive s).lim)

theorem growth_pos (s : Species) : 0 < growth s := Real.exp_pos _

theorem actual_root_limit (s : Species) :
    Filter.Tendsto (fun n : Nat => (count s n : ℝ) ^ (1 / (n : ℝ)))
      Filter.atTop (nhds (growth s)) := by
  have h := (Real.continuous_exp.tendsto (-(negativeLogCount_subadditive s).lim)).comp
    (negativeLogCount_tendsto s).neg
  apply h.congr'
  apply Filter.eventually_atTop.mpr
  refine ⟨1, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by omega
  change Real.exp (-(negativeLogCount s n / (n : ℝ))) = (count s n : ℝ) ^ (1 / (n : ℝ))
  rw [Real.rpow_def_of_pos (count_cast_pos (s := s) hn0)]
  apply congrArg Real.exp
  simp only [negativeLogCount, ite_eq_right hn0]
  ring

#print axioms growth_pos
#print axioms actual_root_limit
end LiteralDL
```
<!-- END SOURCE -->

### LogConjugateConvex

<!-- SOURCE {"module": "LogConjugateConvex", "bytes": 2022, "sha256": "8f13c8201b3f86ff2bbc991b5bef32424058f8194c39dc733fa5312f230f3235"} -->
```lean
import ConjugateSlope
namespace LiteralDL

theorem conjugate_input_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.exp x-1 := by
  have := Real.one_le_exp hx
  linarith

theorem conjugate_input_lt {x : ℝ} (hx : x < Real.log (5/4)) : Real.exp x-1 < 1/4 := by
  have h := (Real.exp_lt_exp.mpr hx).trans_eq (Real.exp_log (by norm_num : (0:ℝ) < 5/4))
  linarith

theorem logConjugate_continuousOn :
    ContinuousOn logConjugate (Set.Icc 0 (Real.log (5/4))) := by
  apply ContinuousOn.log
  · exact (continuous_const.add (continuous_catalanBranch.comp
      (Real.continuous_exp.sub continuous_const))).continuousOn
  · intro x hx
    have hc := (catalanBranch_global_bounds (conjugate_input_nonneg hx.1)).1
    linarith

theorem logConjugate_strictConvex :
    StrictConvexOn ℝ (Set.Icc 0 (Real.log (5/4))) logConjugate := by
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Icc _ _) logConjugate_continuousOn
  rw [interior_Icc]
  intro x hx y hy hxy
  rw [deriv_logConjugate hx.1.le hx.2,deriv_logConjugate hy.1.le hy.2]
  have hqx0 := conjugate_input_nonneg hx.1.le
  have hqy0 := conjugate_input_nonneg hy.1.le
  have hqx1 := conjugate_input_lt hx.2
  have hqy1 := conjugate_input_lt hy.2
  have hux0 := (catalanBranch_global_bounds hqx0).1
  have huy0 := (catalanBranch_global_bounds hqy0).1
  have hux1 : catalanBranch (Real.exp x-1) < 1/2 := by
    have h := catalanBranch_strictMono ⟨hqx0,hqx1.le⟩
      (show (1/4:ℝ) ∈ Set.Icc 0 (1/4) from ⟨by norm_num,le_rfl⟩) hqx1
    simpa only [catalanBranch_quarter] using h
  have huy1 : catalanBranch (Real.exp y-1) < 1/2 := by
    have h := catalanBranch_strictMono ⟨hqy0,hqy1.le⟩
      (show (1/4:ℝ) ∈ Set.Icc 0 (1/4) from ⟨by norm_num,le_rfl⟩) hqy1
    simpa only [catalanBranch_quarter] using h
  apply conjugateSlope_strictMono ⟨hux0,hux1⟩ ⟨huy0,huy1⟩
  exact catalanBranch_strictMono ⟨hqx0,hqx1.le⟩ ⟨hqy0,hqy1.le⟩
    (sub_lt_sub_right (Real.exp_lt_exp.mpr hxy) 1)

#print axioms logConjugate_strictConvex
end LiteralDL
```
<!-- END SOURCE -->

### GeometricBridge

<!-- SOURCE {"module": "GeometricBridge", "bytes": 1515, "sha256": "e6fd52f129ea9915ee33243a906bf4a79ff2cf7f40a3eea9ca4feb89b75cd755"} -->
```lean
import ActualRootLimit
import Mathlib.Analysis.SpecificLimits.Basic
open scoped ENNReal
namespace LiteralDL

theorem count_le_growth_pow (s : Species) (n : Nat) :
    (count s n : ℝ) ≤ growth s ^ n := by
  by_cases hn : n = 0
  · simp [hn, count_zero]
  have hc := count_cast_pos (s := s) hn
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hl := (negativeLogCount_subadditive s).lim_le_div (negativeLogCount_bddBelow s) hn
  simp only [negativeLogCount, ite_eq_right hn] at hl
  have hd := (le_div_iff₀ hn0).mp hl
  unfold growth
  rw [← Real.exp_nat_mul, ← Real.exp_log hc]
  exact Real.exp_le_exp.mpr (by nlinarith)

theorem finite_below_growth (s : Species) {z : ℝ} (hz : 0 ≤ z) (hzg : growth s * z < 1) :
    historySum s (ENNReal.ofReal z) < ⊤ := by
  have hg := growth_pos s
  have hs : Summable (fun n : Nat => (count s n : ℝ) * z^n) := by
    apply (summable_geometric_of_lt_one (mul_nonneg hg.le hz) hzg).of_nonneg_of_le
    · intro n; positivity
    · intro n
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (count_le_growth_pow s n) (pow_nonneg hz n)
  rw [historySum_coeff]
  have he : (fun n : Nat => ENNReal.ofReal ((count s n : ℝ) * z^n)) =
      (fun n : Nat => (count s n : ℝ≥0∞) * ENNReal.ofReal z ^ n) := by
    funext n
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_pow hz]
    simp
  rw [← he]
  exact hs.tsum_ofReal_lt_top

#print axioms count_le_growth_pow
#print axioms finite_below_growth
end LiteralDL
```
<!-- END SOURCE -->

### LogConjugateExpansive

<!-- SOURCE {"module": "LogConjugateExpansive", "bytes": 1683, "sha256": "65ff16048e4059e7fc83d81c9160130d33a93f36ec147c1373d25e38a9c38c4c"} -->
```lean
import LogConjugateConvex
namespace LiteralDL

theorem logConjugate_zero : logConjugate 0 = 0 := by
  simp [logConjugate,catalanBranch_zero]

theorem conjugate_branch_interior {x : ℝ} (hx : 0 < x) (hxu : x < Real.log (5/4)) :
    0 < catalanBranch (Real.exp x-1) ∧ catalanBranch (Real.exp x-1) < 1/2 := by
  have hq0 : 0 < Real.exp x-1 := by
    have h := Real.exp_lt_exp.mpr hx
    rw [Real.exp_zero] at h
    linarith
  have hq1 := conjugate_input_lt hxu
  constructor
  · have h := catalanBranch_strictMono
      (show (0:ℝ) ∈ Set.Icc 0 (1/4) from ⟨le_rfl,by norm_num⟩) ⟨hq0.le,hq1.le⟩ hq0
    simpa only [catalanBranch_zero] using h
  · have h := catalanBranch_strictMono ⟨hq0.le,hq1.le⟩
      (show (1/4:ℝ) ∈ Set.Icc 0 (1/4) from ⟨by norm_num,le_rfl⟩) hq1
    simpa only [catalanBranch_quarter] using h

theorem logConjugate_minus_id_strictMono :
    StrictMonoOn (fun x => logConjugate x-x) (Set.Icc 0 (Real.log (5/4))) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (logConjugate_continuousOn.sub continuousOn_id)
  rw [interior_Icc]
  intro x hx
  have hd := (hasDerivAt_logConjugate hx.1.le hx.2).sub (hasDerivAt_id x)
  rw [hd.deriv]
  rw [← (hasDerivAt_logConjugate hx.1.le hx.2).deriv,deriv_logConjugate hx.1.le hx.2]
  have hu := conjugate_branch_interior hx.1 hx.2
  exact sub_pos.mpr (conjugateSlope_gt_one hu.1 hu.2)

theorem logConjugate_expansive {x y : ℝ} (hx : x ∈ Set.Icc 0 (Real.log (5/4)))
    (hy : y ∈ Set.Icc 0 (Real.log (5/4))) (hxy : x < y) :
    y-x < logConjugate y-logConjugate x := by
  have h := logConjugate_minus_id_strictMono hx hy hxy
  linarith

#print axioms logConjugate_expansive
end LiteralDL
```
<!-- END SOURCE -->

### ThresholdIdentity

<!-- SOURCE {"module": "ThresholdIdentity", "bytes": 1933, "sha256": "d8ca6bb8d48881e89fb7f06f1661d72e0317c2c33b64468884790688e377e9bc"} -->
```lean
import GeometricBridge
namespace LiteralDL

theorem growth_mul_rho_le (s : Species) : growth s * rho s ≤ 1 := by
  have hp : ∀ n : Nat, Real.log (rho s) ≤ negativeLogCount s n / n := by
    intro n
    by_cases hn : n = 0
    · simp only [hn, Nat.cast_zero, div_zero]
      exact Real.log_nonpos (rho_pos s).le (by have := (actualThreshold s).quarter; change rho s ≤ 1/4 at this; linarith)
    have hc := count_cast_pos (s := s) hn
    have hr := rho_pos s
    have hb : (count s n : ℝ) * rho s ^ n ≤ 1 := le_trans (count_exponential_bound s n) (by norm_num)
    have hl := Real.log_le_log (mul_pos hc (pow_pos hr n)) hb
    rw [Real.log_mul hc.ne' (pow_pos hr n).ne', Real.log_pow, Real.log_one] at hl
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    simp only [negativeLogCount, ite_eq_right hn]
    apply (le_div_iff₀ hn0).mpr
    nlinarith
  have hL := ge_of_tendsto' (negativeLogCount_tendsto s) hp
  have he := Real.exp_le_exp.mpr (show -(negativeLogCount_subadditive s).lim + Real.log (rho s) ≤ 0 by linarith)
  rw [Real.exp_add, Real.exp_log (rho_pos s), Real.exp_zero] at he
  exact he

theorem growth_mul_rho_ge (s : Species) : 1 ≤ growth s * rho s := by
  by_contra h
  have hlt : growth s * rho s < 1 := lt_of_not_ge h
  have hg := growth_pos s
  let z := (rho s + 1 / growth s) / 2
  have hi : growth s * (1 / growth s) = 1 := by field_simp
  have hz : rho s < z := by dsimp [z]; nlinarith
  have hz0 : 0 ≤ z := le_trans (rho_pos s).le hz.le
  have hzg : growth s * z < 1 := by dsimp [z]; nlinarith
  have hf := (historySum_finite_iff s hz0).mp (finite_below_growth s hz0 hzg)
  exact (not_le_of_gt hz) hf

theorem growth_eq_inv_rho (s : Species) : growth s = (rho s)⁻¹ := by
  have he := le_antisymm (growth_mul_rho_le s) (growth_mul_rho_ge s)
  rw [← one_div]
  apply (eq_div_iff (rho_pos s).ne').mpr
  simpa using he

#print axioms growth_eq_inv_rho
end LiteralDL
```
<!-- END SOURCE -->

### SpeciesShapes

<!-- SOURCE {"module": "SpeciesShapes", "bytes": 1482, "sha256": "5fc19e0d5318e6e3c7aac98c60c45002847b0d4400e9537b6adeb909fa761a28"} -->
```lean
import ThresholdIdentity
namespace LiteralDL

def leaves : Species → Nat
  | .leaf => 1
  | .node a b => leaves a + leaves b

theorem leaves_pos (s : Species) : 0 < leaves s := by
  induction s <;> simp_all [leaves]

def caterpillar : Nat → Species
  | 0 => .leaf
  | 1 => .leaf
  | n+2 => .node (caterpillar (n+1)) .leaf

def balanced : Nat → Species
  | 0 => .leaf
  | 1 => .leaf
  | n+2 => .node (balanced ((n+2)/2)) (balanced ((n+3)/2))
termination_by n => n
 decreasing_by all_goals omega

theorem leaves_caterpillar {k : Nat} (hk : 0 < k) : leaves (caterpillar k) = k := by
  induction k with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero => simp [caterpillar, leaves]
    | succ j => simp only [caterpillar, leaves]; rw [ih (by omega)]

theorem leaves_balanced {k : Nat} (hk : 0 < k) : leaves (balanced k) = k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => omega
    | succ k =>
      cases k with
      | zero => simp [balanced, leaves]
      | succ j =>
        rw [balanced, leaves, ih _ (by omega) (by omega), ih _ (by omega) (by omega)]
        omega

inductive ShapeIso : Species → Species → Prop where
  | leaf : ShapeIso .leaf .leaf
  | node {a b c d} : ShapeIso a c → ShapeIso b d → ShapeIso (.node a b) (.node c d)
  | swap {a b c d} : ShapeIso a d → ShapeIso b c → ShapeIso (.node a b) (.node c d)

#print axioms leaves_caterpillar
#print axioms leaves_balanced
end LiteralDL
```
<!-- END SOURCE -->

### FiniteShapes

<!-- SOURCE {"module": "FiniteShapes", "bytes": 1177, "sha256": "311e58b8603450f8347e21c68d935f8c30fb7f2c333dfc12c56b2349eaa4b16c"} -->
```lean
import SpeciesShapes
namespace LiteralDL

def speciesPool : Nat → List Species
  | 0 => []
  | d+1 => .leaf :: ((speciesPool d).product (speciesPool d)).map (fun p => .node p.1 p.2)

theorem mem_speciesPool (s : Species) (d : Nat) (hd : leaves s ≤ d) : s ∈ speciesPool d := by
  induction d generalizing s with
  | zero => have := leaves_pos s; omega
  | succ d ih =>
    cases s with
    | leaf => simp [speciesPool]
    | node a b =>
      have ha := leaves_pos a
      have hb := leaves_pos b
      have h1 : leaves a ≤ d := by simp only [leaves] at hd; omega
      have h2 : leaves b ≤ d := by simp only [leaves] at hd; omega
      have hma := ih a h1
      have hmb := ih b h2
      simp only [speciesPool, List.mem_cons, List.mem_map]
      right
      exact ⟨(a,b), List.mem_product.mpr ⟨hma,hmb⟩,rfl⟩

instance fixedLeavesFintype (k : Nat) : Fintype {s : Species // leaves s = k} :=
  Fintype.ofFinset ((speciesPool k).toFinset.filter (fun s => leaves s = k))
    (by intro s; simp only [Finset.mem_filter, List.mem_toFinset]
        exact ⟨fun h => h.2, fun h => ⟨mem_speciesPool s k h.le,h⟩⟩)

#print axioms fixedLeavesFintype
end LiteralDL
```
<!-- END SOURCE -->

### StrictChildThreshold

<!-- SOURCE {"module": "StrictChildThreshold", "bytes": 1798, "sha256": "928790d737670955732c6f55f34256e0565c0a85f3e291774aae21110829f451"} -->
```lean
import FiniteShapes
open scoped ENNReal
namespace LiteralDL

theorem historySum_node_quadratic (a b : Species) (z : ℝ≥0∞) :
    historySum (.node a b) z = historySum a z + historySum b z + historySum a z * historySum b z +
      historySum (.node a b) z * historySum (.node a b) z := by
  have h := total_quadratic (fun q : Atom (.node a b) => z ^ size (atomHist q))
  rw [atomMass_node, ← historySum_skeleton] at h
  exact h

theorem rho_node_lt_left (a b : Species) : rho (.node a b) < rho a := by
  by_contra hn
  have hr : rho a ≤ rho (.node a b) := le_of_not_gt hn
  let z := ENNReal.ofReal (rho a)
  let H := historySum (.node a b) z
  have ha : historySum a z = ENNReal.ofReal (1/2) := historySum_at_rho a
  have hH : H ≤ ENNReal.ofReal (1/2) := by
    change historySum (.node a b) (ENNReal.ofReal (rho a)) ≤ _
    rw [(actualThreshold (.node a b)).representation (rho a) ⟨(rho_pos a).le,hr⟩]
    exact ENNReal.ofReal_le_ofReal ((actualThreshold (.node a b)).bounds (rho a) ⟨(rho_pos a).le,hr⟩).2
  have hl : ENNReal.ofReal (1/2) ≤ H := by rw [← ha]; exact historySum_node_ge_left a b z
  have hq : historySum a z + H*H ≤ H := by
    calc
      _ ≤ (historySum a z + historySum b z + historySum a z * historySum b z) + H*H := by gcongr; exact le_trans le_self_add le_self_add
      _ = H := (historySum_node_quadratic a b z).symm
  have hh : ENNReal.ofReal (1/2) + ENNReal.ofReal (1/2) * ENNReal.ofReal (1/2) ≤ ENNReal.ofReal (1/2) :=
    (add_le_add ha.ge (mul_le_mul' hl hl)).trans (hq.trans hH)
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top), ENNReal.toReal_mul] at ht
  norm_num at ht

#print axioms rho_node_lt_left
end LiteralDL
```
<!-- END SOURCE -->

### ThresholdUniqueness

<!-- SOURCE {"module": "ThresholdUniqueness", "bytes": 896, "sha256": "4bcceca20683bd6db0a2c65aeb3eee64d4f3512c4cf184c55088c70ca36f09fe"} -->
```lean
import StrictChildThreshold
open scoped ENNReal
namespace LiteralDL

theorem rho_eq_of_historySum_eq (a b : Species)
    (h : ∀ z : ℝ≥0∞, historySum a z = historySum b z) : rho a = rho b := by
  apply le_antisymm
  · apply (historySum_finite_iff b (rho_pos a).le).mp
    rw [← h]
    exact (historySum_finite_iff a (rho_pos a).le).mpr le_rfl
  · apply (historySum_finite_iff a (rho_pos b).le).mp
    rw [h]
    exact (historySum_finite_iff b (rho_pos b).le).mpr le_rfl

theorem rho_swap (a b : Species) : rho (.node a b) = rho (.node b a) := by
  apply rho_eq_of_historySum_eq
  intro z
  rw [historySum_coeff, historySum_coeff]
  simp_rw [count_swap a b]

theorem rho_node_lt_right (a b : Species) : rho (.node a b) < rho b := by
  rw [rho_swap]
  exact rho_node_lt_left b a

#print axioms rho_eq_of_historySum_eq
#print axioms rho_swap
#print axioms rho_node_lt_right
end LiteralDL
```
<!-- END SOURCE -->

### ClosureAudit

<!-- SOURCE {"module": "ClosureAudit", "bytes": 5315, "sha256": "630ce8302045fafd7c9bc55eda311822fb6f71cf610b0cdde60dbf9529644c07"} -->
```lean
import ThresholdUniqueness
#print axioms LiteralDL.Species
#print axioms LiteralDL.weight
#print axioms LiteralDL.weight_pos
#print axioms LiteralDL.Hist
#print axioms LiteralDL.size
#print axioms LiteralDL.size_pos
#print axioms LiteralDL.depth
#print axioms LiteralDL.depth_bound
#print axioms LiteralDL.pool
#print axioms LiteralDL.mem_pool
#print axioms LiteralDL.fiberFintype
#print axioms LiteralDL.count
#print axioms LiteralDL.duplicate
#print axioms LiteralDL.duplicate_injective
#print axioms LiteralDL.supermultiplicative
#print axioms LiteralDL.fiber_zero_empty
#print axioms LiteralDL.one
#print axioms LiteralDL.positiveFiber
#print axioms LiteralDL.count_pos
#print axioms LiteralDL.Event
#print axioms LiteralDL.EventTree
#print axioms LiteralDL.encode
#print axioms LiteralDL.Valid
#print axioms LiteralDL.encode_valid
#print axioms LiteralDL.valid_has_history
#print axioms LiteralDL.encode_ne_loss
#print axioms LiteralDL.encode_injective
#print axioms LiteralDL.sourceEquiv
#print axioms LiteralDL.splitEquiv
#print axioms LiteralDL.pairFintype
#print axioms LiteralDL.pairCount
#print axioms LiteralDL.nodeJoin
#print axioms LiteralDL.nodeCut
#print axioms LiteralDL.nodeEquiv
#print axioms LiteralDL.count_node
#print axioms LiteralDL.pairCount_eq
#print axioms LiteralDL.leafJoin
#print axioms LiteralDL.leafCut
#print axioms LiteralDL.leafEquiv
#print axioms LiteralDL.count_leaf
#print axioms LiteralDL.count_node_convolution
#print axioms LiteralDL.extantCount
#print axioms LiteralDL.encode_size
#print axioms LiteralDL.sourceFiberEquiv
#print axioms LiteralDL.swapRoot
#print axioms LiteralDL.swapRoot_size
#print axioms LiteralDL.swapRoot_twice
#print axioms LiteralDL.swapFiber
#print axioms LiteralDL.count_swap
#print axioms LiteralDL.count_zero
#print axioms LiteralDL.Skeleton
#print axioms LiteralDL.Atom
#print axioms LiteralDL.atomHist
#print axioms LiteralDL.assemble
#print axioms LiteralDL.cutSkeleton
#print axioms LiteralDL.assemble_cut
#print axioms LiteralDL.cut_assemble
#print axioms LiteralDL.skeletonEquiv
#print axioms LiteralDL.skeletonSize
#print axioms LiteralDL.assemble_size
#print axioms LiteralDL.rootEquiv
#print axioms LiteralDL.skWeight
#print axioms LiteralDL.total
#print axioms LiteralDL.total_quadratic
#print axioms LiteralDL.historySum
#print axioms LiteralDL.skWeight_pow
#print axioms LiteralDL.historySum_skeleton
#print axioms LiteralDL.skHeight
#print axioms LiteralDL.cutWeight
#print axioms LiteralDL.cutTotal
#print axioms LiteralDL.cutWeight_fork
#print axioms LiteralDL.cutTotal_succ
#print axioms LiteralDL.cutTotal_zero
#print axioms LiteralDL.cutTotal_bound
#print axioms LiteralDL.total_le_of_prefixed
#print axioms LiteralDL.sizeEquiv
#print axioms LiteralDL.historySum_coeff
#print axioms LiteralDL.historySum_le_of_atom_prefixed
#print axioms LiteralDL.atomNodeEquiv
#print axioms LiteralDL.atomMass_node
#print axioms LiteralDL.total_eq_of_mass_eq
#print axioms LiteralDL.catalanBranch
#print axioms LiteralDL.catalanBranch_properties
#print axioms LiteralDL.total_principal
#print axioms LiteralDL.total_infinite_above
#print axioms LiteralDL.atomMass_leaf
#print axioms LiteralDL.historySum_leaf_principal
#print axioms LiteralDL.historySum_leaf_infinite
#print axioms LiteralDL.historySum_node_principal
#print axioms LiteralDL.branchValue
#print axioms LiteralDL.continuous_catalanBranch
#print axioms LiteralDL.branchValue_continuous
#print axioms LiteralDL.catalanBranch_zero
#print axioms LiteralDL.catalanBranch_quarter
#print axioms LiteralDL.branchValue_zero
#print axioms LiteralDL.catalanBranch_strictMono
#print axioms LiteralDL.mass_le_total
#print axioms LiteralDL.historySum_node_ge_left
#print axioms LiteralDL.historySum_node_ge_right
#print axioms LiteralDL.historySum_mono
#print axioms LiteralDL.historySum_node_infinite
#print axioms LiteralDL.ActualThreshold
#print axioms LiteralDL.leafThreshold
#print axioms LiteralDL.nodeThreshold
#print axioms LiteralDL.actualThreshold
#print axioms LiteralDL.rho
#print axioms LiteralDL.rho_pos
#print axioms LiteralDL.historySum_at_rho
#print axioms LiteralDL.historySum_finite_iff
#print axioms LiteralDL.count_exponential_bound
#print axioms LiteralDL.negativeLogCount
#print axioms LiteralDL.count_cast_pos
#print axioms LiteralDL.negativeLogCount_subadditive
#print axioms LiteralDL.negativeLogCount_bddBelow
#print axioms LiteralDL.negativeLogCount_tendsto
#print axioms LiteralDL.growth
#print axioms LiteralDL.growth_pos
#print axioms LiteralDL.actual_root_limit
#print axioms LiteralDL.count_le_growth_pow
#print axioms LiteralDL.finite_below_growth
#print axioms LiteralDL.growth_mul_rho_le
#print axioms LiteralDL.growth_mul_rho_ge
#print axioms LiteralDL.growth_eq_inv_rho
#print axioms LiteralDL.leaves
#print axioms LiteralDL.leaves_pos
#print axioms LiteralDL.caterpillar
#print axioms LiteralDL.balanced
#print axioms LiteralDL.leaves_caterpillar
#print axioms LiteralDL.leaves_balanced
#print axioms LiteralDL.ShapeIso
#print axioms LiteralDL.speciesPool
#print axioms LiteralDL.mem_speciesPool
#print axioms LiteralDL.fixedLeavesFintype
#print axioms LiteralDL.historySum_node_quadratic
#print axioms LiteralDL.rho_node_lt_left
#print axioms LiteralDL.rho_eq_of_historySum_eq
#print axioms LiteralDL.rho_swap
#print axioms LiteralDL.rho_node_lt_right
```
<!-- END SOURCE -->

### ShapeTransport

<!-- SOURCE {"module": "ShapeTransport", "bytes": 2326, "sha256": "b7ab47e12db46b1b9cbdeb67696e1a4d94c957509326a121b10bb44192b0b218"} -->
```lean
import FiniteShapes
import ThresholdUniqueness
namespace LiteralDL

theorem ShapeIso.refl (s : Species) : ShapeIso s s := by
  induction s with
  | leaf => exact .leaf
  | node a b ha hb => exact .node ha hb

theorem ShapeIso.symm {s t : Species} (h : ShapeIso s t) : ShapeIso t s := by
  induction h with
  | leaf => exact .leaf
  | node _ _ ha hb => exact .node ha hb
  | swap _ _ ha hb => exact .swap hb ha

theorem ShapeIso.trans {s t u : Species} (h : ShapeIso s t) (g : ShapeIso t u) :
    ShapeIso s u := by
  induction h generalizing u with
  | leaf => cases g; exact .leaf
  | node ha hb ia ib =>
    cases g with
    | node ga gb => exact .node (ia ga) (ib gb)
    | swap ga gb => exact .swap (ia ga) (ib gb)
  | swap ha hb ia ib =>
    cases g with
    | node ga gb => exact .swap (ia gb) (ib ga)
    | swap ga gb => exact .node (ia gb) (ib ga)

theorem count_node_congr {a b c d : Species}
    (ha : ∀ n, count a n = count c n) (hb : ∀ n, count b n = count d n) :
    ∀ n, count (.node a b) n = count (.node c d) n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [count_node_convolution, count_node_convolution]
    have hs : (∑ i : Fin (n+1), count (.node a b) i * count (.node a b) (n-i)) =
        ∑ i : Fin (n+1), count (.node c d) i * count (.node c d) (n-i) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases h0 : i.val = 0
      · simp [h0, count_zero]
      by_cases hn : i.val = n
      · simp [hn, count_zero]
      have hi : i.val < n := by have := i.isLt; omega
      have hj : n-i.val < n := by omega
      rw [ih _ hi, ih _ hj]
    rw [hs]
    simp_rw [ha, hb]

theorem ShapeIso.count_eq {s t} (h : ShapeIso s t) (n : Nat) : count s n = count t n := by
  induction h generalizing n with
  | leaf => rfl
  | node ha hb ia ib => exact count_node_congr ia ib n
  | swap ha hb ia ib =>
    exact (count_node_congr ia ib n).trans (count_swap _ _ n)

theorem ShapeIso.leaves_eq {s t} (h : ShapeIso s t) : leaves s = leaves t := by
  induction h <;> simp_all [leaves, Nat.add_comm]

theorem ShapeIso.rho_eq {s t} (h : ShapeIso s t) : rho s = rho t := by
  apply rho_eq_of_historySum_eq
  intro z
  rw [historySum_coeff, historySum_coeff]
  simp_rw [h.count_eq]

#print axioms ShapeIso.count_eq
#print axioms ShapeIso.rho_eq
end LiteralDL
```
<!-- END SOURCE -->

### BranchDomain

<!-- SOURCE {"module": "BranchDomain", "bytes": 2060, "sha256": "e18b14b5411d660e2462491a406e3f457560f93ba95ba1caf965f8b8fd5e1ad7"} -->
```lean
import ShapeTransport
namespace LiteralDL
open scoped ENNReal

theorem branchValue_nonneg {s z} (hz : 0 ≤ z) (hr : z ≤ rho s) :
    0 ≤ branchValue s z := ((actualThreshold s).bounds z ⟨hz,hr⟩).1

theorem branchValue_pos {s z} (hz : 0 < z) (hr : z ≤ rho s) :
    0 < branchValue s z := by
  have h := (actualThreshold s).increasing
    (show 0 ∈ Set.Icc 0 (rho s) from ⟨le_rfl,(rho_pos s).le⟩) ⟨hz.le,hr⟩ hz
  simpa only [branchValue_zero] using h

theorem branchValue_lt_half {s z} (hz : 0 ≤ z) (hr : z < rho s) :
    branchValue s z < 1/2 := by
  have h := (actualThreshold s).increasing ⟨hz,hr.le⟩
    (show rho s ∈ Set.Icc 0 (rho s) from ⟨(rho_pos s).le,le_rfl⟩) hr
  have he : branchValue s (rho s) = 1/2 := (actualThreshold s).endpoint
  exact he ▸ h

theorem branch_node_quadratic (a b : Species) {z : ℝ} (hz : 0 ≤ z)
    (hr : z ≤ rho (.node a b)) :
    branchValue a z + branchValue b z + branchValue a z * branchValue b z +
      branchValue (.node a b) z * branchValue (.node a b) z = branchValue (.node a b) z := by
  have hra := hr.trans (rho_node_lt_left a b).le
  have hrb := hr.trans (rho_node_lt_right a b).le
  have ha := branchValue_nonneg hz hra
  have hb := branchValue_nonneg hz hrb
  have hn := branchValue_nonneg hz hr
  have he := historySum_node_quadratic a b (ENNReal.ofReal z)
  rw [(actualThreshold (.node a b)).representation z ⟨hz,hr⟩,
    (actualThreshold a).representation z ⟨hz,hra⟩,
    (actualThreshold b).representation z ⟨hz,hrb⟩] at he
  rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul hn,
    ← ENNReal.ofReal_add ha hb,
    ← ENNReal.ofReal_add (add_nonneg ha hb) (mul_nonneg ha hb),
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg ha hb) (mul_nonneg ha hb))
      (mul_nonneg hn hn)] at he
  have ht := congrArg ENNReal.toReal he
  simpa only [ENNReal.toReal_ofReal hn,
    ENNReal.toReal_ofReal (add_nonneg (add_nonneg (add_nonneg ha hb)
      (mul_nonneg ha hb)) (mul_nonneg hn hn))] using ht.symm

#print axioms branch_node_quadratic
end LiteralDL
```
<!-- END SOURCE -->

### BranchGlobal

<!-- SOURCE {"module": "BranchGlobal", "bytes": 1163, "sha256": "fad4cb732022a2cac389675409bdc280e9febe4b87b223e0d80b9eef48d65ac1"} -->
```lean
import BranchDomain
import RealAssociator
namespace LiteralDL

theorem branchValue_global_bounds (s : Species) {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ branchValue s z ∧ branchValue s z ≤ 1/2 := by
  induction s with
  | leaf => exact catalanBranch_global_bounds hz
  | node a b ia ib =>
    exact catalanBranch_global_bounds (by
      exact add_nonneg (add_nonneg ia.1 ib.1) (mul_nonneg ia.1 ib.1))

theorem branchValue_ge_leaf (s : Species) {z : ℝ} (hz : 0 ≤ z) :
    branchValue .leaf z ≤ branchValue s z := by
  induction s with
  | leaf => rfl
  | node a b ia ib =>
    exact ia.trans (mergeValue_ge_left (branchValue_global_bounds a hz).1
      (branchValue_global_bounds a hz).2 (branchValue_global_bounds b hz).1)

theorem rho_le_of_global_branch_le (s t : Species)
    (h : ∀ z : ℝ, 0 ≤ z → branchValue s z ≤ branchValue t z) : rho t ≤ rho s := by
  by_contra hn
  have hr : rho s < rho t := lt_of_not_ge hn
  have hc := branchValue_lt_half (rho_pos s).le hr
  have he : branchValue s (rho s) = 1/2 := (actualThreshold s).endpoint
  have hh := h (rho s) (rho_pos s).le
  linarith

#print axioms rho_le_of_global_branch_le
end LiteralDL
```
<!-- END SOURCE -->

### CaterpillarOrder

<!-- SOURCE {"module": "CaterpillarOrder", "bytes": 1961, "sha256": "88ec591cc6516889d9bd570a95b958ea90a7dc95d73f33c1a47a95f37cb1b715"} -->
```lean
import BranchGlobal
namespace LiteralDL

theorem caterpillar_succ {k : Nat} (hk : 0 < k) :
    caterpillar (k+1) = .node (caterpillar k) .leaf := by
  cases k with
  | zero => omega
  | succ k => rfl

theorem caterpillar_merge_le {a b : Nat} (ha : 0 < a) (hb : 0 < b)
    {z : ℝ} (hz : 0 ≤ z) :
    mergeValue (branchValue (caterpillar a) z) (branchValue (caterpillar b) z) ≤
      branchValue (caterpillar (a+b)) z := by
  induction b with
  | zero => omega
  | succ b ih =>
    cases b with
    | zero =>
      rw [caterpillar_succ ha]
      rfl
    | succ b =>
      have hbp : 0 < b+1 := by omega
      rw [caterpillar_succ hbp, show a+(b+1+1) = (a+(b+1))+1 by omega,
        caterpillar_succ (by omega : 0 < a+(b+1))]
      change mergeValue (branchValue (caterpillar a) z)
        (mergeValue (branchValue (caterpillar (b+1)) z) (branchValue .leaf z)) ≤
        mergeValue (branchValue (caterpillar (a+(b+1))) z) (branchValue .leaf z)
      exact (mergeValue_associator (branchValue_global_bounds _ hz).1
        (branchValue_global_bounds _ hz).1 (branchValue_global_bounds _ hz).1
        (branchValue_ge_leaf _ hz)).trans
        (mergeValue_mono (mergeValue_nonneg (branchValue_global_bounds _ hz).1
          (branchValue_global_bounds _ hz).1) (branchValue_global_bounds _ hz).1
          (ih hbp) le_rfl)

theorem branchValue_le_caterpillar (s : Species) {z : ℝ} (hz : 0 ≤ z) :
    branchValue s z ≤ branchValue (caterpillar (leaves s)) z := by
  induction s with
  | leaf => rfl
  | node a b ia ib =>
    exact (mergeValue_mono (branchValue_global_bounds _ hz).1
      (branchValue_global_bounds _ hz).1 ia ib).trans
      (caterpillar_merge_le (leaves_pos a) (leaves_pos b) hz)

theorem rho_caterpillar_le (s : Species) : rho (caterpillar (leaves s)) ≤ rho s :=
  rho_le_of_global_branch_le s _ (fun _ hz => branchValue_le_caterpillar s hz)

#print axioms branchValue_le_caterpillar
#print axioms rho_caterpillar_le
end LiteralDL
```
<!-- END SOURCE -->

### GrowthFinalBounds

<!-- SOURCE {"module": "GrowthFinalBounds", "bytes": 1348, "sha256": "12bfccfaa2c9422929e4744a958bac1ea838a5002ffc212dea7d9199fa42fbe0"} -->
```lean
import BranchGlobal
import SpeciesShapes
namespace LiteralDL.GrowthStage
open LiteralDL

theorem leaf_quadratic {z : ℝ} (hz : 0 ≤ z) (hr : z ≤ rho .leaf) :
    z + branchValue .leaf z * branchValue .leaf z = branchValue .leaf z := by
  have hq : rho .leaf ≤ 1/4 := (actualThreshold .leaf).quarter
  exact (catalanBranch_properties hz (hr.trans hq)).2.2

theorem leaf_mass (s : Species) {z : ℝ} (hz : 0 ≤ z) (hr : z ≤ rho s) :
    (leaves s : ℝ) * z ≤ branchValue s z := by
  induction s with
  | leaf =>
    have h := leaf_quadratic hz hr
    simp only [leaves, Nat.cast_one, one_mul]
    nlinarith [sq_nonneg (branchValue .leaf z)]
  | node a b ia ib =>
    have ha := hr.trans (rho_node_lt_left a b).le
    have hb := hr.trans (rho_node_lt_right a b).le
    have h := branch_node_quadratic a b hz hr
    have hn := mul_nonneg (branchValue_nonneg hz ha) (branchValue_nonneg hz hb)
    have ia' := ia ha
    have ib' := ib hb
    simp only [leaves, Nat.cast_add]
    nlinarith [sq_nonneg (branchValue (.node a b) z)]

theorem growth_lower (s : Species) : 2 * (leaves s : ℝ) ≤ growth s := by
  have h := leaf_mass s (rho_pos s).le le_rfl
  have he : branchValue s (rho s) = 1/2 := (actualThreshold s).endpoint
  have hg := growth_mul_rho_ge s
  have heq := growth_mul_rho_le s
  nlinarith [rho_pos s]
end LiteralDL.GrowthStage
```
<!-- END SOURCE -->

### GrowthFinalCaterpillar

<!-- SOURCE {"module": "GrowthFinalCaterpillar", "bytes": 1600, "sha256": "ea139539772fa7bec96112db8e341dcbe6f51541d6f2aaa8cc9a94c15df6d4c9"} -->
```lean
import GrowthFinalBounds
namespace LiteralDL.GrowthStage
open LiteralDL
set_option maxHeartbeats 1000000

theorem caterpillar_cubic (k : Nat) (hk : 0 < k) {z : ℝ}
    (hz : 0 ≤ z) (hr : z ≤ rho (caterpillar k)) :
    (((k:ℝ)^3-(k:ℝ))/3)*z^2 ≤ branchValue (caterpillar k) z := by
  induction k with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero =>
      norm_num [caterpillar]
      exact (branchValue_global_bounds .leaf hz).1
    | succ j =>
      have hr' : z ≤ rho (caterpillar (j+1)) :=
        hr.trans (rho_node_lt_left (caterpillar (j+1)) .leaf).le
      have hi := ih (by omega) hr'
      have he := branch_node_quadratic (caterpillar (j+1)) .leaf hz hr
      have hn := (branchValue_global_bounds .leaf hz).1
      have hn' := (branchValue_global_bounds (caterpillar (j+1)) hz).1
      have hp := mul_nonneg hn' hn
      have hm := leaf_mass (caterpillar (j+2)) hz hr
      rw [leaves_caterpillar (by omega)] at hm
      have hc : (0:ℝ) ≤ (j+2:Nat)*z := by positivity
      have hsq : ((j+2:Nat):ℝ)^2*z^2 ≤ branchValue (caterpillar (j+2)) z ^ 2 := by
        nlinarith only [hm, hc]
      change branchValue (caterpillar (j+1)) z + branchValue .leaf z +
        branchValue (caterpillar (j+1)) z * branchValue .leaf z +
        branchValue (caterpillar (j+2)) z * branchValue (caterpillar (j+2)) z = branchValue (caterpillar (j+2)) z at he
      simp only [show j+1+1=j+2 by omega] at *
      push_cast at *
      nlinarith only [hi, he, hn, hp, hsq, sq_nonneg z, mul_nonneg (Nat.cast_nonneg j : (0:ℝ) ≤ j) (sq_nonneg z)]
end LiteralDL.GrowthStage
```
<!-- END SOURCE -->

### GrowthFinalScalar

<!-- SOURCE {"module": "GrowthFinalScalar", "bytes": 1511, "sha256": "d0416897223297362d45b9e324a630672ef6b0a2bd14b44d97ea6f07d7597564"} -->
```lean
import GrowthFinalBounds
set_option maxHeartbeats 1000000
namespace LiteralDL.GrowthStage

theorem merge_bound {a b z x y w : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hz : 0 ≤ z)
    (hab : (a+b)^2 ≤ 5*a*b) (hs : (a+b)*z ≤ 1/1000)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hw : 0 ≤ w) (hh : w ≤ 1/2)
    (hxb : x ≤ a*z+20*(a*z)^2) (hyb : y ≤ b*z+20*(b*z)^2)
    (he : x+y+x*y+w*w=w) : w ≤ (a+b)*z+20*((a+b)*z)^2 := by
  have haz : 0 ≤ a*z := mul_nonneg ha hz
  have hbz : 0 ≤ b*z := mul_nonneg hb hz
  have hau : a*z ≤ 1/1000 := by nlinarith
  have hbu : b*z ≤ 1/1000 := by nlinarith
  have hxx : x ≤ 51/50*(a*z) := by nlinarith
  have hyy : y ≤ 51/50*(b*z) := by nlinarith
  have hp : x*y ≤ 2*(a*z)*(b*z) := by
    have h := mul_le_mul hxx hyy hy (by positivity : 0 ≤ 51/50*(a*z))
    nlinarith [mul_nonneg haz hbz]
  let q := x+y+x*y
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hc : (a*z)*(b*z) ≤ (a*z+b*z)/1000 := by
    have h := mul_le_mul_of_nonneg_right hau hbz
    nlinarith only [h, haz]
  have hq : q ≤ 11/10*((a+b)*z) := by
    dsimp [q]
    nlinarith only [hxx, hyy, hp, hc, haz, hbz]
  have hwq : w ≤ 2*q := by dsimp [q] at *; nlinarith only [he, hh, hw]
  have hwq2 : w*w ≤ 4*q^2 := by nlinarith only [hwq, hw, hq0]
  have hq2 : 4*q^2 ≤ 5*((a+b)*z)^2 := by nlinarith only [hq, hq0]
  have hsquare := mul_le_mul_of_nonneg_right hab (sq_nonneg z)
  dsimp [q] at hwq2 hq2
  nlinarith only [he, hp, hxb, hyb, hwq2, hq2, hsquare]
end LiteralDL.GrowthStage
```
<!-- END SOURCE -->

### StrictRotation

<!-- SOURCE {"module": "StrictRotation", "bytes": 2714, "sha256": "d116011ba13cd251dca5e1dd50f8c93bac4979eb7253928ffd05e347b47431bd"} -->
```lean
import CaterpillarOrder
namespace LiteralDL

theorem branch_node_gt_left (a b : Species) {z : ℝ} (hz : 0 < z)
    (hr : z ≤ rho (.node a b)) : branchValue a z < branchValue (.node a b) z := by
  have he := branch_node_quadratic a b hz.le hr
  have hb := branchValue_pos hz (hr.trans (rho_node_lt_right a b).le)
  have ha := branchValue_nonneg hz.le (hr.trans (rho_node_lt_left a b).le)
  nlinarith [mul_nonneg ha hb.le, sq_nonneg (branchValue (.node a b) z)]

theorem branch_nonleaf_gt_leaf {s : Species} (hs : s ≠ .leaf) {z : ℝ}
    (hz : 0 < z) (hr : z ≤ rho s) : branchValue .leaf z < branchValue s z := by
  cases s with
  | leaf => exact (hs rfl).elim
  | node a b => exact (branchValue_ge_leaf a hz.le).trans_lt (branch_node_gt_left a b hz hr)

theorem rho_rotation_le (a b : Species) :
    rho (.node (.node a b) .leaf) ≤ rho (.node a (.node b .leaf)) := by
  apply rho_le_of_global_branch_le
  intro z hz
  exact mergeValue_associator (branchValue_global_bounds a hz).1
    (branchValue_global_bounds b hz).1 (branchValue_global_bounds .leaf hz).1
    (branchValue_ge_leaf a hz)

theorem rho_rotation_lt (a b : Species) (ha : a ≠ .leaf) :
    rho (.node (.node a b) .leaf) < rho (.node a (.node b .leaf)) := by
  have hle := rho_rotation_le a b
  apply lt_of_le_of_ne hle
  intro heq
  let r := rho (.node a (.node b .leaf))
  have hr : 0 < r := rho_pos _
  have hrL : r = rho (.node (.node a b) .leaf) := heq.symm
  have hleft : r < rho (.node a b) := hrL ▸ rho_node_lt_left (.node a b) .leaf
  have hright : r < rho (.node b .leaf) := rho_node_lt_right a (.node b .leaf)
  have hA : r ≤ rho a := (rho_node_lt_left a (.node b .leaf)).le
  have hx := branch_node_quadratic a b hr.le hleft.le
  have hy := branch_node_quadratic b .leaf hr.le hright.le
  have hac := branch_nonleaf_gt_leaf ha hr hA
  have hx0 := branchValue_pos hr hleft.le
  have hy0 := branchValue_nonneg hr.le hright.le
  have hxh := branchValue_lt_half hr.le hleft
  have hyh := branchValue_lt_half hr.le hright
  have hys : branchValue .leaf r + branchValue b r + branchValue .leaf r * branchValue b r +
      branchValue (.node b .leaf) r * branchValue (.node b .leaf) r = branchValue (.node b .leaf) r := by
    nlinarith [hy]
  have hc := catalan_associator_strict hx hys hac hx0 hy0 (by linarith)
  have heL := branch_node_quadratic (.node a b) .leaf hr.le hrL.le
  have heR := branch_node_quadratic a (.node b .leaf) hr.le le_rfl
  have hvL : branchValue (.node (.node a b) .leaf) r = 1/2 := hrL ▸ (actualThreshold _).endpoint
  have hvR : branchValue (.node a (.node b .leaf)) r = 1/2 := (actualThreshold _).endpoint
  rw [hvL] at heL
  rw [hvR] at heR
  nlinarith

#print axioms rho_rotation_lt
end LiteralDL
```
<!-- END SOURCE -->

### GrowthFinalBalanced

<!-- SOURCE {"module": "GrowthFinalBalanced", "bytes": 2577, "sha256": "3d5cf75a33baebcb3918712fed0cbe9a973a9b1464f4a30cfbb29a7f41c47dad"} -->
```lean
import GrowthFinalScalar
namespace LiteralDL.GrowthStage
open LiteralDL
set_option maxHeartbeats 1000000

theorem balanced_value_bound (k : Nat) (hk : 0 < k) {z : ℝ}
    (hz : 0 ≤ z) (hr : z ≤ rho (balanced k)) (hs : (k:ℝ)*z ≤ 1/1000) :
    branchValue (balanced k) z ≤ (k:ℝ)*z+20*((k:ℝ)*z)^2 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => omega
    | succ n =>
      cases n with
      | zero =>
        norm_num only [Nat.zero_add, balanced, Nat.cast_one, one_mul] at hr ⊢
        have he := leaf_quadratic hz hr
        have hb := (branchValue_global_bounds .leaf hz).2
        have hn := (branchValue_global_bounds .leaf hz).1
        have hx : branchValue .leaf z ≤ 2*z := by nlinarith
        nlinarith
      | succ n =>
        let a := (n+2)/2
        let b := (n+3)/2
        have ha : 0 < a := by dsimp [a]; omega
        have hb : 0 < b := by dsimp [b]; omega
        have hat : a < n+2 := by dsimp [a]; omega
        have hbt : b < n+2 := by dsimp [b]; omega
        have hab : a+b=n+2 := by dsimp [a,b]; omega
        have hba : a ≤ b := by dsimp [a,b]; omega
        have hba' : b ≤ a+1 := by dsimp [a,b]; omega
        have hn : balanced (n+2) = .node (balanced a) (balanced b) := by
          simp only [balanced]
          rfl
        rw [hn] at hr ⊢
        have hra := hr.trans (rho_node_lt_left _ _).le
        have hrb := hr.trans (rho_node_lt_right _ _).le
        have hcast : (a:ℝ)+(b:ℝ)=(n+2:Nat) := by exact_mod_cast hab
        have haz : (a:ℝ)*z ≤ 1/1000 := by
          have : (a:ℝ) ≤ (n+2:Nat) := by exact_mod_cast hat.le
          nlinarith
        have hbz : (b:ℝ)*z ≤ 1/1000 := by
          have : (b:ℝ) ≤ (n+2:Nat) := by exact_mod_cast hbt.le
          nlinarith
        have hbal : ((a:ℝ)+(b:ℝ))^2 ≤ 5*(a:ℝ)*(b:ℝ) := by
          have ha1 : (1:ℝ) ≤ a := by exact_mod_cast ha
          have h1 : (a:ℝ) ≤ b := by exact_mod_cast hba
          have h2 : (b:ℝ) ≤ a+1 := by exact_mod_cast hba'
          nlinarith [sq_nonneg ((b:ℝ)-(a:ℝ))]
        have h := merge_bound (Nat.cast_nonneg a) (Nat.cast_nonneg b) hz hbal
          (by simpa only [hcast] using hs)
          (branchValue_global_bounds (balanced a) hz).1
          (branchValue_global_bounds (balanced b) hz).1
          (branchValue_global_bounds _ hz).1
          (branchValue_global_bounds _ hz).2
          (ih a hat ha hra haz) (ih b hbt hb hrb hbz)
          (branch_node_quadratic _ _ hz hr)
        simpa only [hcast] using h

end LiteralDL.GrowthStage
```
<!-- END SOURCE -->

### StrictMerge

<!-- SOURCE {"module": "StrictMerge", "bytes": 2247, "sha256": "e12731420f4451b6aaaebbdf34441ca29d9fe531269c2f1808415030c4913bfb"} -->
```lean
import StrictRotation
namespace LiteralDL

theorem mergeValue_input_lt {a b : ℝ} (h : mergeValue a b < 1/2) :
    a+b+a*b < 1/4 := by
  by_contra hn
  have he := catalanBranch_saturated (le_of_not_gt hn)
  change catalanBranch (a+b+a*b) < 1/2 at h
  linarith

theorem mergeValue_strict {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hac : a < c) (hbd : b ≤ d) (hq : c+d+c*d ≤ 1/4) :
    mergeValue a b < mergeValue c d := by
  have hc : 0 ≤ c := ha.trans hac.le
  have hd : 0 ≤ d := hb.trans hbd
  have hprod := mul_le_mul hac.le hbd hb hc
  have hinput : a+b+a*b < c+d+c*d := by linarith
  exact catalanBranch_strictMono ⟨by positivity,hinput.le.trans hq⟩
    ⟨by positivity,hq⟩ hinput

theorem mergeValue_associator_lt {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hac : c < a)
    (hhalf : mergeValue (mergeValue a b) c < 1/2) :
    mergeValue a (mergeValue b c) < mergeValue (mergeValue a b) c := by
  have hx0 := mergeValue_nonneg ha hb
  have hy0 := mergeValue_nonneg hc hb
  have hxhalf : mergeValue a b < 1/2 :=
    (mergeValue_ge_left hx0 (mergeValue_half ha hb) hc).trans_lt hhalf
  have hyle : mergeValue c b ≤ mergeValue a b := mergeValue_mono hc hb hac.le le_rfl
  have hyhalf := hyle.trans_lt hxhalf
  have hqx := mergeValue_input_lt hxhalf
  have hqy := mergeValue_input_lt hyhalf
  have hx := (catalanBranch_properties (by positivity : 0 ≤ a+b+a*b) hqx.le).2.2
  have hy := (catalanBranch_properties (by positivity : 0 ≤ c+b+c*b) hqy.le).2.2
  have hxpos : 0 < mergeValue a b := by
    change 0 < catalanBranch (a+b+a*b)
    have hpos : 0 < a := lt_of_le_of_lt hc hac
    nlinarith [hx, sq_nonneg (catalanBranch (a+b+a*b)), mul_nonneg ha hb]
  have hd : mergeValue a b + mergeValue c b < 1 := by linarith
  have hs := catalan_associator_strict hx hy hac hxpos hy0 hd
  have hqout := mergeValue_input_lt hhalf
  have hinput : a+mergeValue c b+a*mergeValue c b <
      mergeValue a b+c+mergeValue a b*c := by
    change (1+a)*mergeValue c b+a < (1+c)*mergeValue a b+c at hs
    nlinarith
  rw [mergeValue_comm b c]
  exact catalanBranch_strictMono
    ⟨by positivity,hinput.le.trans hqout.le⟩ ⟨by positivity,hqout.le⟩ hinput

#print axioms mergeValue_associator_lt
end LiteralDL
```
<!-- END SOURCE -->

### CaterpillarSplit

<!-- SOURCE {"module": "CaterpillarSplit", "bytes": 2508, "sha256": "eb62101fddf96ccccba2001a9cb39f3527ad3ffed1cacefeb57973198a08c15b"} -->
```lean
import StrictMerge
namespace LiteralDL

theorem caterpillar_ne_leaf {k : Nat} (hk : 2 ≤ k) : caterpillar k ≠ .leaf := by
  cases k with
  | zero => omega
  | succ k => cases k with
    | zero => omega
    | succ k => simp [caterpillar]

theorem rho_caterpillar_split_lt {a b : Nat} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    rho (caterpillar (a+b)) < rho (.node (caterpillar a) (caterpillar b)) := by
  obtain ⟨j,rfl⟩ : ∃ j, b = j+2 := ⟨b-2,by omega⟩
  have hrot := rho_rotation_lt (caterpillar a) (caterpillar (j+1)) (caterpillar_ne_leaf ha)
  have hle := rho_caterpillar_le (.node (.node (caterpillar a) (caterpillar (j+1))) .leaf)
  have hsize : leaves (.node (.node (caterpillar a) (caterpillar (j+1))) .leaf) = a+(j+2) := by
    simp only [leaves, leaves_caterpillar (by omega : 0 < a),
      leaves_caterpillar (by omega : 0 < j+1)]
    omega
  rw [hsize] at hle
  exact hle.trans_lt hrot

theorem caterpillar_merge_lt {a b : Nat} (ha : 2 ≤ a) (hb : 2 ≤ b)
    {z : ℝ} (hz : 0 < z) (hr : z < rho (caterpillar (a+b))) :
    mergeValue (branchValue (caterpillar a) z) (branchValue (caterpillar b) z) <
      branchValue (caterpillar (a+b)) z := by
  obtain ⟨j,rfl⟩ : ∃ j, b = j+2 := ⟨b-2,by omega⟩
  have hle := rho_caterpillar_le (.node (caterpillar a) (caterpillar (j+2)))
  simp only [leaves, leaves_caterpillar (by omega : 0 < a),
    leaves_caterpillar (by omega : 0 < j+2)] at hle
  have hra : z ≤ rho (caterpillar a) :=
    (hr.le.trans hle).trans (rho_node_lt_left _ _).le
  have hac := branch_nonleaf_gt_leaf (caterpillar_ne_leaf ha) hz hra
  have hins := caterpillar_merge_le (by omega : 0 < a) (by omega : 0 < j+1) hz.le
  have houter := mergeValue_mono
    (mergeValue_nonneg (branchValue_global_bounds _ hz.le).1 (branchValue_global_bounds _ hz.le).1)
    (branchValue_global_bounds .leaf hz.le).1 hins le_rfl
  have hsucc : a+(j+2) = (a+(j+1))+1 := by omega
  have hout : mergeValue (mergeValue (branchValue (caterpillar a) z)
      (branchValue (caterpillar (j+1)) z)) (branchValue .leaf z) ≤
      branchValue (caterpillar (a+(j+2))) z := by
    rw [hsucc,caterpillar_succ (by omega : 0 < a+(j+1))]
    exact houter
  have hhalf := hout.trans_lt (branchValue_lt_half hz.le hr)
  have hs := mergeValue_associator_lt (branchValue_global_bounds _ hz.le).1
    (branchValue_global_bounds _ hz.le).1 (branchValue_global_bounds .leaf hz.le).1 hac hhalf
  exact hs.trans_le hout

#print axioms rho_caterpillar_split_lt
#print axioms caterpillar_merge_lt
end LiteralDL
```
<!-- END SOURCE -->

### GrowthFinalAsymptotic

<!-- SOURCE {"module": "GrowthFinalAsymptotic", "bytes": 1497, "sha256": "7e9bb3c2b734972a4142313d5b9447b0dea8ecf1dd3eaf30a3740458259c8aac"} -->
```lean
import GrowthFinalCaterpillar
import GrowthFinalBalanced
namespace LiteralDL.GrowthStage
open LiteralDL Filter
set_option maxHeartbeats 1000000

theorem caterpillar_square_lower (k : Nat) (hk : 0 < k) :
    (k:ℝ)^3-(k:ℝ) ≤ 3/2 * growth (caterpillar k)^2 := by
  let s := caterpillar k
  have h := caterpillar_cubic k hk (rho_pos s).le le_rfl
  have ep : branchValue (caterpillar k) (rho s) = 1/2 := (actualThreshold s).endpoint
  rw [ep] at h
  have he : growth s * rho s = 1 := le_antisymm (growth_mul_rho_le s) (growth_mul_rho_ge s)
  have hi : rho s ^2 * growth s ^2 = 1 := by
    calc
      _ = (growth s * rho s)^2 := by ring
      _ = 1 := by rw [he]; norm_num
  have hm := mul_le_mul_of_nonneg_right h (sq_nonneg (growth s))
  change (((k:ℝ)^3-(k:ℝ))/3 * rho s ^2) * growth s ^2 ≤ _ at hm
  rw [mul_assoc, hi, mul_one] at hm
  nlinarith only [hm]

theorem balanced_growth_upper (k : Nat) (hk : 0 < k) :
    growth (balanced k) ≤ 1000*(k:ℝ) := by
  let s := balanced k
  have hr := rho_pos s
  have hg := growth_pos s
  have he : growth s * rho s = 1 := le_antisymm (growth_mul_rho_le s) (growth_mul_rho_ge s)
  by_contra hn
  have hl : 1000*(k:ℝ) < growth s := lt_of_not_ge hn
  have hs : (k:ℝ)*rho s ≤ 1/1000 := by nlinarith
  have hb := balanced_value_bound k hk hr.le le_rfl hs
  have ep : branchValue (balanced k) (rho s) = 1/2 := (actualThreshold s).endpoint
  rw [ep] at hb
  have hz : 0 ≤ (k:ℝ)*rho s := by positivity
  nlinarith

end LiteralDL.GrowthStage
```
<!-- END SOURCE -->

### GrowthFinalLimit

<!-- SOURCE {"module": "GrowthFinalLimit", "bytes": 1408, "sha256": "72640daa6a5ffcf8a1b4c32e63c0ece819f37a2768c3a441ac7e28d3c069a8b2"} -->
```lean
import GrowthFinalAsymptotic
namespace LiteralDL.GrowthStage
open LiteralDL Filter
set_option maxHeartbeats 1000000

theorem caterpillar_superlinear :
    Tendsto (fun k : Nat => growth (caterpillar k)/(k:ℝ)) atTop atTop := by
  apply tendsto_atTop.2
  intro M
  obtain ⟨N,hN⟩ := exists_nat_gt (3*M^2+2)
  filter_upwards [eventually_ge_atTop N] with k hk
  have hNk : (N:ℝ) ≤ k := by exact_mod_cast hk
  have hk2 : (2:ℝ) < k := by nlinarith [sq_nonneg M]
  have hk0 : (0:ℝ) < k := by linarith
  have hkn : 0 < k := by exact_mod_cast hk0
  by_cases hM : M ≤ 0
  · exact hM.trans (div_nonneg (growth_pos _).le hk0.le)
  have hMp : 0 < M := lt_of_not_ge hM
  by_contra hnot
  have hlt : growth (caterpillar k)/(k:ℝ) < M := lt_of_not_ge hnot
  have hglt : growth (caterpillar k) < M*(k:ℝ) := (div_lt_iff₀ hk0).mp hlt
  have hg := growth_pos (caterpillar k)
  have hsq : growth (caterpillar k)^2 < M^2*(k:ℝ)^2 := by
    nlinarith only [hglt, hg, mul_pos hMp hk0]
  have hc := caterpillar_square_lower k hkn
  have hkk : 2*(k:ℝ) ≤ (k:ℝ)^3 := by
    have hp := mul_nonneg (show 0 ≤ (k:ℝ)^2-2 by nlinarith only [hk2]) hk0.le
    nlinarith only [hp]
  have hg3 : (k:ℝ)^3 ≤ 3*growth (caterpillar k)^2 := by nlinarith only [hc,hkk]
  have hkp : 0 < (k:ℝ)-3*M^2 := by linarith
  have hp := mul_pos hkp (sq_pos_of_pos hk0)
  nlinarith only [hp,hsq,hg3]

end LiteralDL.GrowthStage
```
<!-- END SOURCE -->

### StrictExtension

<!-- SOURCE {"module": "StrictExtension", "bytes": 2138, "sha256": "38e57abce07dbf9b4cafd8a128f2d8d823cabd45a86f3452f39fcfd2ead9cb26"} -->
```lean
import CaterpillarSplit
namespace LiteralDL

theorem ShapeIso.branch_eq {s t} (h : ShapeIso s t) (z : ℝ) :
    branchValue s z = branchValue t z := by
  induction h with
  | leaf => rfl
  | node ha hb ia ib => simp only [branchValue,ia,ib]
  | swap ha hb ia ib =>
    simp only [branchValue,ia,ib]
    congr 1
    ring

theorem node_input_le_quarter (a b : Species) {z : ℝ} (hz : 0 ≤ z)
    (hr : z ≤ rho (.node a b)) :
    branchValue a z + branchValue b z + branchValue a z * branchValue b z ≤ 1/4 := by
  have he := branch_node_quadratic a b hz hr
  nlinarith [sq_nonneg (branchValue (.node a b) z - 1/2)]

theorem strict_leaf_extension (s t : Species)
    (hglobal : ∀ z : ℝ, 0 ≤ z → branchValue s z ≤ branchValue t z)
    (hstrict : ∀ z : ℝ, 0 < z → z < rho t → branchValue s z < branchValue t z) :
    rho (.node t .leaf) < rho (.node s .leaf) ∧
      ∀ z : ℝ, 0 < z → z < rho (.node t .leaf) →
        branchValue (.node s .leaf) z < branchValue (.node t .leaf) z := by
  have hval : ∀ z : ℝ, 0 < z → z ≤ rho (.node t .leaf) →
      branchValue (.node s .leaf) z < branchValue (.node t .leaf) z := by
    intro z hz hr
    have hchild : z < rho t := hr.trans_lt (rho_node_lt_left t .leaf)
    exact mergeValue_strict (branchValue_global_bounds s hz.le).1
      (branchValue_global_bounds .leaf hz.le).1 (hstrict z hz hchild) le_rfl
      (node_input_le_quarter t .leaf hz.le hr)
  constructor
  · have hle : rho (.node t .leaf) ≤ rho (.node s .leaf) := by
      apply rho_le_of_global_branch_le
      intro z hz
      exact mergeValue_mono (branchValue_global_bounds s hz).1
        (branchValue_global_bounds .leaf hz).1 (hglobal z hz) le_rfl
    apply lt_of_le_of_ne hle
    intro heq
    have h := hval (rho (.node t .leaf)) (rho_pos _) le_rfl
    have ht : branchValue (.node t .leaf) (rho (.node t .leaf)) = 1/2 :=
      (actualThreshold _).endpoint
    have hs : branchValue (.node s .leaf) (rho (.node t .leaf)) = 1/2 :=
      heq ▸ (actualThreshold _).endpoint
    linarith
  · intro z hz hr
    exact hval z hz hr.le

#print axioms strict_leaf_extension
end LiteralDL
```
<!-- END SOURCE -->

### GrowthFinalEndpoint

<!-- SOURCE {"module": "GrowthFinalEndpoint", "bytes": 2504, "sha256": "bbfa7accf40cc630bf8ac614f358dcda7e3396e6e080af1f1a85b88dc899fb92"} -->
```lean
import GrowthFinalLimit
namespace LiteralDL.GrowthStage
open LiteralDL Filter

theorem source_growth_component :
    (∀ s : Species, 0 < growth s ∧
      Tendsto (fun n : Nat => (count s n : ℝ) ^ (1/(n:ℝ))) atTop (nhds (growth s)) ∧
      growth s = (rho s)⁻¹) ∧
    (∀ k : Nat, 0 < k → leaves (caterpillar k) = k ∧ leaves (balanced k) = k ∧
      2*(k:ℝ) ≤ growth (balanced k) ∧ growth (balanced k) ≤ 1000*(k:ℝ) ∧
      (k:ℝ)^3-(k:ℝ) ≤ 3/2*growth (caterpillar k)^2) ∧
    Tendsto (fun k : Nat => growth (caterpillar k)/(k:ℝ)) atTop atTop ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : Nat, ∀ k : Nat, N ≤ k →
      c*(k:ℝ) ≤ growth (balanced k) ∧ growth (balanced k) ≤ C*(k:ℝ)) := by
  refine ⟨?_, ?_, caterpillar_superlinear, ?_⟩
  · intro s
    exact ⟨growth_pos s, actual_root_limit s, growth_eq_inv_rho s⟩
  · intro k hk
    refine ⟨leaves_caterpillar hk, leaves_balanced hk, ?_, balanced_growth_upper k hk,
      caterpillar_square_lower k hk⟩
    simpa only [leaves_balanced hk] using growth_lower (balanced k)
  · refine ⟨2,1000,by norm_num,by norm_num,1,?_⟩
    intro k hk
    refine ⟨?_,balanced_growth_upper k (by omega)⟩
    simpa only [leaves_balanced (by omega : 0 < k)] using growth_lower (balanced k)

theorem auxiliary_conventions : caterpillar 0 = .leaf ∧ balanced 0 = .leaf ∧
    (∀ s : Species, count s 0 = 0) ∧
    growth (caterpillar 0)/(0:ℝ) = 0 := by
  simp [caterpillar, balanced, count_zero]

theorem growth_shapeIso {s t : Species} (h : ShapeIso s t) : growth s = growth t := by
  rw [growth_eq_inv_rho, growth_eq_inv_rho, h.rho_eq]

theorem balanced_shape_growth {s : Species} {k : Nat} (hk : 0 < k)
    (h : ShapeIso s (balanced k)) :
    leaves s = k ∧ 2*(k:ℝ) ≤ growth s ∧ growth s ≤ 1000*(k:ℝ) := by
  rw [growth_shapeIso h]
  exact ⟨h.leaves_eq.trans (leaves_balanced hk),
    by simpa only [leaves_balanced hk] using growth_lower (balanced k),
    balanced_growth_upper k hk⟩

theorem caterpillar_family_superlinear (f : Nat → Species)
    (h : ∀ k, ShapeIso (f k) (caterpillar k)) :
    Tendsto (fun k : Nat => growth (f k)/(k:ℝ)) atTop atTop := by
  have he : (fun k : Nat => growth (f k)/(k:ℝ)) =
      (fun k : Nat => growth (caterpillar k)/(k:ℝ)) := by
    funext k
    rw [growth_shapeIso (h k)]
  rw [he]
  exact caterpillar_superlinear

#print axioms source_growth_component
#print axioms auxiliary_conventions
end LiteralDL.GrowthStage
```
<!-- END SOURCE -->

### LeafExpansion

<!-- SOURCE {"module": "LeafExpansion", "bytes": 2321, "sha256": "419dbdf9c43cb6dd5096f311035930f0219b7aeced926fddf11d56cf29572ffb"} -->
```lean
import StrictExtension
namespace LiteralDL
inductive LeafExpansion : Species → Species → Prop where
  | cherry : LeafExpansion .leaf (.node .leaf .leaf)
  | left {a b c} : LeafExpansion a b → LeafExpansion (.node a c) (.node b c)
  | right {a b c} : LeafExpansion a b → LeafExpansion (.node c a) (.node c b)

theorem LeafExpansion.global_le {s t} (h : LeafExpansion s t) {z : ℝ} (hz : 0 ≤ z) :
    branchValue s z ≤ branchValue t z := by
  induction h with
  | cherry =>
    exact mergeValue_ge_left (branchValue_global_bounds .leaf hz).1
      (branchValue_global_bounds .leaf hz).2 (branchValue_global_bounds .leaf hz).1
  | @left a b c h ih =>
    exact mergeValue_mono (branchValue_global_bounds a hz).1
      (branchValue_global_bounds c hz).1 ih le_rfl
  | @right a b c h ih =>
    exact mergeValue_mono (branchValue_global_bounds c hz).1
      (branchValue_global_bounds a hz).1 le_rfl ih

theorem LeafExpansion.strict_value {s t} (h : LeafExpansion s t) {z : ℝ}
    (hz : 0 < z) (hr : z ≤ rho t) : branchValue s z < branchValue t z := by
  induction h with
  | cherry => exact branch_node_gt_left .leaf .leaf hz hr
  | @left a b c h ih =>
    exact mergeValue_strict (branchValue_global_bounds a hz.le).1
      (branchValue_global_bounds c hz.le).1
      (ih (hr.trans (rho_node_lt_left b c).le)) le_rfl
      (node_input_le_quarter b c hz.le hr)
  | @right a b c h ih =>
    have hs : branchValue (.node c a) z = mergeValue (branchValue a z) (branchValue c z) := mergeValue_comm _ _
    have ht : branchValue (.node c b) z = mergeValue (branchValue b z) (branchValue c z) := mergeValue_comm _ _
    rw [hs,ht]
    have hq := node_input_le_quarter c b hz.le hr
    exact mergeValue_strict (branchValue_global_bounds a hz.le).1
      (branchValue_global_bounds c hz.le).1
      (ih (hr.trans (rho_node_lt_right c b).le)) le_rfl (by nlinarith)

theorem LeafExpansion.rho_lt {s t} (h : LeafExpansion s t) : rho t < rho s := by
  have hle := rho_le_of_global_branch_le s t (fun _ hz => h.global_le hz)
  apply lt_of_le_of_ne hle
  intro he
  have hh := h.strict_value (rho_pos t) le_rfl
  have hs : branchValue s (rho t) = 1/2 := he ▸ (actualThreshold s).endpoint
  have ht : branchValue t (rho t) = 1/2 := (actualThreshold t).endpoint
  linarith

#print axioms LeafExpansion.rho_lt
end LiteralDL
```
<!-- END SOURCE -->

### StrictCaterpillar

<!-- SOURCE {"module": "StrictCaterpillar", "bytes": 2914, "sha256": "2db213a95a82e9b2211bfe0eba32bdd8e13d9a75a2c0d79e7d1d3bfdc2a113e4"} -->
```lean
import StrictExtension
namespace LiteralDL

theorem leaves_ge_two_of_nonleaf {s : Species} (hs : s ≠ .leaf) : 2 ≤ leaves s := by
  cases s with
  | leaf => exact (hs rfl).elim
  | node a b => have := leaves_pos a; have := leaves_pos b; simp only [leaves]; omega

theorem caterpillar_dichotomy (s : Species) :
    ShapeIso s (caterpillar (leaves s)) ∨
      (rho (caterpillar (leaves s)) < rho s ∧
        ∀ z : ℝ, 0 < z → z < rho (caterpillar (leaves s)) →
          branchValue s z < branchValue (caterpillar (leaves s)) z) := by
  induction s with
  | leaf => exact Or.inl .leaf
  | node a b ia ib =>
    by_cases ha : a = .leaf
    · subst a
      have he : caterpillar (leaves (.node .leaf b)) = .node (caterpillar (leaves b)) .leaf := by
        rw [leaves,show leaves .leaf + leaves b = leaves b+1 by simp [leaves,Nat.add_comm],
          caterpillar_succ (leaves_pos b)]
      rw [he]
      rcases ib with hi | hs
      · exact Or.inl (.swap .leaf hi)
      · right
        have h := strict_leaf_extension b (caterpillar (leaves b))
          (fun _ hz => branchValue_le_caterpillar b hz) hs.2
        constructor
        · rw [rho_swap .leaf b]; exact h.1
        · intro z hz hr
          have hswap : branchValue (.node .leaf b) z = branchValue (.node b .leaf) z :=
            mergeValue_comm _ _
          rw [hswap]
          exact h.2 z hz hr
    · by_cases hb : b = .leaf
      · subst b
        have he : caterpillar (leaves (.node a .leaf)) = .node (caterpillar (leaves a)) .leaf := by
          rw [leaves,show leaves a + leaves .leaf = leaves a+1 by rfl,
            caterpillar_succ (leaves_pos a)]
        rw [he]
        rcases ia with hi | hs
        · exact Or.inl (.node hi .leaf)
        · exact Or.inr (strict_leaf_extension a (caterpillar (leaves a))
            (fun _ hz => branchValue_le_caterpillar a hz) hs.2)
      · right
        have hla := leaves_ge_two_of_nonleaf ha
        have hlb := leaves_ge_two_of_nonleaf hb
        have hglob : ∀ z : ℝ, 0 ≤ z → branchValue (.node a b) z ≤
            branchValue (.node (caterpillar (leaves a)) (caterpillar (leaves b))) z := by
          intro z hz
          exact mergeValue_mono (branchValue_global_bounds a hz).1
            (branchValue_global_bounds b hz).1 (branchValue_le_caterpillar a hz)
            (branchValue_le_caterpillar b hz)
        constructor
        · exact (rho_caterpillar_split_lt hla hlb).trans_le
            (rho_le_of_global_branch_le _ _ hglob)
        · intro z hz hr
          exact (hglob z hz.le).trans_lt (caterpillar_merge_lt hla hlb hz hr)

theorem rho_caterpillar_strict (s : Species)
    (hs : ¬ ShapeIso s (caterpillar (leaves s))) :
    rho (caterpillar (leaves s)) < rho s := by
  rcases caterpillar_dichotomy s with hi | hi
  · exact (hs hi).elim
  · exact hi.1

#print axioms caterpillar_dichotomy
#print axioms rho_caterpillar_strict
end LiteralDL
```
<!-- END SOURCE -->

### BalancedExpansion

<!-- SOURCE {"module": "BalancedExpansion", "bytes": 1242, "sha256": "dd5831e68ca4948dbb67b25151466d1989b3a5365f6ee5ac7f90703afe066a4f"} -->
```lean
import LeafExpansion
namespace LiteralDL

theorem balanced_node {k : Nat} (hk : 2 ≤ k) :
    balanced k = .node (balanced (k/2)) (balanced ((k+1)/2)) := by
  cases k with
  | zero => omega
  | succ k => cases k with
    | zero => omega
    | succ k => simp [balanced,Nat.add_assoc]

theorem balanced_successor_expansion {k : Nat} (hk : 0 < k) :
    LeafExpansion (balanced k) (balanced (k+1)) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases h1 : k = 1
    · subst k
      simpa [balanced] using LeafExpansion.cherry
    have hk2 : 2 ≤ k := by omega
    rw [balanced_node hk2, balanced_node (by omega : 2 ≤ k+1)]
    by_cases he : k%2 = 0
    · have h0 : (k+1)/2 = k/2 := by omega
      have h1 : (k+1+1)/2 = k/2+1 := by omega
      rw [h0,h1]
      exact .right (ih (k/2) (by omega) (by omega))
    · have h0 : (k+1)/2 = k/2+1 := by omega
      have h1 : (k+1+1)/2 = k/2+1 := by omega
      rw [h0,h1]
      exact .left (ih (k/2) (by omega) (by omega))

theorem rho_balanced_successor_lt {k : Nat} (hk : 0 < k) :
    rho (balanced (k+1)) < rho (balanced k) := (balanced_successor_expansion hk).rho_lt

#print axioms balanced_successor_expansion
#print axioms rho_balanced_successor_lt
end LiteralDL
```
<!-- END SOURCE -->

### CaterpillarCounts

<!-- SOURCE {"module": "CaterpillarCounts", "bytes": 2159, "sha256": "b7712bb6a212b064edb9882cbc9bff233156b6736d9c8c338d9b34ccae8910df"} -->
```lean
import StrictCaterpillar
import Mathlib.Order.Filter.Finite
namespace LiteralDL

theorem eventual_count_lt_of_growth_lt (s t : Species) (hg : growth s < growth t) :
    ∀ᶠ n : Nat in Filter.atTop, count s n < count t n := by
  obtain ⟨c,hsc,hct⟩ := exists_between hg
  have hs := (actual_root_limit s).eventually_lt_const hsc
  have ht := (actual_root_limit t).eventually_const_lt hct
  filter_upwards [hs,ht] with n hn hm
  by_contra hc
  have hle : (count t n : ℝ) ≤ count s n := by exact_mod_cast le_of_not_gt hc
  have hp := Real.rpow_le_rpow (Nat.cast_nonneg (count t n)) hle
    (show (0:ℝ) ≤ 1/(n:ℝ) by positivity)
  linarith

theorem eventual_count_lt_of_rho_lt (s t : Species) (hr : rho t < rho s) :
    ∀ᶠ n : Nat in Filter.atTop, count s n < count t n := by
  apply eventual_count_lt_of_growth_lt
  rw [growth_eq_inv_rho s,growth_eq_inv_rho t]
  exact (inv_lt_inv₀ (rho_pos s) (rho_pos t)).mpr hr

theorem eventual_caterpillar_maximum (k : Nat) : ∃ N : Nat, 1 ≤ N ∧
    ∀ s : Species, leaves s = k → ∀ n : Nat, N ≤ n →
      count s n ≤ count (caterpillar k) n ∧
      (count s n = count (caterpillar k) n ↔ ShapeIso s (caterpillar k)) := by
  have hall : ∀ s : {s : Species // leaves s = k}, ∀ᶠ n : Nat in Filter.atTop,
      count s.1 n ≤ count (caterpillar k) n ∧
      (count s.1 n = count (caterpillar k) n ↔ ShapeIso s.1 (caterpillar k)) := by
    intro s
    by_cases hi : ShapeIso s.1 (caterpillar k)
    · exact Filter.Eventually.of_forall (fun n => ⟨(hi.count_eq n).le,⟨fun _ => hi,fun _ => hi.count_eq n⟩⟩)
    · have hr : rho (caterpillar k) < rho s.1 := by
        have h := rho_caterpillar_strict s.1
        rw [s.2] at h
        exact h hi
      filter_upwards [eventual_count_lt_of_rho_lt s.1 (caterpillar k) hr] with n hn
      exact ⟨hn.le,⟨fun he => (ne_of_lt hn he).elim,fun hh => (hi hh).elim⟩⟩
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp (Filter.eventually_all.mpr hall)
  refine ⟨max 1 N,le_max_left _ _,?_⟩
  intro s hs n hn
  exact hN n ((le_max_right _ _).trans hn) ⟨s,hs⟩

#print axioms eventual_caterpillar_maximum
end LiteralDL
```
<!-- END SOURCE -->

### BalancedFinalDiscrete

<!-- SOURCE {"module": "BalancedFinalDiscrete", "bytes": 4179, "sha256": "e17d676a1f8c19a797ae3b600d3378007a413ec802db98cdc71d38c966ddd7e8"} -->
```lean
import LogConjugateExpansive
import BalancedExpansion
namespace LiteralDL.BalancedStage
open LiteralDL

theorem strict_midpoint {x y z : ℝ}
    (hx : x ∈ Set.Icc 0 (Real.log (5/4)))
    (hy : y ∈ Set.Icc 0 (Real.log (5/4)))
    (hz : z ∈ Set.Icc 0 (Real.log (5/4)))
    (hxz : x < z) (hm : 2*y ≤ x+z) :
    2*logConjugate y < logConjugate x+logConjugate z := by
  have hmid : (x+z)/2 ∈ Set.Icc 0 (Real.log (5/4)) := ⟨by linarith [hx.1,hz.1],by linarith [hx.2,hz.2]⟩
  have hj := logConjugate_strictConvex.2 hx hz (ne_of_lt hxz)
    (show (0:ℝ)<1/2 by norm_num) (show (0:ℝ)<1/2 by norm_num)
    (show (1/2:ℝ)+1/2=1 by norm_num)
  have he : (1/2:ℝ)*x+(1/2)*z = (x+z)/2 := by ring
  simp only [smul_eq_mul] at hj
  rw [he] at hj
  have hle : logConjugate y ≤ logConjugate ((x+z)/2) := by
    rcases lt_or_eq_of_le (show y ≤ (x+z)/2 by linarith) with h|h
    · have hh := logConjugate_expansive hy hmid h
      linarith
    · rw [h]
  linarith

/-- Finite, closed-domain version; no value beyond K is used. -/
theorem discrete_convex (b : Nat → ℝ) (K : Nat)
    (hpos : 0 < b 1)
    (hinc : ∀ i, 1 ≤ i → i+1 ≤ K → b i < b (i+1))
    (hdom : ∀ i, 2 ≤ i → i ≤ K →
      b (i/2)+b ((i+1)/2) ∈ Set.Icc 0 (Real.log (5/4)))
    (hrec : ∀ i, 2 ≤ i → i ≤ K →
      b i = logConjugate (b (i/2)+b ((i+1)/2))) :
    ∀ n, 2 ≤ n → n+1 ≤ K → 2*b n < b (n-1)+b (n+1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn hnK
    by_cases htwo : n=2
    · subst n
      have h2 := hrec 2 (by omega) (by omega)
      have h3 := hrec 3 (by omega) hnK
      norm_num at h2 h3
      have hd2 := hdom 2 (by omega) (by omega)
      have hd3 := hdom 3 (by omega) hnK
      norm_num only [Nat.reduceDiv, Nat.reduceAdd] at hd2 hd3
      have hzero : (0:ℝ) ∈ Set.Icc 0 (Real.log (5/4)) :=
        ⟨le_rfl, Real.log_nonneg (by norm_num)⟩
      have he := logConjugate_expansive hzero hd2 (by linarith : 0 < b 1+b 1)
      rw [logConjugate_zero, ← h2] at he
      have he2 := logConjugate_expansive hd2 hd3 (by linarith : b 1+b 1 < b 1+b 2)
      rw [← h2, ← h3] at he2
      norm_num
      linarith
    · let m := n/2
      have hm : 1 ≤ m := by dsimp [m]; omega
      have hmi : m+1 ≤ K := by dsimp [m]; omega
      have hm_lt : b m < b (m+1) := hinc m hm hmi
      have h0 := hdom (n-1) (by omega) (by omega)
      have h1 := hdom n hn (by omega)
      have h2 := hdom (n+1) (by omega) hnK
      rw [hrec n hn (by omega), hrec (n-1) (by omega) (by omega),
        hrec (n+1) (by omega) hnK]
      apply strict_midpoint h0 h1 h2
      · by_cases hp : n%2=0
        · have hh : 2 ≤ m := by dsimp [m]; omega
          have he := hinc (m-1) (by omega) (by omega)
          have e0 : (n-1)/2=m-1 := by dsimp [m]; omega
          have e1 : (n-1+1)/2=m := by dsimp [m]; omega
          have e2 : (n+1)/2=m := by dsimp [m]; omega
          have e3 : (n+1+1)/2=m+1 := by dsimp [m]; omega
          rw [e0,e1,e2,e3]
          have em : m-1+1=m := by omega
          rw [em] at he
          linarith
        · have e0 : (n-1)/2=m := by dsimp [m]; omega
          have e1 : (n-1+1)/2=m := by dsimp [m]; omega
          have e2 : (n+1)/2=m+1 := by dsimp [m]; omega
          have e3 : (n+1+1)/2=m+1 := by dsimp [m]; omega
          rw [e0,e1,e2,e3]
          linarith
      · by_cases hp : n%2=0
        · have hh : 2 ≤ m := by dsimp [m]; omega
          have hc := ih m (by dsimp [m]; omega) hh hmi
          have e0 : (n-1)/2=m-1 := by dsimp [m]; omega
          have e1 : (n-1+1)/2=m := by dsimp [m]; omega
          have e2 : (n+1)/2=m := by dsimp [m]; omega
          have e3 : (n+1+1)/2=m+1 := by dsimp [m]; omega
          change 2*(b m+b ((n+1)/2)) ≤ _
          rw [e0,e1,e2,e3]
          linarith
        · have e0 : (n-1)/2=m := by dsimp [m]; omega
          have e1 : (n-1+1)/2=m := by dsimp [m]; omega
          have e2 : (n+1)/2=m+1 := by dsimp [m]; omega
          have e3 : (n+1+1)/2=m+1 := by dsimp [m]; omega
          change 2*(b m+b ((n+1)/2)) ≤ _
          rw [e0,e1,e2,e3]
          linarith

#print axioms discrete_convex
end LiteralDL.BalancedStage
```
<!-- END SOURCE -->

### ProgressAudit

<!-- SOURCE {"module": "ProgressAudit", "bytes": 682, "sha256": "4b698cacc31ee352c1d0e9c3ece0a922420bfa0f803dca9f79d30e9951733a3a"} -->
```lean
import ClosureAudit
import CaterpillarCounts
import BalancedExpansion
import LogConjugateExpansive
#print LiteralDL.eventual_caterpillar_maximum
#print LiteralDL.rho_caterpillar_strict
#print axioms LiteralDL.ShapeIso.refl
#print axioms LiteralDL.ShapeIso.symm
#print axioms LiteralDL.ShapeIso.trans
#print axioms LiteralDL.ShapeIso.count_eq
#print axioms LiteralDL.ShapeIso.rho_eq
#print axioms LiteralDL.rho_caterpillar_strict
#print axioms LiteralDL.eventual_caterpillar_maximum
#print axioms LiteralDL.balanced_successor_expansion
#print axioms LiteralDL.rho_balanced_successor_lt
#print axioms LiteralDL.logConjugate_strictConvex
#print axioms LiteralDL.logConjugate_expansive
```
<!-- END SOURCE -->

### BalancedFinalSplit

<!-- SOURCE {"module": "BalancedFinalSplit", "bytes": 2813, "sha256": "c599a261ffcce4937f53268a1a7a1b16d0c0c5ffcf50488ea3024a46becb9908"} -->
```lean
import BalancedFinalDiscrete
namespace LiteralDL.BalancedStage

theorem delta_lt (b : Nat → ℝ) (K : Nat)
    (hc : ∀ n, 2 ≤ n → n+1 ≤ K → 2*b n < b (n-1)+b (n+1))
    {i j : Nat} (hi : 1 ≤ i) (hij : i < j) (hj : j+1 ≤ K) :
    b (i+1)-b i < b (j+1)-b j := by
  have step : ∀ j, i+1 ≤ j → j+1 ≤ K → b (i+1)-b i < b (j+1)-b j := by
    intro j hji
    induction j, hji using Nat.le_induction with
    | base =>
      intro hk
      have h := hc (i+1) (by omega) hk
      have he : i+1-1=i := by omega
      rw [he] at h
      linarith
    | succ j hji ih =>
      intro hk
      have h := hc (j+1) (by omega) hk
      have he : j+1-1=j := by omega
      rw [he] at h
      have hh := ih (by omega)
      linarith
  exact step j (by omega) hj

theorem split_ordered (b : Nat → ℝ) (K : Nat)
    (hc : ∀ n, 2 ≤ n → n+1 ≤ K → 2*b n < b (n-1)+b (n+1)) :
    ∀ i j : Nat, 1 ≤ i → i ≤ j → i+j ≤ K →
      b ((i+j)/2)+b ((i+j+1)/2) ≤ b i+b j ∧
      (b ((i+j)/2)+b ((i+j+1)/2) = b i+b j ↔ j ≤ i+1) := by
  have main : ∀ d i j : Nat, j-i=d → 1 ≤ i → i ≤ j → i+j ≤ K →
      b ((i+j)/2)+b ((i+j+1)/2) ≤ b i+b j ∧
      (b ((i+j)/2)+b ((i+j+1)/2) = b i+b j ↔ j ≤ i+1) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro i j hd hi hij hk
      by_cases hnear : j ≤ i+1
      · have e0 : (i+j)/2=i := by omega
        have e1 : (i+j+1)/2=j := by omega
        rw [e0,e1]
        exact ⟨le_rfl,⟨fun _ => hnear,fun _ => rfl⟩⟩
      · have hdelta := delta_lt b K hc hi (show i<j-1 by omega) (by omega)
        have he : j-1+1=j := by omega
        rw [he] at hdelta
        have hs : i+1+(j-1)=i+j := by omega
        have hinner := ih ((j-1)-(i+1)) (by omega) (i+1) (j-1) rfl
          (by omega) (by omega) (by omega)
        rw [hs] at hinner
        have hh : b ((i+j)/2)+b ((i+j+1)/2) < b i+b j := by linarith [hinner.1]
        exact ⟨hh.le,⟨fun h => (ne_of_lt hh h).elim, fun h => (hnear h).elim⟩⟩
  intro i j hi hij hk
  exact main (j-i) i j rfl hi hij hk

theorem split_min (b : Nat → ℝ) (K : Nat)
    (hc : ∀ n, 2 ≤ n → n+1 ≤ K → 2*b n < b (n-1)+b (n+1))
    {i j : Nat} (hi : 1 ≤ i) (hj : 1 ≤ j) (hk : i+j ≤ K) :
      b ((i+j)/2)+b ((i+j+1)/2) ≤ b i+b j ∧
      (b ((i+j)/2)+b ((i+j+1)/2) = b i+b j ↔ i ≤ j+1 ∧ j ≤ i+1) := by
  rcases le_total i j with hij|hji
  · have h := split_ordered b K hc i j hi hij hk
    exact ⟨h.1, h.2.trans ⟨fun hh => ⟨by omega,hh⟩,fun hh => hh.2⟩⟩
  · have h := split_ordered b K hc j i hj hji (by omega)
    rw [Nat.add_comm j i, add_comm (b j) (b i)] at h
    exact ⟨h.1,h.2.trans ⟨fun hh => ⟨hh,by omega⟩,fun hh => hh.1⟩⟩

#print axioms split_min
end LiteralDL.BalancedStage
```
<!-- END SOURCE -->

### GrowthFinalAudit

<!-- SOURCE {"module": "GrowthFinalAudit", "bytes": 10655, "sha256": "3286e0f2a23bf8d3afb67af7ef0ea0d5afe2a94bab6c9688fc6acd137f66b5fa"} -->
```lean
import ActualRootLimit
import ActualThreshold
import AtomMass
import BalancedExpansion
import BranchDomain
import BranchGlobal
import BranchRegularity
import CardinalRecurrence
import CatalanAssociator
import CatalanDerivative
import CaterpillarCounts
import CaterpillarOrder
import CaterpillarSplit
import ClippedCatalan
import ClosureAudit
import ConjugateSlope
import DuplicationSkeleton
import EndpointAudit
import FiniteShapes
import GeometricBridge
import GrowthFinalAsymptotic
import GrowthFinalBalanced
import GrowthFinalBounds
import GrowthFinalCaterpillar
import GrowthFinalEndpoint
import GrowthFinalLimit
import GrowthFinalScalar
import HistoryEvaluation
import HistoryOrder
import LeafExpansion
import LeastFixedPoint
import LiteralHistory
import LogConjugateConvex
import LogConjugateExpansive
import LogFekete
import ProgressAudit
import RealAssociator
import ScalarBranch
import ScalarEvaluation
import ShapeTransport
import SourceFiber
import SourceHistory
import SourceWeighted
import SpeciesShapes
import StrictCaterpillar
import StrictChildThreshold
import StrictExtension
import StrictMerge
import StrictRotation
import ThresholdFacts
import ThresholdIdentity
import ThresholdUniqueness
import WeightedSkeleton
#print LiteralDL.GrowthStage.source_growth_component
#print axioms LiteralDL.growth
#print axioms LiteralDL.growth_pos
#print axioms LiteralDL.actual_root_limit
#print axioms LiteralDL.ActualThreshold
#print axioms LiteralDL.leafThreshold
#print axioms LiteralDL.nodeThreshold
#print axioms LiteralDL.actualThreshold
#print axioms LiteralDL.atomNodeEquiv
#print axioms LiteralDL.atomMass_node
#print axioms LiteralDL.total_eq_of_mass_eq
#print axioms LiteralDL.balanced_node
#print axioms LiteralDL.balanced_successor_expansion
#print axioms LiteralDL.rho_balanced_successor_lt
#print axioms LiteralDL.branchValue_nonneg
#print axioms LiteralDL.branchValue_pos
#print axioms LiteralDL.branchValue_lt_half
#print axioms LiteralDL.branch_node_quadratic
#print axioms LiteralDL.branchValue_global_bounds
#print axioms LiteralDL.branchValue_ge_leaf
#print axioms LiteralDL.rho_le_of_global_branch_le
#print axioms LiteralDL.branchValue
#print axioms LiteralDL.continuous_catalanBranch
#print axioms LiteralDL.branchValue_continuous
#print axioms LiteralDL.catalanBranch_zero
#print axioms LiteralDL.catalanBranch_quarter
#print axioms LiteralDL.branchValue_zero
#print axioms LiteralDL.catalanBranch_strictMono
#print axioms LiteralDL.PairFiber
#print axioms LiteralDL.Split
#print axioms LiteralDL.splitEquiv
#print axioms LiteralDL.pairCount
#print axioms LiteralDL.NodeRoot
#print axioms LiteralDL.nodeJoin
#print axioms LiteralDL.nodeCut
#print axioms LiteralDL.nodeEquiv
#print axioms LiteralDL.count_node
#print axioms LiteralDL.pairCount_eq
#print axioms LiteralDL.LeafRoot
#print axioms LiteralDL.leafJoin
#print axioms LiteralDL.leafCut
#print axioms LiteralDL.leafEquiv
#print axioms LiteralDL.count_leaf
#print axioms LiteralDL.count_node_convolution
#print axioms LiteralDL.catalan_associator_identity
#print axioms LiteralDL.catalan_associator_strict
#print axioms LiteralDL.hasDerivAt_catalanBranch
#print axioms LiteralDL.logConjugate
#print axioms LiteralDL.hasDerivAt_logConjugate
#print axioms LiteralDL.eventual_count_lt_of_growth_lt
#print axioms LiteralDL.eventual_count_lt_of_rho_lt
#print axioms LiteralDL.eventual_caterpillar_maximum
#print axioms LiteralDL.caterpillar_succ
#print axioms LiteralDL.caterpillar_merge_le
#print axioms LiteralDL.branchValue_le_caterpillar
#print axioms LiteralDL.rho_caterpillar_le
#print axioms LiteralDL.caterpillar_ne_leaf
#print axioms LiteralDL.rho_caterpillar_split_lt
#print axioms LiteralDL.caterpillar_merge_lt
#print axioms LiteralDL.catalanBranch_global_bounds
#print axioms LiteralDL.catalanBranch_saturated
#print axioms LiteralDL.catalanBranch_mono
#print axioms LiteralDL.mergeValue
#print axioms LiteralDL.mergeValue_nonneg
#print axioms LiteralDL.mergeValue_half
#print axioms LiteralDL.mergeValue_mono
#print axioms LiteralDL.mergeValue_comm
#print axioms LiteralDL.mergeValue_ge_left
#print axioms LiteralDL.conjugateSlope
#print axioms LiteralDL.conjugateSlope_den_pos
#print axioms LiteralDL.conjugateSlope_gt_one
#print axioms LiteralDL.conjugateSlope_strictMono
#print axioms LiteralDL.deriv_logConjugate
#print axioms LiteralDL.Skeleton
#print axioms LiteralDL.Atom
#print axioms LiteralDL.atomHist
#print axioms LiteralDL.assemble
#print axioms LiteralDL.cutSkeleton
#print axioms LiteralDL.assemble_cut
#print axioms LiteralDL.cut_assemble
#print axioms LiteralDL.skeletonEquiv
#print axioms LiteralDL.skeletonSize
#print axioms LiteralDL.assemble_size
#print axioms LiteralDL.speciesPool
#print axioms LiteralDL.mem_speciesPool
#print axioms LiteralDL.count_le_growth_pow
#print axioms LiteralDL.finite_below_growth
#print axioms LiteralDL.GrowthStage.caterpillar_square_lower
#print axioms LiteralDL.GrowthStage.balanced_growth_upper
#print axioms LiteralDL.GrowthStage.balanced_value_bound
#print axioms LiteralDL.GrowthStage.leaf_quadratic
#print axioms LiteralDL.GrowthStage.leaf_mass
#print axioms LiteralDL.GrowthStage.growth_lower
#print axioms LiteralDL.GrowthStage.caterpillar_cubic
#print axioms LiteralDL.GrowthStage.source_growth_component
#print axioms LiteralDL.GrowthStage.auxiliary_conventions
#print axioms LiteralDL.GrowthStage.caterpillar_superlinear
#print axioms LiteralDL.GrowthStage.merge_bound
#print axioms LiteralDL.atomMass_leaf
#print axioms LiteralDL.historySum_leaf_principal
#print axioms LiteralDL.historySum_leaf_infinite
#print axioms LiteralDL.historySum_node_principal
#print axioms LiteralDL.mass_le_total
#print axioms LiteralDL.historySum_node_ge_left
#print axioms LiteralDL.historySum_node_ge_right
#print axioms LiteralDL.historySum_mono
#print axioms LiteralDL.historySum_node_infinite
#print axioms LiteralDL.LeafExpansion
#print axioms LiteralDL.LeafExpansion.global_le
#print axioms LiteralDL.LeafExpansion.strict_value
#print axioms LiteralDL.LeafExpansion.rho_lt
#print axioms LiteralDL.skHeight
#print axioms LiteralDL.cutWeight
#print axioms LiteralDL.cutTotal
#print axioms LiteralDL.cutWeight_fork
#print axioms LiteralDL.cutTotal_succ
#print axioms LiteralDL.cutTotal_zero
#print axioms LiteralDL.cutTotal_bound
#print axioms LiteralDL.total_le_of_prefixed
#print axioms LiteralDL.Species
#print axioms LiteralDL.weight
#print axioms LiteralDL.weight_pos
#print axioms LiteralDL.Hist
#print axioms LiteralDL.size
#print axioms LiteralDL.size_pos
#print axioms LiteralDL.depth
#print axioms LiteralDL.depth_bound
#print axioms LiteralDL.pool
#print axioms LiteralDL.mem_pool
#print axioms LiteralDL.Fiber
#print axioms LiteralDL.count
#print axioms LiteralDL.duplicate
#print axioms LiteralDL.duplicate_injective
#print axioms LiteralDL.supermultiplicative
#print axioms LiteralDL.fiber_zero_empty
#print axioms LiteralDL.one
#print axioms LiteralDL.positiveFiber
#print axioms LiteralDL.count_pos
#print axioms LiteralDL.conjugate_input_nonneg
#print axioms LiteralDL.conjugate_input_lt
#print axioms LiteralDL.logConjugate_continuousOn
#print axioms LiteralDL.logConjugate_strictConvex
#print axioms LiteralDL.logConjugate_zero
#print axioms LiteralDL.conjugate_branch_interior
#print axioms LiteralDL.logConjugate_minus_id_strictMono
#print axioms LiteralDL.logConjugate_expansive
#print axioms LiteralDL.negativeLogCount
#print axioms LiteralDL.count_cast_pos
#print axioms LiteralDL.negativeLogCount_subadditive
#print axioms LiteralDL.negativeLogCount_bddBelow
#print axioms LiteralDL.negativeLogCount_tendsto
#print axioms LiteralDL.mergeValue_associator
#print axioms LiteralDL.catalanBranch
#print axioms LiteralDL.catalanBranch_properties
#print axioms LiteralDL.total_principal
#print axioms LiteralDL.total_infinite_above
#print axioms LiteralDL.ShapeIso.refl
#print axioms LiteralDL.ShapeIso.symm
#print axioms LiteralDL.ShapeIso.trans
#print axioms LiteralDL.count_node_congr
#print axioms LiteralDL.ShapeIso.count_eq
#print axioms LiteralDL.ShapeIso.leaves_eq
#print axioms LiteralDL.ShapeIso.rho_eq
#print axioms LiteralDL.extantCount
#print axioms LiteralDL.encode_size
#print axioms LiteralDL.sourceFiberEquiv
#print axioms LiteralDL.swapRoot
#print axioms LiteralDL.swapRoot_size
#print axioms LiteralDL.swapRoot_twice
#print axioms LiteralDL.swapFiber
#print axioms LiteralDL.count_swap
#print axioms LiteralDL.count_zero
#print axioms LiteralDL.Event
#print axioms LiteralDL.EventTree
#print axioms LiteralDL.encode
#print axioms LiteralDL.Valid
#print axioms LiteralDL.encode_valid
#print axioms LiteralDL.valid_has_history
#print axioms LiteralDL.encode_ne_loss
#print axioms LiteralDL.encode_injective
#print axioms LiteralDL.sourceEquiv
#print axioms LiteralDL.sizeEquiv
#print axioms LiteralDL.historySum_coeff
#print axioms LiteralDL.historySum_le_of_atom_prefixed
#print axioms LiteralDL.leaves
#print axioms LiteralDL.leaves_pos
#print axioms LiteralDL.caterpillar
#print axioms LiteralDL.balanced
#print axioms LiteralDL.leaves_caterpillar
#print axioms LiteralDL.leaves_balanced
#print axioms LiteralDL.ShapeIso
#print axioms LiteralDL.leaves_ge_two_of_nonleaf
#print axioms LiteralDL.caterpillar_dichotomy
#print axioms LiteralDL.rho_caterpillar_strict
#print axioms LiteralDL.historySum_node_quadratic
#print axioms LiteralDL.rho_node_lt_left
#print axioms LiteralDL.ShapeIso.branch_eq
#print axioms LiteralDL.node_input_le_quarter
#print axioms LiteralDL.strict_leaf_extension
#print axioms LiteralDL.mergeValue_input_lt
#print axioms LiteralDL.mergeValue_strict
#print axioms LiteralDL.mergeValue_associator_lt
#print axioms LiteralDL.branch_node_gt_left
#print axioms LiteralDL.branch_nonleaf_gt_leaf
#print axioms LiteralDL.rho_rotation_le
#print axioms LiteralDL.rho_rotation_lt
#print axioms LiteralDL.rho
#print axioms LiteralDL.rho_pos
#print axioms LiteralDL.historySum_at_rho
#print axioms LiteralDL.historySum_finite_iff
#print axioms LiteralDL.count_exponential_bound
#print axioms LiteralDL.growth_mul_rho_le
#print axioms LiteralDL.growth_mul_rho_ge
#print axioms LiteralDL.growth_eq_inv_rho
#print axioms LiteralDL.rho_eq_of_historySum_eq
#print axioms LiteralDL.rho_swap
#print axioms LiteralDL.rho_node_lt_right
#print axioms LiteralDL.rootEquiv
#print axioms LiteralDL.skWeight
#print axioms LiteralDL.total
#print axioms LiteralDL.total_quadratic
#print axioms LiteralDL.historySum
#print axioms LiteralDL.skWeight_pow
#print axioms LiteralDL.historySum_skeleton
#print axioms LiteralDL.GrowthStage.growth_shapeIso
#print axioms LiteralDL.GrowthStage.balanced_shape_growth
#print axioms LiteralDL.GrowthStage.caterpillar_family_superlinear
```
<!-- END SOURCE -->

### BalancedFinalValues

<!-- SOURCE {"module": "BalancedFinalValues", "bytes": 2880, "sha256": "561f7ad0145ed7b55edef305989ca31cdeae0cea597cba01440b1aa139d1fa5b"} -->
```lean
import BalancedFinalSplit
namespace LiteralDL.BalancedStage
open LiteralDL

noncomputable def logValue (s : Species) (z : ℝ) := Real.log (1+branchValue s z)

theorem logValue_nonneg (s : Species) {z : ℝ} (hz : 0 ≤ z) : 0 ≤ logValue s z :=
  Real.log_nonneg (by linarith [(branchValue_global_bounds s hz).1])

theorem logValue_pos (s : Species) {z : ℝ} (hz : 0 < z) (hr : z ≤ rho s) :
    0 < logValue s z := Real.log_pos (by linarith [branchValue_pos hz hr])

theorem exp_logValue (s : Species) {z : ℝ} (hz : 0 ≤ z) :
    Real.exp (logValue s z) = 1+branchValue s z :=
  Real.exp_log (by linarith [(branchValue_global_bounds s hz).1])

theorem exp_log_pair (a b : Species) {z : ℝ} (hz : 0 ≤ z) :
    Real.exp (logValue a z+logValue b z)-1 =
      branchValue a z+branchValue b z+branchValue a z*branchValue b z := by
  rw [Real.exp_add,exp_logValue a hz,exp_logValue b hz]
  ring

theorem logValue_node (a b : Species) {z : ℝ} (hz : 0 ≤ z) :
    logValue (.node a b) z = logConjugate (logValue a z+logValue b z) := by
  unfold logConjugate
  rw [exp_log_pair a b hz]
  rfl

theorem logValue_input_mem (a b : Species) {z : ℝ} (hz : 0 ≤ z)
    (hr : z ≤ rho (.node a b)) :
    logValue a z+logValue b z ∈ Set.Icc 0 (Real.log (5/4)) := by
  refine ⟨add_nonneg (logValue_nonneg a hz) (logValue_nonneg b hz),?_⟩
  have he := exp_log_pair a b hz
  have hq := node_input_le_quarter a b hz hr
  apply Real.exp_le_exp.mp
  rw [Real.exp_log (by norm_num : (0:ℝ)<5/4)]
  linarith

theorem balanced_radius_antitone {i K : Nat} (hi : 1 ≤ i) (hik : i ≤ K) :
    rho (balanced K) ≤ rho (balanced i) := by
  induction K, hik using Nat.le_induction with
  | base => exact le_rfl
  | succ K hK ih =>
    exact (rho_balanced_successor_lt (by omega : 0 < K)).le.trans ih

theorem balanced_log_discrete {K : Nat} (hK : 1 ≤ K) {z : ℝ} (hz : 0 < z)
    (hr : z ≤ rho (balanced K)) :
    ∀ n, 2 ≤ n → n+1 ≤ K →
      2*logValue (balanced n) z < logValue (balanced (n-1)) z+logValue (balanced (n+1)) z := by
  apply discrete_convex (fun n => logValue (balanced n) z) K
  · exact logValue_pos _ hz (hr.trans (balanced_radius_antitone (by omega) (by omega)))
  · intro i hi hiK
    have he := (balanced_successor_expansion (by omega : 0 < i)).strict_value hz
      (hr.trans (balanced_radius_antitone (by omega) hiK))
    exact Real.log_lt_log (by linarith [(branchValue_global_bounds (balanced i) hz.le).1])
      (by linarith : 1+branchValue (balanced i) z < 1+branchValue (balanced (i+1)) z)
  · intro i hi hiK
    have h := logValue_input_mem (balanced (i/2)) (balanced ((i+1)/2)) hz.le
    have he := balanced_node hi
    rw [← he] at h
    exact h (hr.trans (balanced_radius_antitone (by omega) hiK))
  · intro i hi hiK
    rw [balanced_node hi,logValue_node _ _ hz.le]

#print axioms balanced_log_discrete
end LiteralDL.BalancedStage
```
<!-- END SOURCE -->

### BalancedFinalOrder

<!-- SOURCE {"module": "BalancedFinalOrder", "bytes": 4008, "sha256": "21a68d1ef7f945daaac46e0d9650b496c765bd5d64c6b5ccaa9797d823fb3010"} -->
```lean
import BalancedFinalValues
namespace LiteralDL.BalancedStage
open LiteralDL

theorem conjugate_le {x y : ℝ}
    (hx : x ∈ Set.Icc 0 (Real.log (5/4)))
    (hy : y ∈ Set.Icc 0 (Real.log (5/4))) (hxy : x ≤ y) :
    logConjugate x ≤ logConjugate y := by
  rcases lt_or_eq_of_le hxy with h|h
  · have he := logConjugate_expansive hx hy h
    linarith
  · rw [h]

theorem conjugate_eq_iff {x y : ℝ}
    (hx : x ∈ Set.Icc 0 (Real.log (5/4)))
    (hy : y ∈ Set.Icc 0 (Real.log (5/4))) (hxy : x ≤ y) :
    logConjugate x = logConjugate y ↔ x=y := by
  constructor
  · intro he
    by_contra hn
    have hh := logConjugate_expansive hx hy (lt_of_le_of_ne hxy hn)
    linarith
  · rintro rfl; rfl

theorem log_minimum (K : Nat) (hK : 1 ≤ K) {z : ℝ} (hz : 0 < z)
    (hr : z ≤ rho (balanced K)) (s : Species) (hs : leaves s ≤ K)
    (hrs : z ≤ rho s) :
    logValue (balanced (leaves s)) z ≤ logValue s z ∧
    (logValue (balanced (leaves s)) z = logValue s z ↔ ShapeIso s (balanced (leaves s))) := by
  induction s with
  | leaf => simp only [leaves,balanced]; exact ⟨le_rfl,⟨fun _ => .leaf,fun _ => trivial⟩⟩
  | node a b ia ib =>
    have ha := leaves_pos a
    have hb := leaves_pos b
    have hsa : leaves a ≤ K := by simp only [leaves] at hs; omega
    have hsb : leaves b ≤ K := by simp only [leaves] at hs; omega
    have hra := hrs.trans (rho_node_lt_left a b).le
    have hrb := hrs.trans (rho_node_lt_right a b).le
    obtain ⟨ha_le,ha_eq⟩ := ia hsa hra
    obtain ⟨hb_le,hb_eq⟩ := ib hsb hrb
    have htotal : leaves a+leaves b ≤ K := hs
    have htwo : 2 ≤ leaves a+leaves b := by omega
    have hsplit := split_min (fun n => logValue (balanced n) z) K
      (balanced_log_discrete hK hz hr) (by omega : 1 ≤ leaves a) (by omega : 1 ≤ leaves b) htotal
    have hleft := logValue_input_mem (balanced ((leaves a+leaves b)/2))
      (balanced ((leaves a+leaves b+1)/2)) hz.le
    have hbal := balanced_node htwo
    rw [← hbal] at hleft
    have hleft' := hleft (hr.trans (balanced_radius_antitone (by omega) htotal))
    have hright := logValue_input_mem a b hz.le hrs
    have hsum : logValue (balanced ((leaves a+leaves b)/2)) z +
        logValue (balanced ((leaves a+leaves b+1)/2)) z ≤ logValue a z+logValue b z := by
      linarith [hsplit.1]
    have hle := conjugate_le hleft' hright hsum
    have heq := conjugate_eq_iff hleft' hright hsum
    have hroot : logValue (balanced (leaves (.node a b))) z =
        logConjugate (logValue (balanced ((leaves a+leaves b)/2)) z+
          logValue (balanced ((leaves a+leaves b+1)/2)) z) := by
      rw [leaves,balanced_node htwo,logValue_node _ _ hz.le]
    rw [hroot,logValue_node a b hz.le]
    refine ⟨hle,⟨?_,?_⟩⟩
    · intro he
      have hin := heq.mp he
      have hae : logValue (balanced (leaves a)) z = logValue a z := by linarith [hsplit.1]
      have hbe : logValue (balanced (leaves b)) z = logValue b z := by linarith [hsplit.1]
      have hse : logValue (balanced ((leaves a+leaves b)/2)) z+
          logValue (balanced ((leaves a+leaves b+1)/2)) z =
          logValue (balanced (leaves a)) z+logValue (balanced (leaves b)) z := by linarith
      obtain ⟨hab,hba⟩ := hsplit.2.mp hse
      have hai := ha_eq.mp hae
      have hbi := hb_eq.mp hbe
      simp only [leaves]
      rw [balanced_node htwo]
      rcases le_total (leaves a) (leaves b) with h|h
      · have e0 : (leaves a+leaves b)/2=leaves a := by omega
        have e1 : (leaves a+leaves b+1)/2=leaves b := by omega
        rw [e0,e1]
        exact .node hai hbi
      · have e0 : (leaves a+leaves b)/2=leaves b := by omega
        have e1 : (leaves a+leaves b+1)/2=leaves a := by omega
        rw [e0,e1]
        exact .swap hai hbi
    · intro hi
      have he : logValue (balanced (leaves (.node a b))) z = logValue (.node a b) z := by
        unfold logValue
        rw [hi.branch_eq]
      rwa [hroot,logValue_node a b hz.le] at he

#print axioms log_minimum
end LiteralDL.BalancedStage
```
<!-- END SOURCE -->

### BalancedFinalExtremum

<!-- SOURCE {"module": "BalancedFinalExtremum", "bytes": 4070, "sha256": "02922a6c2a12abfefa648688eec377443533efd42dd45ddc25d0f7163105f9b6"} -->
```lean
import BalancedFinalOrder
import CaterpillarCounts
namespace LiteralDL.BalancedStage
open LiteralDL

theorem rho_balanced_strict (s : Species)
    (hi : ¬ ShapeIso s (balanced (leaves s))) :
    rho s < rho (balanced (leaves s)) := by
  by_contra hn
  have hr : rho (balanced (leaves s)) ≤ rho s := le_of_not_gt hn
  have h := log_minimum (leaves s) (leaves_pos s) (rho_pos (balanced (leaves s)))
    le_rfl s le_rfl hr
  have hlt : logValue (balanced (leaves s)) (rho (balanced (leaves s))) <
      logValue s (rho (balanced (leaves s))) := lt_of_le_of_ne h.1 (fun he => hi (h.2.mp he))
  have he : branchValue (balanced (leaves s)) (rho (balanced (leaves s))) = 1/2 :=
    (actualThreshold (balanced (leaves s))).endpoint
  have hs := (branchValue_global_bounds s ((rho_pos (balanced (leaves s))).le)).2
  have hh : logValue s (rho (balanced (leaves s))) ≤
      logValue (balanced (leaves s)) (rho (balanced (leaves s))) := by
    unfold logValue
    rw [he]
    apply Real.log_le_log (by linarith [(branchValue_global_bounds s ((rho_pos (balanced (leaves s))).le)).1])
    linarith
  exact (not_lt_of_ge hh) hlt

theorem rho_balanced_le (s : Species) : rho s ≤ rho (balanced (leaves s)) := by
  by_cases hi : ShapeIso s (balanced (leaves s))
  · exact hi.rho_eq.le
  · exact (rho_balanced_strict s hi).le

theorem rho_balanced_eq_iff (s : Species) :
    rho s = rho (balanced (leaves s)) ↔ ShapeIso s (balanced (leaves s)) := by
  constructor
  · intro he
    by_contra hi
    exact ne_of_lt (rho_balanced_strict s hi) he
  · exact ShapeIso.rho_eq

theorem eventual_balanced_minimum (k : Nat) : ∃ N : Nat, 1 ≤ N ∧
    ∀ s : Species, leaves s = k → ∀ n : Nat, N ≤ n →
      count (balanced k) n ≤ count s n ∧
      (count (balanced k) n = count s n ↔ ShapeIso s (balanced k)) := by
  have hall : ∀ s : {s : Species // leaves s = k}, ∀ᶠ n : Nat in Filter.atTop,
      count (balanced k) n ≤ count s.1 n ∧
      (count (balanced k) n = count s.1 n ↔ ShapeIso s.1 (balanced k)) := by
    intro s
    by_cases hi : ShapeIso s.1 (balanced k)
    · exact Filter.Eventually.of_forall (fun n => ⟨(hi.count_eq n).symm.le,
        ⟨fun _ => hi,fun _ => (hi.count_eq n).symm⟩⟩)
    · have hr : rho s.1 < rho (balanced k) := by
        have h := rho_balanced_strict s.1
        rw [s.2] at h
        exact h hi
      filter_upwards [eventual_count_lt_of_rho_lt (balanced k) s.1 hr] with n hn
      exact ⟨hn.le,⟨fun he => (ne_of_lt hn he).elim,fun hh => (hi hh).elim⟩⟩
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp (Filter.eventually_all.mpr hall)
  refine ⟨max 1 N,le_max_left _ _,?_⟩
  intro s hs n hn
  exact hN n ((le_max_right _ _).trans hn) ⟨s,hs⟩

/-- Expanded assigned component, with a cutoff chosen for each fixed positive leaf count. -/
theorem balanced_component :
    (∀ k : Nat, 0 < k → ∀ s : Species, leaves s = k →
      rho s ≤ rho (balanced k) ∧
      (rho s = rho (balanced k) ↔ ShapeIso s (balanced k)) ∧
      (¬ ShapeIso s (balanced k) → rho s < rho (balanced k))) ∧
    (∀ k : Nat, 0 < k → ∃ N : Nat, 1 ≤ N ∧
      ∀ s : Species, leaves s = k → ∀ n : Nat, N ≤ n →
        count (balanced k) n ≤ count s n ∧
        (count (balanced k) n = count s n ↔ ShapeIso s (balanced k)) ∧
        (count (balanced k) n < count s n ↔ ¬ ShapeIso s (balanced k))) := by
  constructor
  · intro k hk s hs
    have hw := rho_balanced_le s
    have he := rho_balanced_eq_iff s
    have ht := rho_balanced_strict s
    rw [hs] at hw he ht
    exact ⟨hw,he,ht⟩
  · intro k hk
    obtain ⟨N,hN,hh⟩ := eventual_balanced_minimum k
    refine ⟨N,hN,?_⟩
    intro s hs n hn
    obtain ⟨hw,he⟩ := hh s hs n hn
    exact ⟨hw,he,⟨fun ht hi => ne_of_lt ht (he.mpr hi),
      fun hi => lt_of_le_of_ne hw (fun h => hi (he.mp h))⟩⟩

#print axioms rho_balanced_strict
#print axioms rho_balanced_le
#print axioms rho_balanced_eq_iff
#print axioms eventual_balanced_minimum
#print axioms balanced_component
end LiteralDL.BalancedStage
```
<!-- END SOURCE -->

### BalancedFinalAudit

<!-- SOURCE {"module": "BalancedFinalAudit", "bytes": 11079, "sha256": "18f1016ece5fb51028d8450c0d1574c875b512bfa363562ad9ce8cad374a5d35"} -->
```lean
import LiteralHistory
import SourceHistory
import SourceFiber
import CardinalRecurrence
import DuplicationSkeleton
import WeightedSkeleton
import LeastFixedPoint
import SourceWeighted
import EndpointAudit
import AtomMass
import ScalarBranch
import ScalarEvaluation
import HistoryEvaluation
import BranchRegularity
import HistoryOrder
import ActualThreshold
import ThresholdFacts
import LogFekete
import ActualRootLimit
import GeometricBridge
import ThresholdIdentity
import SpeciesShapes
import FiniteShapes
import StrictChildThreshold
import ThresholdUniqueness
import ClosureAudit
import ShapeTransport
import CatalanAssociator
import BranchDomain
import ClippedCatalan
import RealAssociator
import BranchGlobal
import CaterpillarOrder
import StrictRotation
import StrictMerge
import CaterpillarSplit
import StrictExtension
import StrictCaterpillar
import CatalanDerivative
import ConjugateSlope
import LogConjugateConvex
import CaterpillarCounts
import LeafExpansion
import BalancedExpansion
import LogConjugateExpansive
import ProgressAudit
import BalancedFinalDiscrete
import BalancedFinalSplit
import BalancedFinalValues
import BalancedFinalOrder
import BalancedFinalExtremum

#print axioms LiteralDL.Species
#print axioms LiteralDL.weight
#print axioms LiteralDL.weight_pos
#print axioms LiteralDL.Hist
#print axioms LiteralDL.size
#print axioms LiteralDL.size_pos
#print axioms LiteralDL.depth
#print axioms LiteralDL.depth_bound
#print axioms LiteralDL.pool
#print axioms LiteralDL.mem_pool
#print axioms LiteralDL.Fiber
#print axioms LiteralDL.count
#print axioms LiteralDL.duplicate
#print axioms LiteralDL.duplicate_injective
#print axioms LiteralDL.supermultiplicative
#print axioms LiteralDL.fiber_zero_empty
#print axioms LiteralDL.one
#print axioms LiteralDL.positiveFiber
#print axioms LiteralDL.count_pos
#print axioms LiteralDL.Event
#print axioms LiteralDL.EventTree
#print axioms LiteralDL.encode
#print axioms LiteralDL.Valid
#print axioms LiteralDL.encode_valid
#print axioms LiteralDL.valid_has_history
#print axioms LiteralDL.encode_ne_loss
#print axioms LiteralDL.encode_injective
#print axioms LiteralDL.sourceEquiv
#print axioms LiteralDL.extantCount
#print axioms LiteralDL.encode_size
#print axioms LiteralDL.sourceFiberEquiv
#print axioms LiteralDL.swapRoot
#print axioms LiteralDL.swapRoot_size
#print axioms LiteralDL.swapRoot_twice
#print axioms LiteralDL.swapFiber
#print axioms LiteralDL.count_swap
#print axioms LiteralDL.count_zero
#print axioms LiteralDL.PairFiber
#print axioms LiteralDL.Split
#print axioms LiteralDL.splitEquiv
#print axioms LiteralDL.pairCount
#print axioms LiteralDL.NodeRoot
#print axioms LiteralDL.nodeJoin
#print axioms LiteralDL.nodeCut
#print axioms LiteralDL.nodeEquiv
#print axioms LiteralDL.count_node
#print axioms LiteralDL.pairCount_eq
#print axioms LiteralDL.LeafRoot
#print axioms LiteralDL.leafJoin
#print axioms LiteralDL.leafCut
#print axioms LiteralDL.leafEquiv
#print axioms LiteralDL.count_leaf
#print axioms LiteralDL.count_node_convolution
#print axioms LiteralDL.Skeleton
#print axioms LiteralDL.Atom
#print axioms LiteralDL.atomHist
#print axioms LiteralDL.assemble
#print axioms LiteralDL.cutSkeleton
#print axioms LiteralDL.assemble_cut
#print axioms LiteralDL.cut_assemble
#print axioms LiteralDL.skeletonEquiv
#print axioms LiteralDL.skeletonSize
#print axioms LiteralDL.assemble_size
#print axioms LiteralDL.rootEquiv
#print axioms LiteralDL.skWeight
#print axioms LiteralDL.total
#print axioms LiteralDL.total_quadratic
#print axioms LiteralDL.historySum
#print axioms LiteralDL.skWeight_pow
#print axioms LiteralDL.historySum_skeleton
#print axioms LiteralDL.skHeight
#print axioms LiteralDL.cutWeight
#print axioms LiteralDL.cutTotal
#print axioms LiteralDL.cutWeight_fork
#print axioms LiteralDL.cutTotal_succ
#print axioms LiteralDL.cutTotal_zero
#print axioms LiteralDL.cutTotal_bound
#print axioms LiteralDL.total_le_of_prefixed
#print axioms LiteralDL.sizeEquiv
#print axioms LiteralDL.historySum_coeff
#print axioms LiteralDL.historySum_le_of_atom_prefixed
#print axioms LiteralDL.atomNodeEquiv
#print axioms LiteralDL.atomMass_node
#print axioms LiteralDL.total_eq_of_mass_eq
#print axioms LiteralDL.catalanBranch
#print axioms LiteralDL.catalanBranch_properties
#print axioms LiteralDL.total_principal
#print axioms LiteralDL.total_infinite_above
#print axioms LiteralDL.atomMass_leaf
#print axioms LiteralDL.historySum_leaf_principal
#print axioms LiteralDL.historySum_leaf_infinite
#print axioms LiteralDL.historySum_node_principal
#print axioms LiteralDL.branchValue
#print axioms LiteralDL.continuous_catalanBranch
#print axioms LiteralDL.branchValue_continuous
#print axioms LiteralDL.catalanBranch_zero
#print axioms LiteralDL.catalanBranch_quarter
#print axioms LiteralDL.branchValue_zero
#print axioms LiteralDL.catalanBranch_strictMono
#print axioms LiteralDL.mass_le_total
#print axioms LiteralDL.historySum_node_ge_left
#print axioms LiteralDL.historySum_node_ge_right
#print axioms LiteralDL.historySum_mono
#print axioms LiteralDL.historySum_node_infinite
#print axioms LiteralDL.ActualThreshold
#print axioms LiteralDL.leafThreshold
#print axioms LiteralDL.nodeThreshold
#print axioms LiteralDL.actualThreshold
#print axioms LiteralDL.rho
#print axioms LiteralDL.rho_pos
#print axioms LiteralDL.historySum_at_rho
#print axioms LiteralDL.historySum_finite_iff
#print axioms LiteralDL.count_exponential_bound
#print axioms LiteralDL.negativeLogCount
#print axioms LiteralDL.count_cast_pos
#print axioms LiteralDL.negativeLogCount_subadditive
#print axioms LiteralDL.negativeLogCount_bddBelow
#print axioms LiteralDL.negativeLogCount_tendsto
#print axioms LiteralDL.growth
#print axioms LiteralDL.growth_pos
#print axioms LiteralDL.actual_root_limit
#print axioms LiteralDL.count_le_growth_pow
#print axioms LiteralDL.finite_below_growth
#print axioms LiteralDL.growth_mul_rho_le
#print axioms LiteralDL.growth_mul_rho_ge
#print axioms LiteralDL.growth_eq_inv_rho
#print axioms LiteralDL.leaves
#print axioms LiteralDL.leaves_pos
#print axioms LiteralDL.caterpillar
#print axioms LiteralDL.balanced
#print axioms LiteralDL.leaves_caterpillar
#print axioms LiteralDL.leaves_balanced
#print axioms LiteralDL.ShapeIso
#print axioms LiteralDL.speciesPool
#print axioms LiteralDL.mem_speciesPool
#print axioms LiteralDL.historySum_node_quadratic
#print axioms LiteralDL.rho_node_lt_left
#print axioms LiteralDL.rho_eq_of_historySum_eq
#print axioms LiteralDL.rho_swap
#print axioms LiteralDL.rho_node_lt_right
#print axioms LiteralDL.ShapeIso.refl
#print axioms LiteralDL.ShapeIso.symm
#print axioms LiteralDL.ShapeIso.trans
#print axioms LiteralDL.count_node_congr
#print axioms LiteralDL.ShapeIso.count_eq
#print axioms LiteralDL.ShapeIso.leaves_eq
#print axioms LiteralDL.ShapeIso.rho_eq
#print axioms LiteralDL.catalan_associator_identity
#print axioms LiteralDL.catalan_associator_strict
#print axioms LiteralDL.branchValue_nonneg
#print axioms LiteralDL.branchValue_pos
#print axioms LiteralDL.branchValue_lt_half
#print axioms LiteralDL.branch_node_quadratic
#print axioms LiteralDL.catalanBranch_global_bounds
#print axioms LiteralDL.catalanBranch_saturated
#print axioms LiteralDL.catalanBranch_mono
#print axioms LiteralDL.mergeValue
#print axioms LiteralDL.mergeValue_nonneg
#print axioms LiteralDL.mergeValue_half
#print axioms LiteralDL.mergeValue_mono
#print axioms LiteralDL.mergeValue_comm
#print axioms LiteralDL.mergeValue_ge_left
#print axioms LiteralDL.mergeValue_associator
#print axioms LiteralDL.branchValue_global_bounds
#print axioms LiteralDL.branchValue_ge_leaf
#print axioms LiteralDL.rho_le_of_global_branch_le
#print axioms LiteralDL.caterpillar_succ
#print axioms LiteralDL.caterpillar_merge_le
#print axioms LiteralDL.branchValue_le_caterpillar
#print axioms LiteralDL.rho_caterpillar_le
#print axioms LiteralDL.branch_node_gt_left
#print axioms LiteralDL.branch_nonleaf_gt_leaf
#print axioms LiteralDL.rho_rotation_le
#print axioms LiteralDL.rho_rotation_lt
#print axioms LiteralDL.mergeValue_input_lt
#print axioms LiteralDL.mergeValue_strict
#print axioms LiteralDL.mergeValue_associator_lt
#print axioms LiteralDL.caterpillar_ne_leaf
#print axioms LiteralDL.rho_caterpillar_split_lt
#print axioms LiteralDL.caterpillar_merge_lt
#print axioms LiteralDL.ShapeIso.branch_eq
#print axioms LiteralDL.node_input_le_quarter
#print axioms LiteralDL.strict_leaf_extension
#print axioms LiteralDL.leaves_ge_two_of_nonleaf
#print axioms LiteralDL.caterpillar_dichotomy
#print axioms LiteralDL.rho_caterpillar_strict
#print axioms LiteralDL.hasDerivAt_catalanBranch
#print axioms LiteralDL.logConjugate
#print axioms LiteralDL.hasDerivAt_logConjugate
#print axioms LiteralDL.conjugateSlope
#print axioms LiteralDL.conjugateSlope_den_pos
#print axioms LiteralDL.conjugateSlope_gt_one
#print axioms LiteralDL.conjugateSlope_strictMono
#print axioms LiteralDL.deriv_logConjugate
#print axioms LiteralDL.conjugate_input_nonneg
#print axioms LiteralDL.conjugate_input_lt
#print axioms LiteralDL.logConjugate_continuousOn
#print axioms LiteralDL.logConjugate_strictConvex
#print axioms LiteralDL.eventual_count_lt_of_growth_lt
#print axioms LiteralDL.eventual_count_lt_of_rho_lt
#print axioms LiteralDL.eventual_caterpillar_maximum
#print axioms LiteralDL.LeafExpansion
#print axioms LiteralDL.LeafExpansion.global_le
#print axioms LiteralDL.LeafExpansion.strict_value
#print axioms LiteralDL.LeafExpansion.rho_lt
#print axioms LiteralDL.balanced_node
#print axioms LiteralDL.balanced_successor_expansion
#print axioms LiteralDL.rho_balanced_successor_lt
#print axioms LiteralDL.logConjugate_zero
#print axioms LiteralDL.conjugate_branch_interior
#print axioms LiteralDL.logConjugate_minus_id_strictMono
#print axioms LiteralDL.logConjugate_expansive
#print axioms LiteralDL.BalancedStage.strict_midpoint
#print axioms LiteralDL.BalancedStage.discrete_convex
#print axioms LiteralDL.BalancedStage.delta_lt
#print axioms LiteralDL.BalancedStage.split_ordered
#print axioms LiteralDL.BalancedStage.split_min
#print axioms LiteralDL.BalancedStage.logValue
#print axioms LiteralDL.BalancedStage.logValue_nonneg
#print axioms LiteralDL.BalancedStage.logValue_pos
#print axioms LiteralDL.BalancedStage.exp_logValue
#print axioms LiteralDL.BalancedStage.exp_log_pair
#print axioms LiteralDL.BalancedStage.logValue_node
#print axioms LiteralDL.BalancedStage.logValue_input_mem
#print axioms LiteralDL.BalancedStage.balanced_radius_antitone
#print axioms LiteralDL.BalancedStage.balanced_log_discrete
#print axioms LiteralDL.BalancedStage.conjugate_le
#print axioms LiteralDL.BalancedStage.conjugate_eq_iff
#print axioms LiteralDL.BalancedStage.log_minimum
#print axioms LiteralDL.BalancedStage.rho_balanced_strict
#print axioms LiteralDL.BalancedStage.rho_balanced_le
#print axioms LiteralDL.BalancedStage.rho_balanced_eq_iff
#print axioms LiteralDL.BalancedStage.eventual_balanced_minimum
#print axioms LiteralDL.BalancedStage.balanced_component

#print axioms LiteralDL.fiberFintype
#print axioms LiteralDL.pairFintype
#print axioms LiteralDL.fixedLeavesFintype
```
<!-- END SOURCE -->

### FinalSourceTransport

<!-- SOURCE {"module": "FinalSourceTransport", "bytes": 1522, "sha256": "f362114a263c563e6a260c6fd7a04f6dcd0533054c74330a1d1a1af4e65fe4f4"} -->
```lean
import BalancedFinalExtremum
import GrowthFinalEndpoint
namespace LiteralDL.FinalStage
open LiteralDL Filter

def shapeSetoid : Setoid Species where
  r := ShapeIso
  iseqv := ⟨ShapeIso.refl, ShapeIso.symm, ShapeIso.trans⟩
abbrev Unranked := Quotient shapeSetoid
def shape (s : Species) : Unranked := Quotient.mk shapeSetoid s

theorem shape_eq_iff (s t : Species) : shape s = shape t ↔ ShapeIso s t :=
  ⟨fun h => @Quotient.exact Species shapeSetoid s t h,
   fun h => @Quotient.sound Species shapeSetoid s t h⟩

def unrankedLeaves : Unranked → Nat :=
  Quotient.lift leaves (fun _ _ (h : ShapeIso _ _) => h.leaves_eq)
def unrankedCount (q : Unranked) (n : Nat) : Nat :=
  Quotient.lift (fun s => count s n) (fun _ _ (h : ShapeIso _ _) => h.count_eq n) q
noncomputable def unrankedGrowth : Unranked → ℝ :=
  Quotient.lift growth (fun _ _ (h : ShapeIso _ _) => GrowthStage.growth_shapeIso h)
noncomputable def unrankedRho : Unranked → ℝ :=
  Quotient.lift rho (fun _ _ (h : ShapeIso _ _) => h.rho_eq)

noncomputable def sourceCard (s : Species) (n : Nat) : Nat :=
  Nat.card {t : EventTree // Valid s [] t ∧ extantCount t = n}
theorem sourceCard_eq (s : Species) (n : Nat) : sourceCard s n = count s n := by
  unfold sourceCard count
  rw [← Nat.card_congr (sourceFiberEquiv s n []), Nat.card_eq_fintype_card]

theorem sourceCard_shape {s t : Species} (h : ShapeIso s t) (n : Nat) :
    sourceCard s n = sourceCard t n := by
  rw [sourceCard_eq, sourceCard_eq, h.count_eq]
end LiteralDL.FinalStage
```
<!-- END SOURCE -->

### FinalAssembly

<!-- SOURCE {"module": "FinalAssembly", "bytes": 6144, "sha256": "a7cff8d930073705fcf766f77479935c1ff6501c588b53cb83bc6bc0bd16bf7f"} -->
```lean
import FinalSourceTransport
namespace LiteralDL.FinalStage
open LiteralDL Filter

theorem uniform_extrema (k : Nat) : ∃ N : Nat, 1 ≤ N ∧
    ∀ s : Species, leaves s = k → ∀ n : Nat, N ≤ n →
      count (balanced k) n ≤ count s n ∧ count s n ≤ count (caterpillar k) n ∧
      (count (balanced k) n = count s n ↔ ShapeIso s (balanced k)) ∧
      (count s n = count (caterpillar k) n ↔ ShapeIso s (caterpillar k)) := by
  obtain ⟨A,hA,ha⟩ := BalancedStage.eventual_balanced_minimum k
  obtain ⟨B,hB,hb⟩ := eventual_caterpillar_maximum k
  refine ⟨max A B, hA.trans (le_max_left _ _), ?_⟩
  intro s hs n hn
  obtain ⟨hl,he⟩ := ha s hs n ((le_max_left _ _).trans hn)
  obtain ⟨hu,hf⟩ := hb s hs n ((le_max_right _ _).trans hn)
  exact ⟨hl,hu,he,hf⟩

def SourceTarget : Prop :=
  (∀ k : Nat, 0 < k → ∃ N : Nat, 1 ≤ N ∧
    ∀ s : Species, leaves s = k → ∀ n : Nat, N ≤ n →
      count (balanced k) n ≤ count s n ∧ count s n ≤ count (caterpillar k) n ∧
      (count (balanced k) n = count s n ↔ ShapeIso s (balanced k)) ∧
      (count s n = count (caterpillar k) n ↔ ShapeIso s (caterpillar k))) ∧
  (∀ s : Species, 0 < growth s ∧
    Tendsto (fun n : Nat => (count s n : ℝ) ^ (1/(n:ℝ))) atTop (nhds (growth s)) ∧
    growth s = (rho s)⁻¹) ∧
  Tendsto (fun k : Nat => growth (caterpillar k)/(k:ℝ)) atTop atTop ∧
  (∀ k : Nat, 0 < k → 2*(k:ℝ) ≤ growth (balanced k) ∧
    growth (balanced k) ≤ 1000*(k:ℝ))

theorem source_target : SourceTarget := by
  refine ⟨fun k _ => uniform_extrema k, GrowthStage.source_growth_component.1,
    GrowthStage.caterpillar_superlinear, ?_⟩
  intro k hk
  have h := GrowthStage.source_growth_component.2.1 k hk
  exact ⟨h.2.2.1,h.2.2.2.1⟩

theorem unranked_extrema (k : Nat) : ∃ N : Nat, 1 ≤ N ∧
    ∀ q : Unranked, unrankedLeaves q = k → ∀ n : Nat, N ≤ n →
      unrankedCount (shape (balanced k)) n ≤ unrankedCount q n ∧
      unrankedCount q n ≤ unrankedCount (shape (caterpillar k)) n ∧
      (unrankedCount (shape (balanced k)) n = unrankedCount q n ↔
        q = shape (balanced k)) ∧
      (unrankedCount q n = unrankedCount (shape (caterpillar k)) n ↔
        q = shape (caterpillar k)) := by
  obtain ⟨N,hN,hh⟩ := uniform_extrema k
  refine ⟨N,hN,?_⟩
  intro q
  refine Quotient.inductionOn q ?_
  intro s hs n hn
  obtain ⟨hl,hu,he,hf⟩ := hh s hs n hn
  exact ⟨hl,hu,he.trans (shape_eq_iff s (balanced k)).symm,
    hf.trans (shape_eq_iff s (caterpillar k)).symm⟩

theorem unranked_root_limit (q : Unranked) : 0 < unrankedGrowth q ∧
    Tendsto (fun n : Nat => (unrankedCount q n : ℝ) ^ (1/(n:ℝ)))
      atTop (nhds (unrankedGrowth q)) ∧ unrankedGrowth q = (unrankedRho q)⁻¹ := by
  refine Quotient.inductionOn q ?_
  intro s
  exact GrowthStage.source_growth_component.1 s

theorem source_four_claims_expanded :
  (∀ k : Nat, 0 < k → ∃ N : Nat, 1 ≤ N ∧
    ∀ s : Species, leaves s = k → ∀ n : Nat, N ≤ n →
      count (balanced k) n ≤ count s n ∧ count s n ≤ count (caterpillar k) n ∧
      (count (balanced k) n = count s n ↔ ShapeIso s (balanced k)) ∧
      (count s n = count (caterpillar k) n ↔ ShapeIso s (caterpillar k))) ∧
  (∀ s : Species, 0 < growth s ∧
    Tendsto (fun n : Nat => (count s n : ℝ) ^ (1/(n:ℝ))) atTop (nhds (growth s)) ∧
    growth s = (rho s)⁻¹) ∧
  Tendsto (fun k : Nat => growth (caterpillar k)/(k:ℝ)) atTop atTop ∧
  (∀ k : Nat, 0 < k → 2*(k:ℝ) ≤ growth (balanced k) ∧
    growth (balanced k) ≤ 1000*(k:ℝ))
 := source_target

theorem source_event_four_claims_expanded :
  (∀ k : Nat, 0 < k → ∃ N : Nat, 1 ≤ N ∧
    ∀ s : Species, leaves s = k → ∀ n : Nat, N ≤ n →
      sourceCard (balanced k) n ≤ sourceCard s n ∧ sourceCard s n ≤ sourceCard (caterpillar k) n ∧
      (sourceCard (balanced k) n = sourceCard s n ↔ ShapeIso s (balanced k)) ∧
      (sourceCard s n = sourceCard (caterpillar k) n ↔ ShapeIso s (caterpillar k))) ∧
  (∀ s : Species, 0 < growth s ∧
    Tendsto (fun n : Nat => (sourceCard s n : ℝ) ^ (1/(n:ℝ))) atTop (nhds (growth s)) ∧
    growth s = (rho s)⁻¹) ∧
  Tendsto (fun k : Nat => growth (caterpillar k)/(k:ℝ)) atTop atTop ∧
  (∀ k : Nat, 0 < k → 2*(k:ℝ) ≤ growth (balanced k) ∧
    growth (balanced k) ≤ 1000*(k:ℝ))
 := by
  simpa only [sourceCard_eq] using source_four_claims_expanded

theorem balanced_family_linear (f : Nat → Species)
    (h : ∀ k, 0 < k → ShapeIso (f k) (balanced k)) :
    ∀ k, 0 < k → leaves (f k) = k ∧ 2*(k:ℝ) ≤ growth (f k) ∧
      growth (f k) ≤ 1000*(k:ℝ) := by
  intro k hk
  exact GrowthStage.balanced_shape_growth hk (h k hk)

theorem caterpillar_family_superlinear (f : Nat → Species)
    (h : ∀ k, ShapeIso (f k) (caterpillar k)) :
    Tendsto (fun k : Nat => growth (f k)/(k:ℝ)) atTop atTop :=
  GrowthStage.caterpillar_family_superlinear f h

theorem unranked_four_claims_expanded :
    (∀ k : Nat, 0 < k → ∃ N : Nat, 1 ≤ N ∧
      ∀ q : Unranked, unrankedLeaves q = k → ∀ n : Nat, N ≤ n →
        unrankedCount (shape (balanced k)) n ≤ unrankedCount q n ∧
        unrankedCount q n ≤ unrankedCount (shape (caterpillar k)) n ∧
        (unrankedCount (shape (balanced k)) n = unrankedCount q n ↔
          q = shape (balanced k)) ∧
        (unrankedCount q n = unrankedCount (shape (caterpillar k)) n ↔
          q = shape (caterpillar k))) ∧
    (∀ q : Unranked, 0 < unrankedGrowth q ∧
      Tendsto (fun n : Nat => (unrankedCount q n : ℝ) ^ (1/(n:ℝ)))
        atTop (nhds (unrankedGrowth q)) ∧ unrankedGrowth q = (unrankedRho q)⁻¹) ∧
    Tendsto (fun k : Nat => unrankedGrowth (shape (caterpillar k))/(k:ℝ))
      atTop atTop ∧
    (∀ k : Nat, 0 < k → 2*(k:ℝ) ≤ unrankedGrowth (shape (balanced k)) ∧
      unrankedGrowth (shape (balanced k)) ≤ 1000*(k:ℝ)) := by
  exact ⟨fun k _ => unranked_extrema k, unranked_root_limit,
    source_target.2.2.1, source_target.2.2.2⟩

end LiteralDL.FinalStage
```
<!-- END SOURCE -->

### FinalExpandedAudit

<!-- SOURCE {"module": "FinalExpandedAudit", "bytes": 11869, "sha256": "a047ccae1ddfb414834ee6332e87d802a248c34155dd59de53a5d0764b643891"} -->
```lean
import FinalAssembly
import BalancedFinalAudit
import GrowthFinalAudit
#print axioms LiteralDL.ActualThreshold
#print axioms LiteralDL.Atom
#print axioms LiteralDL.BalancedStage.balanced_component
#print axioms LiteralDL.BalancedStage.balanced_log_discrete
#print axioms LiteralDL.BalancedStage.balanced_radius_antitone
#print axioms LiteralDL.BalancedStage.conjugate_eq_iff
#print axioms LiteralDL.BalancedStage.conjugate_le
#print axioms LiteralDL.BalancedStage.delta_lt
#print axioms LiteralDL.BalancedStage.discrete_convex
#print axioms LiteralDL.BalancedStage.eventual_balanced_minimum
#print axioms LiteralDL.BalancedStage.exp_logValue
#print axioms LiteralDL.BalancedStage.exp_log_pair
#print axioms LiteralDL.BalancedStage.logValue
#print axioms LiteralDL.BalancedStage.logValue_input_mem
#print axioms LiteralDL.BalancedStage.logValue_node
#print axioms LiteralDL.BalancedStage.logValue_nonneg
#print axioms LiteralDL.BalancedStage.logValue_pos
#print axioms LiteralDL.BalancedStage.log_minimum
#print axioms LiteralDL.BalancedStage.rho_balanced_eq_iff
#print axioms LiteralDL.BalancedStage.rho_balanced_le
#print axioms LiteralDL.BalancedStage.rho_balanced_strict
#print axioms LiteralDL.BalancedStage.split_min
#print axioms LiteralDL.BalancedStage.split_ordered
#print axioms LiteralDL.BalancedStage.strict_midpoint
#print axioms LiteralDL.Event
#print axioms LiteralDL.EventTree
#print axioms LiteralDL.Fiber
#print axioms LiteralDL.FinalStage.SourceTarget
#print axioms LiteralDL.FinalStage.Unranked
#print axioms LiteralDL.FinalStage.balanced_family_linear
#print axioms LiteralDL.FinalStage.caterpillar_family_superlinear
#print axioms LiteralDL.FinalStage.shape
#print axioms LiteralDL.FinalStage.shapeSetoid
#print axioms LiteralDL.FinalStage.shape_eq_iff
#print axioms LiteralDL.FinalStage.sourceCard
#print axioms LiteralDL.FinalStage.sourceCard_eq
#print axioms LiteralDL.FinalStage.sourceCard_shape
#print axioms LiteralDL.FinalStage.source_event_four_claims_expanded
#print axioms LiteralDL.FinalStage.source_four_claims_expanded
#print axioms LiteralDL.FinalStage.source_target
#print axioms LiteralDL.FinalStage.uniform_extrema
#print axioms LiteralDL.FinalStage.unrankedCount
#print axioms LiteralDL.FinalStage.unrankedGrowth
#print axioms LiteralDL.FinalStage.unrankedLeaves
#print axioms LiteralDL.FinalStage.unrankedRho
#print axioms LiteralDL.FinalStage.unranked_extrema
#print axioms LiteralDL.FinalStage.unranked_root_limit
#print axioms LiteralDL.GrowthStage.auxiliary_conventions
#print axioms LiteralDL.GrowthStage.balanced_growth_upper
#print axioms LiteralDL.GrowthStage.balanced_shape_growth
#print axioms LiteralDL.GrowthStage.balanced_value_bound
#print axioms LiteralDL.GrowthStage.caterpillar_cubic
#print axioms LiteralDL.GrowthStage.caterpillar_family_superlinear
#print axioms LiteralDL.GrowthStage.caterpillar_square_lower
#print axioms LiteralDL.GrowthStage.caterpillar_superlinear
#print axioms LiteralDL.GrowthStage.growth_lower
#print axioms LiteralDL.GrowthStage.growth_shapeIso
#print axioms LiteralDL.GrowthStage.leaf_mass
#print axioms LiteralDL.GrowthStage.leaf_quadratic
#print axioms LiteralDL.GrowthStage.merge_bound
#print axioms LiteralDL.GrowthStage.source_growth_component
#print axioms LiteralDL.Hist
#print axioms LiteralDL.LeafExpansion
#print axioms LiteralDL.LeafExpansion.global_le
#print axioms LiteralDL.LeafExpansion.rho_lt
#print axioms LiteralDL.LeafExpansion.strict_value
#print axioms LiteralDL.LeafRoot
#print axioms LiteralDL.NodeRoot
#print axioms LiteralDL.PairFiber
#print axioms LiteralDL.ShapeIso
#print axioms LiteralDL.ShapeIso.branch_eq
#print axioms LiteralDL.ShapeIso.count_eq
#print axioms LiteralDL.ShapeIso.leaves_eq
#print axioms LiteralDL.ShapeIso.refl
#print axioms LiteralDL.ShapeIso.rho_eq
#print axioms LiteralDL.ShapeIso.symm
#print axioms LiteralDL.ShapeIso.trans
#print axioms LiteralDL.Skeleton
#print axioms LiteralDL.Species
#print axioms LiteralDL.Split
#print axioms LiteralDL.Valid
#print axioms LiteralDL.actualThreshold
#print axioms LiteralDL.actual_root_limit
#print axioms LiteralDL.assemble
#print axioms LiteralDL.assemble_cut
#print axioms LiteralDL.assemble_size
#print axioms LiteralDL.atomHist
#print axioms LiteralDL.atomMass_leaf
#print axioms LiteralDL.atomMass_node
#print axioms LiteralDL.atomNodeEquiv
#print axioms LiteralDL.balanced
#print axioms LiteralDL.balanced_node
#print axioms LiteralDL.balanced_successor_expansion
#print axioms LiteralDL.branchValue
#print axioms LiteralDL.branchValue_continuous
#print axioms LiteralDL.branchValue_ge_leaf
#print axioms LiteralDL.branchValue_global_bounds
#print axioms LiteralDL.branchValue_le_caterpillar
#print axioms LiteralDL.branchValue_lt_half
#print axioms LiteralDL.branchValue_nonneg
#print axioms LiteralDL.branchValue_pos
#print axioms LiteralDL.branchValue_zero
#print axioms LiteralDL.branch_node_gt_left
#print axioms LiteralDL.branch_node_quadratic
#print axioms LiteralDL.branch_nonleaf_gt_leaf
#print axioms LiteralDL.catalanBranch
#print axioms LiteralDL.catalanBranch_global_bounds
#print axioms LiteralDL.catalanBranch_mono
#print axioms LiteralDL.catalanBranch_properties
#print axioms LiteralDL.catalanBranch_quarter
#print axioms LiteralDL.catalanBranch_saturated
#print axioms LiteralDL.catalanBranch_strictMono
#print axioms LiteralDL.catalanBranch_zero
#print axioms LiteralDL.catalan_associator_identity
#print axioms LiteralDL.catalan_associator_strict
#print axioms LiteralDL.caterpillar
#print axioms LiteralDL.caterpillar_dichotomy
#print axioms LiteralDL.caterpillar_merge_le
#print axioms LiteralDL.caterpillar_merge_lt
#print axioms LiteralDL.caterpillar_ne_leaf
#print axioms LiteralDL.caterpillar_succ
#print axioms LiteralDL.conjugateSlope
#print axioms LiteralDL.conjugateSlope_den_pos
#print axioms LiteralDL.conjugateSlope_gt_one
#print axioms LiteralDL.conjugateSlope_strictMono
#print axioms LiteralDL.conjugate_branch_interior
#print axioms LiteralDL.conjugate_input_lt
#print axioms LiteralDL.conjugate_input_nonneg
#print axioms LiteralDL.continuous_catalanBranch
#print axioms LiteralDL.count
#print axioms LiteralDL.count_cast_pos
#print axioms LiteralDL.count_exponential_bound
#print axioms LiteralDL.count_le_growth_pow
#print axioms LiteralDL.count_leaf
#print axioms LiteralDL.count_node
#print axioms LiteralDL.count_node_congr
#print axioms LiteralDL.count_node_convolution
#print axioms LiteralDL.count_pos
#print axioms LiteralDL.count_swap
#print axioms LiteralDL.count_zero
#print axioms LiteralDL.cutSkeleton
#print axioms LiteralDL.cutTotal
#print axioms LiteralDL.cutTotal_bound
#print axioms LiteralDL.cutTotal_succ
#print axioms LiteralDL.cutTotal_zero
#print axioms LiteralDL.cutWeight
#print axioms LiteralDL.cutWeight_fork
#print axioms LiteralDL.cut_assemble
#print axioms LiteralDL.depth
#print axioms LiteralDL.depth_bound
#print axioms LiteralDL.deriv_logConjugate
#print axioms LiteralDL.duplicate
#print axioms LiteralDL.duplicate_injective
#print axioms LiteralDL.encode
#print axioms LiteralDL.encode_injective
#print axioms LiteralDL.encode_ne_loss
#print axioms LiteralDL.encode_size
#print axioms LiteralDL.encode_valid
#print axioms LiteralDL.eventual_caterpillar_maximum
#print axioms LiteralDL.eventual_count_lt_of_growth_lt
#print axioms LiteralDL.eventual_count_lt_of_rho_lt
#print axioms LiteralDL.extantCount
#print axioms LiteralDL.fiberFintype
#print axioms LiteralDL.fiber_zero_empty
#print axioms LiteralDL.finite_below_growth
#print axioms LiteralDL.fixedLeavesFintype
#print axioms LiteralDL.growth
#print axioms LiteralDL.growth_eq_inv_rho
#print axioms LiteralDL.growth_mul_rho_ge
#print axioms LiteralDL.growth_mul_rho_le
#print axioms LiteralDL.growth_pos
#print axioms LiteralDL.hasDerivAt_catalanBranch
#print axioms LiteralDL.hasDerivAt_logConjugate
#print axioms LiteralDL.historySum
#print axioms LiteralDL.historySum_at_rho
#print axioms LiteralDL.historySum_coeff
#print axioms LiteralDL.historySum_finite_iff
#print axioms LiteralDL.historySum_le_of_atom_prefixed
#print axioms LiteralDL.historySum_leaf_infinite
#print axioms LiteralDL.historySum_leaf_principal
#print axioms LiteralDL.historySum_mono
#print axioms LiteralDL.historySum_node_ge_left
#print axioms LiteralDL.historySum_node_ge_right
#print axioms LiteralDL.historySum_node_infinite
#print axioms LiteralDL.historySum_node_principal
#print axioms LiteralDL.historySum_node_quadratic
#print axioms LiteralDL.historySum_skeleton
#print axioms LiteralDL.leafCut
#print axioms LiteralDL.leafEquiv
#print axioms LiteralDL.leafJoin
#print axioms LiteralDL.leafThreshold
#print axioms LiteralDL.leaves
#print axioms LiteralDL.leaves_balanced
#print axioms LiteralDL.leaves_caterpillar
#print axioms LiteralDL.leaves_ge_two_of_nonleaf
#print axioms LiteralDL.leaves_pos
#print axioms LiteralDL.logConjugate
#print axioms LiteralDL.logConjugate_continuousOn
#print axioms LiteralDL.logConjugate_expansive
#print axioms LiteralDL.logConjugate_minus_id_strictMono
#print axioms LiteralDL.logConjugate_strictConvex
#print axioms LiteralDL.logConjugate_zero
#print axioms LiteralDL.mass_le_total
#print axioms LiteralDL.mem_pool
#print axioms LiteralDL.mem_speciesPool
#print axioms LiteralDL.mergeValue
#print axioms LiteralDL.mergeValue_associator
#print axioms LiteralDL.mergeValue_associator_lt
#print axioms LiteralDL.mergeValue_comm
#print axioms LiteralDL.mergeValue_ge_left
#print axioms LiteralDL.mergeValue_half
#print axioms LiteralDL.mergeValue_input_lt
#print axioms LiteralDL.mergeValue_mono
#print axioms LiteralDL.mergeValue_nonneg
#print axioms LiteralDL.mergeValue_strict
#print axioms LiteralDL.negativeLogCount
#print axioms LiteralDL.negativeLogCount_bddBelow
#print axioms LiteralDL.negativeLogCount_subadditive
#print axioms LiteralDL.negativeLogCount_tendsto
#print axioms LiteralDL.nodeCut
#print axioms LiteralDL.nodeEquiv
#print axioms LiteralDL.nodeJoin
#print axioms LiteralDL.nodeThreshold
#print axioms LiteralDL.node_input_le_quarter
#print axioms LiteralDL.one
#print axioms LiteralDL.pairCount
#print axioms LiteralDL.pairCount_eq
#print axioms LiteralDL.pairFintype
#print axioms LiteralDL.pool
#print axioms LiteralDL.positiveFiber
#print axioms LiteralDL.rho
#print axioms LiteralDL.rho_balanced_successor_lt
#print axioms LiteralDL.rho_caterpillar_le
#print axioms LiteralDL.rho_caterpillar_split_lt
#print axioms LiteralDL.rho_caterpillar_strict
#print axioms LiteralDL.rho_eq_of_historySum_eq
#print axioms LiteralDL.rho_le_of_global_branch_le
#print axioms LiteralDL.rho_node_lt_left
#print axioms LiteralDL.rho_node_lt_right
#print axioms LiteralDL.rho_pos
#print axioms LiteralDL.rho_rotation_le
#print axioms LiteralDL.rho_rotation_lt
#print axioms LiteralDL.rho_swap
#print axioms LiteralDL.rootEquiv
#print axioms LiteralDL.size
#print axioms LiteralDL.sizeEquiv
#print axioms LiteralDL.size_pos
#print axioms LiteralDL.skHeight
#print axioms LiteralDL.skWeight
#print axioms LiteralDL.skWeight_pow
#print axioms LiteralDL.skeletonEquiv
#print axioms LiteralDL.skeletonSize
#print axioms LiteralDL.sourceEquiv
#print axioms LiteralDL.sourceFiberEquiv
#print axioms LiteralDL.speciesPool
#print axioms LiteralDL.splitEquiv
#print axioms LiteralDL.strict_leaf_extension
#print axioms LiteralDL.supermultiplicative
#print axioms LiteralDL.swapFiber
#print axioms LiteralDL.swapRoot
#print axioms LiteralDL.swapRoot_size
#print axioms LiteralDL.swapRoot_twice
#print axioms LiteralDL.total
#print axioms LiteralDL.total_eq_of_mass_eq
#print axioms LiteralDL.total_infinite_above
#print axioms LiteralDL.total_le_of_prefixed
#print axioms LiteralDL.total_principal
#print axioms LiteralDL.total_quadratic
#print axioms LiteralDL.valid_has_history
#print axioms LiteralDL.weight
#print axioms LiteralDL.weight_pos
#print axioms LiteralDL.FinalStage.unranked_four_claims_expanded
#eval Lean.versionString
```
<!-- END SOURCE -->
