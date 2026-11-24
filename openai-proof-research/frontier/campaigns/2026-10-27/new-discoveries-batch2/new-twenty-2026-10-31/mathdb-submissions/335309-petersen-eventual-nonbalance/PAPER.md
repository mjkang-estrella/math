# The sharp eventual distance-balance threshold for generalized Petersen graphs

MathDB 335309, stage 4, 20 November 2026. **The packet reports successful compilation and independent kernel checking of 77 modules, in production and in a fresh appendix replay. The final reviewer did not compile Lean; root checks these receipts separately.**

We prove Miklavič–Šparl Conjecture 4.4 with its exact threshold and minimality, on the literal generalized Petersen graph with Bool×ZMod vertices and Mathlib graph distance. The Lean theorem `Petersen.miklavic_sparl_4_4 : Petersen.MiklavicSparl44` has no residual hypotheses and uses only propext, Classical.choice and Quot.sound. It proves connectivity and nonbalance at every positive subdiametral distance for every k≥2 and n>n_k, together with a nonvacuous balanced class at n=n_k for every k. The complete written argument is reproduced below. This is an internal research artifact, not a publication, acceptance decision or claim of completed novelty clearance.

## Source and definitions alongside Lean

Source: Štefko Miklavič and Primož Šparl, *ℓ-distance-balanced graphs*, arXiv:1702.05257v1 (17 February 2017), pp. 1–2 and 12, https://arxiv.org/pdf/1702.05257. The local PDF and extracted text supplied by the proof lane were read; no live-source or journal-version refresh was performed in this stage.

The source states: “Throughout this paper, all graphs are simple (without loops and multiple edges), undirected, finite and connected.” It defines

> For any pair of vertices u, v ∈ V(Γ) we let W_uv be the set of vertices of Γ that are closer to u than to v, that is
> W_uv = {w ∈ V(Γ) | d(u,w) < d(v,w)}.

> The pair u, v is said to be balanced if |W_uv| = |W_vu| and is non-balanced otherwise. Let ℓ denote a positive integer. A connected graph Γ of diameter at least ℓ is said to be ℓ-distance-balanced whenever any pair of vertices u, v ∈ V(Γ) at distance ℓ is balanced, that is, if for any u, v ∈ V(Γ) such that d(u,v) = ℓ we have |W_uv| = |W_vu|.

Adjacent Lean definitions (PetersenDefinitions.lean) are:

```lean
noncomputable def W {V : Type*} [Fintype V] (G : SimpleGraph V) (x y : V) : Finset V :=
  Finset.univ.filter (fun w => G.dist x w < G.dist y w)
def LDB {V : Type*} [Fintype V] (G : SimpleGraph V) (ell : ℕ) : Prop :=
  ∀ x y, G.dist x y = ell → (W G x y).card = (W G y x).card
```

`LDB` is the pair-count condition. The endpoint separately supplies connectivity and the positive subdiametral range, as required by the review, so no disconnected or out-of-range convention is silently used as the source's property.

The source's graph definition (1), p. 2:

> Let n ≥ 3 be a positive integer, and let 1 ≤ k < n/2. The generalized Petersen graph GP(n,k) is defined to have the following vertex set and edge set:
> V(GP(n,k)) = {u_i | i ∈ ℤ_n} ∪ {v_i | i ∈ ℤ_n},
> E(GP(n,k)) = {u_i u_(i+1) | i ∈ ℤ_n} ∪ {v_i v_(i+k) | i ∈ ℤ_n} ∪ {u_i v_i | i ∈ ℤ_n}.

The adjacent Lean definition uses `false` for u and `true` for v:

```lean
def GP (n k : ℕ) [NeZero n] : SimpleGraph (Bool × ZMod n) :=
  SimpleGraph.fromRel fun x y =>
    (x.1 = false ∧ y.1 = false ∧ y.2 = x.2 + 1) ∨
    (x.1 = true ∧ y.1 = true ∧ y.2 = x.2 + (k : ZMod n)) ∨
    (x.1 = false ∧ y.1 = true ∧ y.2 = x.2)
```

`fromRel` adds reverse orientations and deletes loops. `threshold_admissible` proves 3≤n and 2k<n whenever k≥2 and n≥n_k, so the parameters in the literal endpoint lie in the source's graph domain. `gp_connected` proves connectivity for every positive n, including all those parameters. For the source's identification of GP(5,2) as Petersen, `petersen_card`, `petersen_cubic`, and `petersen_diam` prove the requested 10-vertex, cubic, diameter-2 checks directly on this GP. No isomorphism to a second named Mathlib graph is claimed.

The conjecture as printed (arXiv p. 12; mathematical typography normalized, wording unchanged):

> **Conjecture 4.4** Let k ≥ 2 be an integer and let
> n_k = 11; k = 2,
> n_k = (k + 1)²; k odd,
> n_k = k(k + 2); k ≥ 4 even.
>
> Then for any n > n_k the graph GP(n,k) is not ℓ-distance-balanced for any 1 ≤ ℓ < D, where D is the diameter of GP(n,k). Moreover, n_k is the smallest integer with this property.

```lean
def nk (k : ℕ) : ℕ :=
  if k = 2 then 11 else if Odd k then (k+1)^2 else k*(k+2)
```

The full literal Lean endpoint `MiklavicSparl44` is printed in REPORT.md and in the source appendix. The third conjunct supplies a balanced subdiametral class at n_k. Any smaller eventual threshold would include n=n_k, so this is precisely the source's minimality assertion. The theorem `Petersen.miklavic_sparl_4_4` proves this proposition in the packet.

## Fully formalized metric theorem and proof

For x≥0 let x=qk+r, 0≤r<k, and put H(k,r)=min(r,k+1−r), L(k,x)=q+H(k,r). For a residue j, let

f(j)=min(L(k,j.val),L(k,n−j.val)),  p(j)=min(j.val,n−j.val).

Let t(j) be the infimum in ℕ∞ of |b| over all integers b satisfying kb=j in ℤ/n. Thus t(j)=∞ if that pure inner component does not contain j. This is `pure`/`t` in Lean; it is not the zero-valued disconnected graph-distance convention.

**Theorem (Petersen.distance_formula).** If k≥2 and n≥k(k+2), then for every i,j∈ℤ/n,

- d(u_i,v_j)=f(j−i)+1;
- d(u_i,u_j)=min(p(j−i),f(j−i)+2);
- d(v_i,v_j)=min(t(j−i),f(j−i)+2), with the finite result interpreted in ℕ.

**Proof.** First minimize the line cost |a|+|b| subject to a+kb=x. If b≤q, the inequalities |a|≥a and |b|≥b bound the cost below by q+r. If b≥q+1, use |a|≥−a and |b|≥b to obtain q+k+1−r. Both bounds dominate q+min(r,k+1−r). The two choices (a,b)=(r,q) and (r−k,q+1) attain the smaller bound. This is `line_lower` and `lineCost_min`.

For all x≥0, the two bounds on H give 2kL(k,x)≤2x+k(k+1). Use the nearer of j.val and n−j.val, whose doubled size is at most n. Since n≥k(k+2), this implies kf(j)<n (`lineCost_upper`, `f_short`). If y is any integer lift of j, divisibility gives y=j.val+cn. Either c=0, c=−1, or |y|≥n (`lift_split`). In the first two cases the line minimizer bounds any representation a+kb=y below by f(j). In the last case |a+kb|≤k(|a|+|b|), and kf(j)<n≤|y| rules out an improvement (`cost_lift_bound`, `cyclic_lower`). Negating the minimizing representation of n−j.val supplies the second candidate. Hence the minimum cyclic word length equals f (`word_eq_f`). The same lift split with generator 1 proves that the minimum pure outer length is p (`outer_min`, `pure_outer`).

For the graph bridge, record signed net outer steps a, signed net inner steps b, and a natural spoke count s on every walk. Their residue displacement is a+kb, and |a|+|b|+s is at most its length. The spoke parity equals the change of layers. With s=0, the unused layer's signed count is zero. Induction on the walk proves these assertions: an outer step changes a by ±1, an inner step changes b by ±1, and a spoke increases s by 1. The absolute-value triangle inequality controls length; the two layer values control parity. This is the signed-step invariant `walk_step_counts`, and is the chosen lower-bound method.

A mixed walk has odd s≥1, so its length is at least f+1. A same-layer walk either has s=0, giving its pure lower bound, or has even s≥2, giving f+2. Conversely, integer steps along a layer give explicit walks of length at most their absolute value (`layer_nat_walk`, `layer_walk`). Append outer and inner walks with one spoke for mixed endpoints, and with two spokes for nonpure same-layer endpoints. Pure walks give their own upper bounds. These constructions prove `dist_mixed_word` and `dist_same_word`. Substitution of `word_eq_f` and `pure_outer` gives the displayed theorem. All uses of ℕ∞ are bounded by the finite mixed-walk alternative before taking `toNat`. ∎

The elementary line bound here is a little weaker than the supplied proof's sharper rational estimate, but it suffices throughout n≥k(k+2), and it is formally proved for k=2 as well.

Further certified reductions: `threshold_quotient` is exactly q≥k+2 and r>k mod 2 when q=k+2. `diam_le_F_add_two` proves D≤F+2, where F=max_j f(j). The triangle inequality and symmetry of the variational word metric transfer to f. They imply that projection of every GP edge changes f by at most one. A unit-Lipschitz integer function attains every intermediate value along a walk; applying this to a walk from u_0 to an index attaining F proves `radius_attained`, and hence `subdiam_radius`. Thus every 1≤ℓ<D has an index j with f(j)=ℓ−1. No exact diameter formula was needed.

## Certified stage-2 counting mechanism

Write a(i)=min(p(i),f(i)+2), b(i)=min(t(i),f(i)+2), and c(i)=f(i)+1. `closerCount_eq` proves that the count closer to u_0 than v_j is exactly the sum of the cardinalities of {i : a(i)<c(i−j)} and {i : c(i)<b(i−j)}; it likewise identifies the reverse count. Replacing the two strict indicators by their sign difference and reindexing the second layer by i↦j−i proves `cancellation`. The reflection sending index t to i+j−t is a literal GP automorphism, so a finite bijection of the W sets proves `same_layer_balanced` without parameter restrictions beyond positive n.

For k≥3 and n≥k(k+2), `outer_shortcut_iff` says a(i)<f(i)+2 exactly when p(i)≤floor(k/2)+1, and `outer_shortcut_values` gives a(i)=p(i), f(i)=H(p(i)) there. The elementary estimate L(s)+2≤s outside this strip proves that there are no missing outer contributions. `outerCount_strip` proves the exact finite-sum replacement by integer lifts −m,…,m, m=floor(k/2)+1. The minimizing pure-outer lift proves surjectivity; width 2m<n proves injectivity.

For inner lower bounds it suffices to use an explicit pure walk: b(kz)≤|z|. The pulse is antitone in that left endpoint. When f(kz)=|z|, `innerPulse_route` bounds the actual pulse below by K(f(j−kz)−|z|). `innerCount_selected` proves that an injective selection of such vertices can be summed inside the actual cyclic count. The one even root or the two odd roots have total kernel weight two; roots on the opposite ray provide two more. `rootIndex_injective` proves both within-ray injection and ray disjointness from the single width inequality k(ceil(C/2)+ceil(C′/2))<n. `innerCount_four_blocks` checks all selected f-values from the two quotient/remainder blocks and proves I≥4. Its specialization `low_inner` gives f(ak)=a and I(ak)≥4 for every 2≤a≤floor((n/k)/2), throughout n≥k(k+2).

The arithmetic U tables are split into positive, negative and primary modules, with their six-term calculations preserved from the supplied proof lane and freshly checked. `localG_eq_g` proves that their piecewise function is the signed line metric on the required range; `g_nat` identifies it with the previously certified L. `fullU_eq_signedU`, `fullU_eq_U` and `fullU_primary_eq_U` prove that the full finite signed-line sum, including all small-h dummy terms, reduces to those six terms. The actual cyclic outer-count inequality is now certified by `outerCount_le_signedU`. It pairs the signed strip, separates its origin, computes each of the two line lifts, and bounds a pulse at their minimum by their sum. At f(j)≥2 the origin pulse vanishes. The two signed sums normalize to the checked U tables by `signedU_translate` and `signedU_eq_normU`.


## Certified generic strict imbalance

**Theorem (Petersen.generic_eventual_nonbalance).** For every k≥3, n>n_k and 3≤ℓ<diam GP(n,k), GP(n,k) is not ℓ-distance-balanced.

**Proof.** For low radii 2≤a≤floor(q/2), take j=ak. `low_inner` gives f(j)=a and innerCount≥4; the shared outer branch bound and the primary/positive U rows give outerCount≤3 (`witness_low`).

For high radii write a=floor(q/2)+s. `attained_cost_bound` applies to an arbitrary residue, splitting its remainder b at r. If b≤r, twice its radius is at most q+r. Otherwise it is at most q+k−r+1 and q−1+2 floor((k+1)/2); when r=0 the stronger q+k−1 bound also holds. These global bounds justify every branch of the five offset regimes in formula (13), as proved by `high_offset_exists`.

For those regimes `high_offset_data` verifies the exact minimum level, bounds both signed lift costs by 2 floor(q/2), checks both ceiling root depths, and proves the sum of their ceiling depths is strictly less than q. This last condition implies the modular injection width. `innerCount_four_lifts` proves the selected cross profiles using signed g translation, and forces four inner units. `high_offset_outer` applies the certified positive/negative U rows and the two odd near-threshold corner inequalities to bound the actual outer count by three. The common `central_witness` proves all graph and count assertions; `witness_high` discharges every premise from k≥3, n>n_k and the attained level.

Combining low and high cases gives `witness_middle`, and the literal cancellation identity makes the W-cardinality difference strictly negative (`middle_strict_imbalance`). Finally D≤F+2 and unit-step attainment give a residue with f=ℓ−1; since ℓ≥3, the middle witness applies. Its mixed graph distance is exactly ℓ, so the graph fails LDB at ℓ. ∎

All 41 stage-3 modules are preserved verbatim. The generic graph proof shares one outer-count argument and one signed-lift inner argument across all offset classes. Stage 4 also closes the small radii, k=2 and sharpness, as detailed next. References in the supplied argument to older `formal/K2Tables.lean` and `formal/FiniteCases.lean` identify the proof lane's exploratory certificates. This packet compiles the U2 source calculations with an adjusted import and replaces the old Fin(2n) finite certificates by fresh direct Bool×ZMod certificates.

## Stage-4 formal completion

The main declaration is `theorem Petersen.miklavic_sparl_4_4 : Petersen.MiklavicSparl44`. The exact proposition in `PetersenDefinitions.lean` remains unchanged. Its three clauses are supplied by `eventual_connected`, `eventual_nonbalance`, and the sharpness families. The latter exhibit ell=1 for even k, ell=D−1 for odd k, and ell=4 at k=2. The odd case proves that the antipode is the unique circulant-radius maximum and that D=2*(k/2)+4, so the balanced class is genuinely below the diameter. Balance of an entire class, not just a single pair, follows from `LDB_of_mixed`, proved using actual graph automorphisms and literal W cardinalities.

The code's outerCount and innerCount include the common origin. Accordingly the code proves outerCount(0)=2k+4 and outerCount(k)=k+3−k%2, whereas the supplied written argument below omits the common origin from both sides. Finite injective inner-route selections give sufficient strict inequalities. The r=0 selection counts the cyclic antipode once; the r≠0 injection is proved by modular divisibility. The odd terminal contribution in the radius-one count is retained. At n=k(k+2), `inner_zero_multiple` proves innerCount(0)=2(k+2), exactly matching the outer count.

For k=2 the six-term U2 source proofs are connected to the actual seven-position outer strip; every unbounded parameter inequality is proved symbolically. A fixed seven-route selection handles the two boundary radii for n≥13. The n=11,12 certificates used by this packet are fresh and refer directly to Bool×ZMod and the literal GP adjacency. The historical Fin(2n) certificates described in the supplied Appendix A are not imported. Each fresh profile is checked for its zero, edge-Lipschitz and predecessor properties using plain `decide`; `certified_distance` proves that the checked table is Mathlib graph distance. Their exact balance and nonbalance assertions are then transferred by rewriting, not by an assumed equivalence.

For odd sharpness, every contributing inner shortcut has a shortest pure inner route, extracted from a shortest graph walk. The global f bound forces its route length into the finite symbolic interval |z|≤h+2. The explicit antipodal cross profile makes its pulse zero except at the two positions |z|=h+1. Both exact counts are four. This support proof is an additional upper-bound argument; the generic four-root lower bound alone would not prove sharpness.

The source appendix contains all local Lean modules in import order, byte-identical to src. REPORT.md and VALIDATION.json give the current full compilation, independent kernel checking, and empty-build replay extracted from that appendix. Only propext, Classical.choice and Quot.sound occur in the final theorem's printed axioms. Pinned upstream Mathlib oleans remain trusted. No native decision procedure or unproved graph-theorem hypothesis is used.

## Complete supplied written balance argument

The following is the supplied reviewed argument, included intact from its metric section through its k=2 appendix. Its full conclusion is proved by the declarations in REPORT.md. The code uses sufficient inner lower bounds at the two small radii, fresh Bool×ZMod finite certificates, and the additional exact-support argument described above for sharpness. Historical certificate filenames in this supplied argument are provenance references, not imported proof assumptions.

## 1. The line and cyclic metrics

Fix k≥3. Write k=2h+δ, δ∈{0,1}; h≥1, and h≥2 when δ=0. Put

    H(b)=min(b,k+1−b), 0≤b<k,
    L(ak+b)=a+H(b), a≥0, 0≤b<k.

Thus L(x)=min_(t∈Z)(|t|+|x−kt|) for x≥0: negative t cannot improve t=0, and among nonnegative t the minimum is at floor(x/k) or its successor. Extend the sawtooth algebraically to all integers by

    g(ak+b)=a+H(b), a∈Z, 0≤b<k.

In particular g(x+k)=g(x)+1, and g(x)=L(x) for x≥0. For 0≤s≤k,

    g(s)=min(s,k+1−s),
    g(−s)=min(s,k−s−1).

At s=k the second formula gives −1, as it should.

Let n>n_k, and write n=qk+r with 0≤r<k. Exactly the following restrictions will be used:

    q≥k+2; and if q=k+2, then r>δ.                 (1)

Let f(j) be distance from 0 to j in the circulant with steps ±1,±k. Then, for 0≤j≤n,

    f(j)=min(L(j),L(n−j)).                         (2)

Here and below the endpoint j=n represents the same residue as j=0. To justify that no extra winding improves (2), one has

    L(x) ≤ x/k + (k²−1)/(2k)  (x≥0).

This follows by maximizing H(b)−b/k over 0≤b<k; the displayed constant is an upper bound for both parities. Consequently the right side of (2), using the nearer of j and n−j, is at most

    (n+k²−1)/(2k).

Every other lift j+tn has absolute value at least n and therefore word length at least n/k. Since n>k(k+2)>k²−1, it is strictly longer. This proves (2). We also obtain

    F+1 < n/k, where F=max_j f(j).                 (3)

The metric and shortcut-support formulas also hold at n=k(k+2): their strict length comparisons require only n>k²+2k−1. The extra restriction in (1) will be used for strict imbalance, not for those metric identities.

## 2. Three distance profiles and the imbalance identity

For residues i define

    a(i)=d(u₀,u_i), b(i)=d(v₀,v_i), c(i)=d(u₀,v_i).

Let p(i) be cyclic distance along the outer n-cycle, and let t(i) be pure inner-cycle distance, with value ∞ if i is in another inner component. Rearranging the outer and inner steps of a walk, which commute modulo n, gives

    c(i)=f(i)+1,
    a(i)=min(p(i),f(i)+2),
    b(i)=min(t(i),f(i)+2).                         (4)

Indeed a mixed walk needs at least one spoke and a same-layer nonpure walk at least two; the stated lengths are attained by putting all steps of each kind together. Walks, rather than necessarily simple paths, suffice for these distance bounds because a shortest walk can be shortened to a path.

Write sgn(x)=1,0,−1 according as x>0,x=0,x<0. Reflection of indices shows f,a,b are even functions. Comparing the u-layer vertices and reindexing the v-layer by i↦j−i gives

    Δ(j):=|W(u₀,v_j)|−|W(v_j,u₀)|
        =Σ_i {sgn(c(i−j)−a(i))−sgn(c(i−j)−b(i))}. (5)

This is the key cancellation: all positions where the two same-layer metrics agree disappear.

Put m=h+1. The outer shortcuts a(i)<f(i)+2 occur exactly at i=0,±1,…,±m. At ±s, 1≤s≤m, one has a=s and f=H(s). The deficit is two except for even k at s=m, where it is one. For 0≤s≤m, the opposite lift is too long to affect f. Beyond m, L(s)≤s−2 (or equality with the baseline at the odd endpoint), and s−L(s) cannot decrease as s increases, since L is 1-Lipschitz. This proves the asserted support.

For an inner shortcut, (3) shows that any improving pure inner walk uses fewer than n/k steps. Its endpoint is therefore ±tk with 1≤t≤q. For r≠0 these two rays have no overlap in the selected range t,t′≤q: a collision would give k(t+t′) a positive multiple of n below 2n, hence k divides n. Also their pure inner lengths really are t: gcd(n,k)<k implies n/gcd(n,k)>2q. Formula (2) gives

    f(tk)=min(t,q−t+H(r)).

Thus the full two-unit inner deficits include exactly the positions ±tk with

    1≤t≤T:=floor((q+H(r))/2),                      (6)

with a possible one-unit terminal position on each ray. For r=0 use the inner q-cycle: the two rays through t≤floor(q/2) cover its nonzero vertices, with just the antipodal overlap if q is even. These are again the full deficits. None of the nonzero inner shortcut positions is an outer shortcut position: their distances in the index n-cycle are at least k, whereas m<k. One way to see this for r≠0 is that the possible terminal t is <q, since q>H(r)+1.

The i=0 terms cancel in (5). All remaining terms split as

    Δ(j)=O(j)−I(j),                               (7)

where O,I are nonnegative. For a full inner deficit at ±tk its contribution to I is

    K(f(j∓tk)−t),
    K(x)=2 if x=0, 1 if |x|=1, and 0 otherwise.    (8)

All unselected inner deficits can safely be ignored for a lower bound on I.

## 3. The six-term outer calculation

Here is an elementary table used in the proof. It is included explicitly so that the arithmetic is not delegated to a numerical search or SMT answer.

For integers z,C let

    U_k(z,C)=Σ_(s=1)^m Σ_(e=±1)
      [sgn(1+C+g(z+es)−s)
       −sgn(1+C+g(z+es)−(H(s)+2))].              (9)

Every summand is nonnegative. For C≥h+1 and the ranges of z used below, only s=h−1,h,h+1 can contribute. For z∈[0,k−1], g(z±s)≥0; for z=−u, 1≤u≤h, its minimum over these arguments is −1. The lower bound on C therefore makes all s≤h−2 vanish.

For z∈[0,k−1], the nonzero entries are:

| parity of k | C | z and U_k(z,C) |
|---|---|---|
| even | h+1 | z=h or h+1: 1; additionally z=0: 1 when h=2 |
| even | C≥h+2 | none |
| odd | h+1 | z=h: 3; z=h+1: 2; z=h+2: 1; additionally z=0: 2 when h=1, or 1 when h=2 |
| odd | h+2 | z=h+1: 1; additionally z=0: 1 when h=1 |
| odd | C≥h+3 | none |

For the negative arguments needed below:

| parity | range | C | nonzero entries |
|---|---|---|---|
| even | 1≤u≤h−1 | h+1 | u=h−2: 1; u=h−1: 2 |
| even | 1≤u≤h | h+2 | u=h−1 or h: 1 |
| even | 1≤u≤h | C≥h+3 | none |
| odd | 1≤u≤h | h+2 | u=h−1: 1; u=h: 2 |
| odd | 1≤u≤h | h+3 | u=h: 1 |
| odd | 1≤u≤h | C≥h+4 | none |

The even rows use h≥2 and the odd rows h≥1. When h=1, the six-term calculation includes the dummy s=0 terms; both vanish in all table applications because their c value is above 2. These are identities for unbounded h. To check them, substitute s=h−1,h,h+1 into (9), use g(x+k)=g(x)+1, and then g(x)=min(x,k+1−x) on [0,k] and g(−x)=min(x,k−x−1) on [0,k]. At the only argument below −k occurring in these table ranges, namely −k−1, use g=0. For example, the odd positive row at C=h+1 has one unit at z=h from s=h and two further units from s=h+1 (arguments −1 and k), giving 3; z=h+1 gives the central weight 2; z=h+2 the endpoint weight 1. The small-h coincidences at z=0 are exactly the h=1 and h=2 entries displayed above. This accounts for every possible zero or unit value of g producing a nonzero summand. Increasing C beyond the listed values puts every remaining argument above its pulse interval.

Also, directly from (9), for any k≥3,

    U_k(0,2)=2, U_k(0,3)=1, U_k(0,C)=0 for C≥4.  (10)

The cases C=0,1 are handled separately below.

If c(i−j)=1+min(P_i,R_i), its nonnegative outer pulse is at most the sum of the pulses with c=1+P_i and c=1+R_i, because the minimum is one of those two numbers. Thus the U tables give upper bounds for O without assuming that the pulse is monotone.

## 4. Four inner contributions

We use the following counting observation. Write j=Ak+B and n−j=A'k+B', with 0≤B,B'<k, and set

    C=L(j)=A+H(B), C'=L(n−j)=A'+H(B').

Suppose C,C'≥2, A≥H(B), A'≥H(B'), and C,C'≤2T. For C even choose t=C/2 on the positive inner ray; for C odd choose t=(C−1)/2 and (C+1)/2. These are positive and at most T. The condition A≥H(B) implies t≤A. Consequently j−tk≥0 and

    L(j−tk)=C−t,
    L(n−j+tk)=C'+t≥t+2.

At the chosen t the first value is t or t±1, so (2),(8) give total weight two. Applying the same argument to n−j gives total weight two on the negative ray.

The two groups of selected vertices are disjoint. For r≠0 the rays never overlap. For r=0, (1) gives q≥k+3. In the low-radius uses below, C+C'=q. In the high-radius uses, the explicit offsets (13) give C+C'≤q+k−1: if q is even B=−s and the sum is q+2s≤q+k−1; if q is odd, B=s≤h and H(s)+g(−s)≤k−1 gives the same bound. A selected positive root t and negative root t' consequently satisfy

    t+t' ≤ (C+C'+2)/2 ≤ (q+k+1)/2 ≤ q−1.

Thus they cannot represent the same inner-cycle vertex. Within a ray the odd roots are distinct. We conclude

    I(j)≥4.                                      (11)

## 5. Low-radius witnesses

Let 2≤a≤Q:=floor(q/2), and take j=ak. Formula (2) gives f(j)=a. Its outer bound is

    O(j)≤U_k(0,a)+U_k(r,q−a)≤3,                  (12)

by (10) and the positive-argument table: for even k, q−a≥h+1; for odd k, q−a≥h+2.

For (11), C=a, C'=q−a+H(r), A=a,B=0, A'=q−a,B'=r. Since q−a≥Q≥max H, the two axis-dominance inequalities hold. Also C,C'≤2T, using a≥2. Thus Δ(j)≤−1, and the mixed distance a+1 is unbalanced.

## 6. High-radius witnesses

Let a=Q+s>Q be any attained circulant radius, s≥1, and put ε=q mod 2. We construct j=Qk+B with f(j)=a. The offset B is defined by the following cases:

    ε=0: B=s if 2s≤r, otherwise B=−s;
    ε=1,r=0: B=s;
    ε=1,r≥1:
      B=r+s−1 if s≤floor((k−r)/2)+1,
      B=r+1−s otherwise.                         (13)

Only attained radii are being described. In particular (13) always satisfies

    min(g(B), ε+g(r−B))=s.                       (14)

Here is a full justification that these last blocks suffice; no monotonicity of a sawtooth is being assumed. Write an arbitrary index j=Ak+b, 0≤b<k. If b≤r, the two line costs have sum

    q+H(b)+H(r−b) ≤ q+r.

If b>r, their sum is

    q−1+H(b)+H(k+r−b)
      ≤ q−1+min(k−r+2, 2 max H),

using H(b)≤k+1−b, H(k+r−b)≤b−r+1, and the trivial bound by twice max H. These are bounds on every index, not merely the last two blocks.

For ε=0, it follows that every high level Q+s either has 2s≤r, or satisfies both 2s≤k−r+1 and 2s≤2 max H−1. In the first case B=s lies in the last partial block, gives f=Q+s. Otherwise B=−s gives g(−s)=s and g(r+s)≥s, hence f=Q+s. This proves that the even-q construction attains every possible high level.

For ε=1,r≥1, the sum bounds give either

    s≤min(floor((k−r)/2)+1, max H),

or 2s≤r+1. In the first regime B=r+s−1 gives g(B)≥s and 1+g(r−B)=s with r≤B≤(k+r)/2. In the second regime, if the first one is unavailable, B=r+1−s gives g(B)≥s and 1+g(r−B)=s with B≤r. The inequalities 2s≤r+1 and 2s≤k−r+2 respectively verify each required H-value directly. For r=0 separately, H(b)+H(k−b)≤k gives s≤floor(k/2), and B=s attains the level. Thus every attained high level is covered by (13), and direct substitution proves (14).

### The inner lower bound applies

For B≥0, the canonical quotient of j is Q, which is at least max H. If B=−s, then ε=0 and (14) gives g(−s)=s, hence s≤h−1 for even k and s≤h for odd k. Its canonical quotient is Q−1 and its remainder has H-value s+1, so it still satisfies quotient≥H. The canonical quotient of n−j is at least Q; any negative offset in its representation is precisely one of the small offsets in (13), whose H-value is at most Q. Thus both axis-dominance inequalities hold.

Also C=L(j)≤2Q≤2T. For C'=L(n−j), when ε=0, its quotient is at most Q+1 and its remainder has H at most h for even k and h+1 for odd k; respectively Q≥h+1 and Q≥h+2 give C'≤2Q. When ε=1 and k is even the same bound holds. When ε=1 and k is odd, C'≤2Q+1; if r≥1 then T≥Q+1 and this is sufficient, while if r=0 its negative offset gives C'≤2Q directly. Finally C,C'≥a≥2 by (14). Therefore (11) gives I(j)≥4.

### The outer contribution is at most three

We have

    O(j)≤U_k(B,Q)+U_k(r−B,Q+ε).                 (15)

Normalize a positive argument at least k by subtracting k and increasing C by one.

If ε=0 and B=s≥0, then 0≤B,r−B<k. Both U terms are at most one (Q≥h+1 for even k, Q≥h+2 for odd k). If B=−s, the range of s just obtained and the negative table bound the first term by two, and the second by one; if r+s≥k its normalized second term is zero. Thus O≤3.

Suppose ε=1. Here B≥0. If r−B≥0, the even-k bound is immediate. For odd k, Q≥h+2 also makes it immediate. In the remaining odd case Q=h+1, the first U term can be nonzero only for B=h,h+1,h+2, since B=0 is impossible at a high radius. If it is nonzero, r−B≤h, whereas for h≥2 the second term (at C=h+2) can only be nonzero at r−B=h+1. They cannot both contribute. The additional h=1 case has k=3 and, by (1), r=2; then B=1 gives first/second terms 3,0, and B=2 gives 2,1. Thus again O≤3.

If r=0 and r−B<0, then B=s≤h. For even k, the positive term is at most one and the negative term at C≥h+2 at most one. For odd k, (1) forces Q≥h+2, and the corresponding two bounds are again one each.

Finally let r≥1 and r−B<0. By (13), B=r+s−1 and r−B=−(s−1). Formula (14) forces s−1≤h−1 for even k and s−1≤h for odd k. The even bound is at most 1+1. The odd bound with Q≥h+2 is also at most 1+1. If k is odd and Q=h+1, (1) gives r≥2. When s−1≤h−2 the second term is zero. When s−1=h−1 the second is one, and B=r+h−1≥h+1 makes the first at most two. When s−1=h the second is two, and B=r+h≥h+2 makes the first at most one. This exhausts the possibilities and proves O(j)≤3.

Combining with I≥4 proves Δ(j)<0 for every attained high radius.

## 7. Radii zero and one

At j=0, the outer total is O=2k+2. Directly counting the full and possible terminal inner deficits gives

    I=2(q+H(r)) if r≠0;
    I=2q−2 if r=0.

In the latter case (1) implies q≥k+3. In the former H(r)≥1. Thus I>O and the distance-1 pair is unbalanced.

At j=k, the outer total is k+2 for even k and k+1 for odd k, by substituting into the same outer pulses. No opposite-lift pulse appears because q−1≥k+1. For r≠0 the inner-ray counts give I≥q+H(r), which is strictly larger than either outer total by (1). For r=0 those counts give exactly I=q−1 when q is even and I=q when q is odd. If k is even, the smallest allowed even q is k+4 and the smallest allowed odd q is k+3; both give I>k+2. If k is odd, q≥k+3 gives I>k+1 in either parity. Hence the distance-2 pair is unbalanced.

For an explicit check of the ray count when r≠0, put q+H(r)=2T+η, η∈{0,1}. On the positive ray t=1,…,T each contributes one at j=k. On the negative ray t=1,…,T−1 each contributes one; t=T contributes one if η=0 and two if η=1. This already gives 2T+η=q+H(r). Any terminal one-unit deficit only adds a nonnegative amount. For r=0 the unique antipodal overlap when q is even must be counted once, giving the displayed q−1 value.

## 8. All subdiametral distances

By (4), D≤F+2. Therefore 1≤ℓ<D implies 0≤ℓ−1≤F, so ℓ−1 is an attained circulant radius. Sections 5–7 supply a mixed pair at exactly that distance with Δ<0. Thus GP(n,k) is not ℓ-distance-balanced at every subdiametral ℓ, for all n>n_k and k≥3. Appendix A supplies k=2, finishing the full stated range.

## 9. The threshold is sharp

For even k≥4, let n=k(k+2), so q=k+2,r=0. The radius-zero formula gives O=I=2k+2. Thus (u₀,v₀) is balanced. All outer edges form one orbit, all inner edges form one orbit, and a reflection exchanges the ends of every edge within either layer. Hence every adjacent pair is balanced, and D>1. This provides a subdiametral balanced class at n=n_k.

For odd k≥3, write k=2h+1 and set n=(k+1)². Then q=2h+3, r=1, Q=h+1. The maximal circulant radius is F=2h+2, attained only at j=n/2. Indeed earlier quotient blocks have L≤Q−1+(h+1)<F, and in the last block equality forces its unique maximal remainder h+1; (2) gives equality there. At this antipode, both same-layer distances are F+2: the outer pure distance is n/2, and the inner pure distance is also n/2, since k is odd and coprime to n. Thus D=F+2.

At j=n/2 only s=h+1 contributes to O, with weight two on each side, so O=4. The full inner rays have t≤h+2. For t≤h+1 the cross radius at j∓tk is F−t, whose pulse is nonzero only at t=h+1, with weight two on each ray. For t=h+2 it is h=t−2, outside the pulse. Hence I=4 and Δ=0. The only mixed pairs at distance D−1 are rotations of this antipodal pair; same-layer pairs at every distance are balanced by reflection. Therefore the entire distance D−1 class is balanced at n=n_k. The finite n=11 certificate in Appendix A supplies k=2 sharpness. In every case a smaller eventual threshold would still have to include n=n_k, so n_k is minimal. ∎

## Appendix A. A compact k=2 route

**Historical certificate note.** The `formal/` filenames below refer to the proof lane's exploratory certificates. The present packet proves `k2_main` and `k2_sharp` using new direct Bool×ZMod certificates and the U2 source arithmetic, as described in Stage-4 formal completion. No equivalence with the old Fin(2n) representation is assumed. This appendix records the written k=2 argument; this published special case receives no novelty credit.

For n≥13 write n=2q+r, r∈{0,1}, q≥6; q=6 forces r=1. The line metric is now L(x)=ceil(x/2) for x≥0, and its signed extension is g₂(x)=floor((x+1)/2). Formulae (2),(4),(5),(7),(8) hold unchanged. At a position where both layers have shortcuts, expand both against the common baseline f+2 in (5); the O−I identity still holds, without requiring the outer and inner shortcut sets to be disjoint.

The nonzero outer shortcuts are now ±1,±2,±3: their pure lengths are 1,2,3, their f-values 1,1,2, and their deficits 2,1,1. There are no further ones, since x−ceil(x/2)≥2 for x≥4. The inner support and root argument of Section 4 remain valid with k=2 and T=floor((q+r)/2).

Define U₂ by (9), replacing g with g₂ and summing s=1,2,3. Direct substitution gives, for C≥2,

| argument | U₂(argument,C) |
|---|---|
| 0 | 2 if C=2 or 3; 1 if C=4; 0 if C≥5 |
| 1 | 2 if C=2; 1 if C=3 or 4; 0 if C≥5 |
| −1, C≥4 | 1 if C=4 or 5; 0 if C≥6 |

These unbounded-C identities and their following two inequalities are kernel checked in `formal/K2Tables.lean`. For 2≤a≤Q=floor(q/2),

    U₂(0,a)+U₂(r,q−a)≤3,

except at (q,r,a)=(6,0,3), which is n=12 and is excluded here. To check the inequality from the table, a contribution of 2 requires its cost to be at most 3. Both terms can be 2 only when r=0, a=q−a=3, because q≥6; this is precisely the exception. Take j=2a. The four-root argument gives I≥4 and hence strict imbalance at mixed distance a+1.

The maximum circulant radius is ceil(q/2): on 0≤j≤floor(n/2)=q the metric is ceil(j/2). If q is odd, the only additional radius is Q+1, witnessed by j=q=2Q+1. Its two line costs are C=C′=Q+1; both axis-dominance inequalities and all root bounds hold, with q≥7. Here

    O≤U₂(1,Q)+U₂(r−1,Q+1)≤2<4≤I.

The last upper bound follows at once from the table and Q≥3. If q is even there is no additional radius.

For radius zero, directly count the six outer pulses to get O=8. The inner counts are I=2(q+1) for r=1 and I=2q−2 for r=0; both exceed 8. For radius one, use j=2. At the six outer shortcut positions, the opposite lift cannot affect the cross distance because |i−2|≤5 and n≥13. Substitution gives O=5. The inner count of Section 7 gives I≥q+1 for r=1, I=q−1 for r=0 and even q, and I=q for r=0 and odd q. Each is greater than 5 in the present range. Together with D≤F+2 these witnesses cover every subdiametral distance when n≥13.

It remains to check n=12 and sharpness at n=11. Here are complete root-distance profiles; all other rows are their rotations. The symbols a,b,c retain their Section 2 meanings.

| n | profile | values at indices 0,...,n−1 |
|---|---|---|
| 11 | a | 0,1,2,3,4,5,5,4,3,2,1 |
| 11 | b | 0,3,1,4,2,3,3,2,4,1,3 |
| 11 | c | 1,2,2,3,3,4,4,3,3,2,2 |
| 12 | a | 0,1,2,3,4,5,5,5,4,3,2,1 |
| 12 | b | 0,3,1,4,2,5,3,5,2,4,1,3 |
| 12 | c | 1,2,2,3,3,4,4,4,3,3,2,2 |

There is a short exact certificate that these tables are the actual shortest-path distances: zero occurs exactly at the root, adjacent steps change the proposed distance by at most one, and each nonroot vertex has an adjacent predecessor whose proposed distance is one smaller. The first two conditions bound every walk from below; repeated predecessors build a walk of the proposed length. All three conditions, for every ordered pair, are kernel checked in `formal/FiniteCases.lean`, together with that general certificate-to-shortest-walk lemma. The graph predicate in that file is the printed outer/inner/spoke adjacency on Fin(2n), with offsets modulo n, not an adjacency inferred from the tables.

For n=12, both the diameter and its attained maximum are 5. For ℓ=1,2,3,4 respectively, mixed indices j=0,1,4,5 have imbalances −2,−2,−1,−1. For n=11 the diameter is 5 and every pair at distance 4 is balanced. The finite cardinality and diameter assertions are also kernel checked in that file. This settles n=12 and shows that no eventual threshold below 11 works. The independent BFS/profile replay is `scripts/petersen_finite_cases.py`; the unbounded q audit is `scripts/petersen_k2_audit.py`.


## Significance and formalization limits

The metric branches and the cases k≤4 have published predecessors and receive no new-result credit here. The potentially new content is the uniform inner-versus-outer witness mechanism, including distance 2 near the threshold, and odd-k sharpness. The complete three-part conjecture is now proved in Lean, using the source graph and exact threshold rather than a surrogate or asymptotic bound. This does not resolve the review's incomplete citation census or original journal-body access limit. No new prior-art investigation was made in this continuation, and root's independent statement, proof and novelty review remains necessary before acceptance.

## Final-review prior-art refresh and access limits

The final reviewer checked arXiv:1702.05257 on 20 November 2026; its history lists only v1. The graph, strict W comparison, universal distance-class condition and piecewise threshold agree with the literal endpoint. There is no further small-k exception in the arXiv conjecture or in the later papers' restatements. The journal is *Discrete Applied Mathematics* 244 (2018), 143–154, DOI https://doi.org/10.1016/j.dam.2018.03.011. Direct publisher and institutional repository requests returned access refusals; the final journal body was not independently inspected. The journal statement is corroborated indirectly by the later authors' restatements, rather than certified from that body.

The closest inspected prior work is Ma–Wang–Klavžar, arXiv:2407.02635 (distance 1, even-threshold sharpness, and weaker distance-2 bounds), arXiv:2309.01900 (the complete k=3,4 cases), and arXiv:2208.08305v2 (diametral balance). Wang–Ma, DOI https://doi.org/10.1016/j.disc.2026.115070, treats distance-2 balance at n=k²±1, below the eventual threshold; its searchable publisher abstract and theorem preview were inspected, not the full article. These results do not give a short route to the arbitrary-k, arbitrary-subdiametral-distance theorem.

Fresh searches of the four named local registries, two GitHub code queries, and the mandatory omega issue queries found no matching public resolution. API attempts did not produce a complete citing-paper census. This bounded search supports treating the result as a nonroutine resolution, but is not exhaustive novelty clearance. See FINAL-REVIEW-335309.md in the final-check lane for evidence and limitations. No submission, publication or external message occurred.
