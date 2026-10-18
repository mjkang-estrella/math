> Historical working record. This status marker was added after author proof
> completion; the original text below is retained. Its unresolved/no-nominee
> status is superseded by `candidate205m.md`, pending independent gates.

# Staircase multiplicity continuation: exact quotient bounds and their limits

Myeongjin Kang, no affiliation. Original prose CC BY 4.0; diagnostic code MIT.
Author exploration only, resumed 2026-10-18 after the T027O manuscript task.
**No target was frozen, no theorem is nominated, and no count is requested.**
The earlier `checkpoint.md` and `checkpoint-inventory.json` remain unchanged
historical snapshots. This continuation does not rewrite their reading chronology.

## 1. The provisional question and the actual source contracts

For m≥2 put N_m=m(m+1)/2 and ρ_m=(m,…,1). The question remains whether

    g(ρ_m,ρ_m,λ) ≥ m−1

for every complex irreducible label λ⊢N_m other than (N_m) and (1^N_m).
The classical corner formula gives equality at (N_m−1,1), so this is the
proposed sharp minimum, not an unspecified asymptotic bound. Neither the
question nor a restricted version is asserted as a result. The old I17/I21
symmetric/exterior-square scope is unchanged; this ordinary multiplicity
question is not a resolution of that signed scope.

Write W_m=C[S_Nm](v_R⊗v_C) for the *specified* cyclic module in source205.
The stipulated source proves that every irreducible occurs in W_m. Its
actual band projection is a surjection onto the full induced module

    Ind(W_(m−s) ⊠ U_(m,s)),  s=1,2 and m−s≥1.

For s=1 the band is trivial of size m. For s=2, it has size 2m−1 and is the
multiplicity-free sum of all Specht types with at most four rows. The latter
identification uses BOTH the source's generator-specific path support and
Bessenrodt–Bowman, published Theorem 7.11, which computes the entire square
of (m,m−1). I21 already made this identification. It is not new here.

The source's repeated-row construction, strengthened in I21 §2.1, gives
M^ρ_m in a sign twist of W_m. Therefore

    [W_m:S^λ] ≥ K_(λᵗ,ρ_m).

This is also inherited. Separate quotient maps give separate lower bounds;
their multiplicities may be maximized but not added without an independence
argument. In contrast, distinct summands WITHIN a single induced quotient
may and must be added with their LR multiplicities.

## 2. A precise sufficient recursion, not a proved uniform estimate

Set R_1((1))=1. For m≥2 define R_m(λ) as the maximum of:

* 1, from the stipulated cyclic support theorem;
* K_(λᵗ,ρ_m);
* ∑_(ν⊢N_(m−1)) R_(m−1)(ν)c_(ν,(m))^λ;
* if m≥3, ∑_(ν⊢N_(m−2)) ∑_(η⊢2m−1, ℓ(η)≤4)
  R_(m−2)(ν)c_(ν,η)^λ.

All coefficients are nonnegative. Induction using the actual quotients
proves R_m(λ)≤[W_m:S^λ]. Since the full staircase square is invariant under
sign twist, it follows that

    g(ρ_m,ρ_m,λ) ≥ max(R_m(λ),R_m(λᵗ)).                 (2.1)

No sign invariance of W_m is asserted or used. In particular, a bound on the
full smaller square, or on max(R_h(ν),R_h(νᵗ)), cannot simply be fed back into
the W_h position of the displayed recursion. That would be an unjustified
replacement of the specified cyclic module by its ambient square.

A concrete sufficient missing statement is:

    For all m≥5 and every eligible λ,
    max(R_m(λ),R_m(λᵗ)) ≥ m−1.                        (2.2)

It is a proposed combinatorial obligation, NOT a theorem. Together with the
literal m=2,3,4 cases it would settle the original question. This is stronger
than merely finding one successful strip deletion. One must control the
multiplicity-weighted branching sums for every shape, while retaining the
asymmetry of the smaller cyclic bounds. An alternative would construct
independent copies outside these quotients and prove their independence.
Neither operation is completed here.

`quotient-diagnostic.py` computes (2.1) exactly through m=7. The bound reaches
m−1 for every eligible λ at m=2,5,6,7. At m=3 it gives 1 for (3,3) and
(2,2,2), while the actual square multiplicities are 2. At m=4 it gives 2
for (5,5) and (2^5), while their actual multiplicities are 6. All other
eligible labels meet the proposed bound in these finite cases. Exact
Murnaghan–Nakayama character calculations check orthogonality, hook dimensions,
full tensor-square dimensions, integral coefficients, and the range of the
new numerical bounds. These checks do not establish (2.2).

## 3. An infinite obstruction to discarding inherited multiplicities

Let G_n=⊕_(ν⊢n) S^ν, with one copy of each irreducible. Replacing W_h by this
support-only submodule gives the two legitimate but weaker bounds

    A_m(λ) = [Ind(G_N_(m−1) ⊠ 1_m):S^λ],
    B_m(λ) = [Ind(G_N_(m−2) ⊠ U_(m,2)):S^λ].

The shortcut that combines only 1, both dominance Kostka bounds, and A_m,B_m
in the two orientations cannot yield the proposed m−1 bound uniformly.
This statement excludes only that shortcut, not (2.2), not all uses of the
companion, and not the proposed Kronecker bound.

### 3.1 Long hooks: exactly two and eight copies

Let K=2m−1 and λ=(a,1^b), a+b=N_m, with both arms long: a>K and b≥4.
Any ν⊂λ is a hook (c,1^d). The skew diagram λ/ν is the disjoint union of a
horizontal row of length A=a−c and a vertical column of length B=b−d.
Thus its skew Schur function is h_A e_B. For A,B>0, Pieri gives

    h_A e_B = s_(A+1,1^(B−1)) + s_(A,1^B).

For B=0 only s_(A) occurs. To have a constituent of length at most four,
one needs B≤4. With A+B=K, the total multiplicities for B=0,1,2,3,4 are
respectively 1,2,2,2,1. All five ν are valid under the stated arm bounds;
there are no others with a ≤4-row constituent. Hence B_m(λ)=8 exactly.
For a horizontal m-strip the only possible values of B are 0 and 1,
each giving one copy, so A_m(λ)=2.

Take a=ceil(N_m/2), b=N_m−a. For every m≥10 the same arm conditions hold
for λ and λᵗ. Both have more than m rows after the relevant transpose:
K_(λ,ρ_m)=K_(λᵗ,ρ_m)=0, since a semistandard tableau of content ρ_m uses
only m letters and cannot have a column longer than m. Thus the maximum of
all these support-only bounds is exactly 8<m−1. The inequalities on the
arms follow directly from N_m/2−1≥2m−1 for m≥7.

### 3.2 A non-hook family: exactly four and twenty-eight copies

The same issue persists beyond hooks. Let λ=(a,2,1^b), a+b+2=N_m, with
 a≥K+2, b≥6, K≥7. In any relevant skew diagram λ/ν, column strictness for
a ≤4-row constituent forces at most four removed cells in each column.
The top horizontal segment is disconnected from the remaining skew diagram
because ν_1≥a−K≥2. Apart from that segment there are exactly two cases:

1. The cell (2,2) remains in ν. Remove B bottom cells from column one,
   B=0,…,4. The skew Schur function is h_(K−B)e_B. These cases total 8.
2. The cell (2,2) is removed. It is disconnected from the B bottom cells,
   since b≥6. The skew Schur function is h_(K−B−1)h_1e_B, B=0,…,4.
   Applying the preceding two-hook identity and then adding one box gives
   the ≤4-row multiplicity sums 2,5,6,5,2, respectively. These total 20.

All the listed ν are distinct and valid; a removed fifth bottom cell would
force five entries in a skew column and contributes nothing. The two cases
exhaust ν. Consequently B_m(λ)=28. For η=(m), case 1 contributes B=0,1
once each; case 2 also contributes B=0,1 once each. Hence A_m(λ)=4.
Multiplicity is counted here even when different Pieri paths end in the
same η, as the LR sum requires.

Now set a=floor(N_m/2), b=N_m−a−2. For every m≥30 both λ and
λᵗ=(b+2,2,1^(a−2)) meet the arm conditions. Both dominance bounds vanish
by the same column-length argument. The support-only maximum is exactly
28<m−1. `hook-bound-diagnostic.py` independently enumerates the one-box
Pieri additions and checks the parameter inequalities for finite ranges;
the elementary inequalities and skew-Schur argument above prove the
infinite-family assertion. This is route exclusion evidence, not a nominee.

## 4. Closest operations and contribution boundary

* **Pinned cyclic source205:** the full induced quotient, specified generator,
  square-deficit dominance map, odd-path test, and positivity induction are
  inputs. Its proof selects one LR witness, whereas (2.2) requires a uniform
  multiplicity estimate. The formal recursion itself is an elementary
  consequence of these printed maps and is not a substantial new result.
* **I21:** the exact repeated-row permutation module, ordinary Kostka
  multiplicities, width-two full-square identification, arbitrary-width
  cyclic quotients and warning against adding separate bounds are already
  developed. Its signed rank failures and growing-width requirements do not
  prove or refute this ordinary quantitative question.
* **Universal Tensor Squares companion:** the actually read balance proof
  separates local projected squares into disjoint output sectors. Its
  neighboring-column block is the same classical multiplicity-free two-row
  square. Its balanced-list substitutions explicitly preserve SUPPORT, not
  the larger Kostka multiplicities of a permutation module. Replacing such
  a local block by a full balanced permutation module would be invalid.
  Nothing in this screen establishes that all other companion packings fail.
* **Vallejo, arXiv:1310.8362v2, §8:** Theorem 8.10 constructs, for each fixed
  tail ν⊢d, a degree-d polynomial on the main interval whose leading
  coefficient is f^ν and whose values are the staircase-square
  multiplicities. Its proof counts removable diagram classes and applies
  the signed RT formula. Theorem 8.14 bounds the exceptional integer zeros;
  Table 1 treats d≤5. This pays fixed-depth growth and the near-trivial
  formulas, but does not supply a uniform bound when the tail varies with m.
  No new fixed-depth result is nominated.
* **Bessenrodt–Bowman–Sutton, arXiv:1903.07717, §5:** equation (5.1)
  g_λ=∑_νG_νd_(λ,ν), projectivity, Carter's criterion, Theorem 5.10 and
  Theorem 5.11 give lower bounds from decomposition numbers and LR data in
  specified families. Their introductory discussion already records
  g(ρ_m,ρ_m,(N_m−1,1))=m−1 and unbounded multiplicities in other families.
  The all-label estimates of G or d required here were not obtained.
* **Bessenrodt–Bowman, ALCO 6 (2023), Theorem 7.11:** the two-row square and
  its split are primary inputs, not new band multiplicities. Their §10
  signed conjecture remains the older I17/I21 target, not this screen's result.
* **Accepted R026:** the integral regular summand in the staircase CUBE and
  its Bryant–Kovács/Ikenmeyer mechanism are paid. This screen claims no new
  cube statement, integral extension, or count from those constructions.

These are operation-level comparisons of the stated reads, not a worldwide
novelty determination. There is no complete candidate to classify.

## 5. Disposition and handoff

**NO NOMINEE; proposed all-partition sharp multiplicity question unproved
and not frozen.** The useful progress is the exact safe recursion, finite
all-partition tests through m=7, and the two infinite support-only route
exclusions. The remaining debt is specifically the uniform estimate (2.2),
with the cyclic/ambient distinction respected, or another independent-copy
construction. Neither generic support, separate quotients, signed trace
identities, nor fixed-depth asymptotics pay that debt. The full original
question is not weakened into a bounded-m, hook-only or fixed-depth result.
