# A certified weighted profile for the Long–Wagner three-cube problem

## Scope and source convention

This manuscript gives the complete ordinary proof underlying the formalization
packet for MathDB 340621. Formal verification status is recorded separately in
REPORT.md; unproved planned Lean declarations are never used as axioms.
The completed packet proves LongWagner.lw_upper for every n and
LongWagner.lw_conj_5_1 for n≥3, including the explicit extremizer. All 174
modules have compiled and passed standalone kernel checking; both endpoints
use only propext, Classical.choice, and Quot.sound.

Long and Wagner, *The largest projective cube-free subsets of Z_(2^n)*,
arXiv:1810.01225v1, Conjecture 5.1, state:

> The largest 3-cube-free family in Z_(2^n) has size (5/8) · 2^n.

Their displayed definition, for a multiset of generators, is

Σ*S = { sum_(i∈I) a_i : ∅ ≠ I ⊆ [k] }.

The source uses k in this display after describing a multiset of size d.
In dimension three the definition is exactly the seven nonempty subset sums
x,y,z,x+y,x+z,y+z,x+y+z. The source explicitly allows repeated generators
and views the cube as a set of residues. For d-cube-freeness its definition says
“there does not exist a multiset S of size d with (Σ*S)⊆A”.
It also explicitly includes the singleton zero cube.
Thus coincidences and zero generators count, as in the literal Lean definition:

```lean
def CubeFree3 {G : Type*} [AddCommGroup G] (A : Finset G) : Prop :=
  ∀ x y z : G, ¬ (x ∈ A ∧ y ∈ A ∧ z ∈ A ∧
    x+y ∈ A ∧ x+z ∈ A ∧ y+z ∈ A ∧ x+y+z ∈ A)
```

The cyclic group is Lean's ZMod (2^n). The standing range n≥3 for equality
comes from Conjecture 1.12, which assumes d≤n. MathDB’s introductory phrase
“n positive” omits this inherited restriction: equality is not asserted here
for n=1,2, where (5/8)·2^n is nonintegral. The stronger upper bound holds
for every n≥0. The small maxima at n=0,1,2 are respectively 0,1,2.

**Theorem.** Every such cube-free A⊆Z_(2^n) satisfies 8|A|≤5·2^n.
For n≥3 the greatest possible size is 5·2^(n−3), attained by the inverse
image of {1,3,4,5,7} under reduction modulo eight.

Source: [definitions, §1.2](https://arxiv.org/html/1810.01225v1#S1.SS2)
and [Conjecture 5.1, §5](https://arxiv.org/html/1810.01225v1#S5).
A local HTML snapshot and its SHA256 are in sources/.

## 1. A finite signed-integer inequality

Let V={−18,...,−1,1,...,18}. Call B⊆V admissible if there do not exist integers a,b,c for which

{a,b,c,a+b,a+c,b+c,a+b+c} ⊆ B.

Only cubes entirely contained in V are relevant; generators can repeat.

Assign the same weight to i and −i, with these positive integer weights:

| i | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 |
|---|---|---|---|---|---|---|---|---|---|
| w_i | 253 | 269 | 288 | 286 | 166 | 342 | 174 | 256 | 262 |

| i | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 |
|---|---|---|---|---|---|---|---|---|---|
| w_i | 174 | 61 | 226 | 69 | 149 | 98 | 100 | 82 | 90 |

**Finite lemma.** Every admissible B⊆V satisfies

sum_(i=1)^18 w_i (1_B(i)+1_B(−i)) ≤ 4131.                 (1)

This lemma is proved by the attached finite certificate, **not by a floating optimizer**. The complete data are `certificate-340621.json`, SHA256

`b6923d9c3139b621fc89579508d085c50e3c5515d24967535d316da18d876451`.

Its standalone verifier is `scripts/verify_340621.py`. Here is the certificate's exact proof system and soundness proof, so the finite calculation is fully specified and auditable.

Index V in increasing order and represent subsets by 36-bit nonnegative integers. Each certificate state consists of an allowed mask M and one of the following:

* A **branch** gives a nonempty mask E⊆M and a triple (a,b,c) whose set of seven displayed sums is exactly E. For every v∈E the certificate contains the strictly smaller child M\{v}.
* A **leaf** gives a list of valid cube masks E⊆M, each with a positive integer coefficient λ_E. The verifier checks that the load sum_(E containing v) λ_E is at most w_v for every vertex v, and that

  w(M)−sum_E λ_E ≤4131.

For any admissible S⊆M, each cube E omits at least one vertex of S. Consequently

sum_E λ_E ≤ sum_(v∈M\S) sum_(E containing v) λ_E
            ≤ sum_(v∈M\S) w_v = w(M)−w(S).

This proves the bound at every leaf. At a branch, S omits some v∈E and therefore lies in that child. Induction on |M| proves the bound at every state. The root mask is all of V, so (1) follows. Masks strictly decrease at branches, so no circular justification is possible.

The standalone verifier independently reconstructs each used seven-sum set from its three integer generators, checks every branch child, every packing load and every leaf arithmetic inequality. It uses only Python integers, set operations and JSON parsing: no SciPy, SAT solver, native approximation or assumed optimizer answer. It reports:

* 12,564 states: 3,510 branches and 9,054 leaves;
* 1,441 distinct valid cube masks used;
* 80,091 nonnegative integer packing coefficients checked;
* root bound 4131, with no failed condition.

The original uncompressed certificate was independently checked as well, by a different consumer and a pure deletion bound. It is retained in `logs/`, but is not needed for this proof. The optimization programs in `scripts/cube_*columns.py` and `cube_capture_certificate.py` were used only to discover weights; neither their floating arithmetic nor their solver correctness is a premise of (1).

## 2. Averaging the finite lemma over odd multipliers

Write N=2^n, n≥1. A cube-free A cannot contain 0, since the three zero generators give the cube {0}.

For 0≤j<n, let L_j be the residues with exact 2-adic valuation j and let

α_j=|A∩L_j|/|L_j|.

Set α_j=0 for j≥n. For a nonzero integer t with valuation j<n, multiplication by t maps the odd residues of Z_N uniformly onto L_j: writing t=2^j u with u odd, multiplication by u is invertible, and every element of L_j has exactly 2^j odd preimages. If j≥n the image is 0, which is absent from A. This also treats negative t.

For every odd residue x define

B_x={t∈V : tx∈A}.

It is admissible: a full integer cube in B_x would map under multiplication by x to a projective cube in A. This argument is valid even when coefficients coincide modulo N or some coefficient maps to 0. Repeated generators are allowed by the source definition.

Average (1) over all odd x. The weight sums in the five represented valuation classes are exactly

| j | 0 | 1 | 2 | 3 | 4 |
|---|---|---|---|---|---|
| sum_(v_2(t)=j) w_|t| | 2906 | 2048 | 1024 | 512 | 200 |

(The standalone verifier separately checks these sums.) Hence

2906α_0+2048α_1+1024α_2+512α_3+200α_4 ≤4131.             (2)

This is an all-order inequality. It is not an enumeration of cyclic groups through some n.

## 3. The already-known high-odd branch, with an elementary proof

We use the following special case of Ranđelović's Proposition 2, arXiv:2611.23559v1 (17 November 2026): if A⊆Z_(2^n) is cube-free and α_0>2/3, then |A|≤5N/8. For completeness, here is its elementary proof specialized to the groups needed here. This branch is a published input and receives no separate novelty credit.

For n=1, absence of 0 gives |A|≤1≤5N/8. Suppose n≥2. Write c=α_0 and let C be the odd part of A.

First,

2c+α_1≤2.                                               (3)

Indeed, none of the triples (x,2x,3x), with x odd, has all entries in A. Counting entries and averaging over odd x gives (3): x and 3x are each uniform on L_0, and 2x is uniform on L_1.

If there were an even e with e,2e∈A, the three translates requiring z,z+e,z+2e∈C would have a common odd z, since c>2/3. The generators z,e,e would then give a cube in A. Thus there is no such even e. Doubling between adjacent even valuation layers consequently gives

α_j+α_(j+1)≤1  (j≥1),                                  (4)

where the extended zero layers make the final cases automatic.

If 2/3<c≤3/4, put B=2|A∩2Z_N|/N, the density of the even part in its subgroup. Then B=sum_(j≥1) α_j/2^j, a finite sum after the zero extension. The exact identity

3B−α_1 = sum_(j≥1) (α_j+α_(j+1))/2^j

and (4) show 3B−α_1≤1. Combining with (3),

|A|/N=(c+B)/2 ≤ c/2+(3−2c)/6 =1/2+c/6≤5/8.

If c>3/4, the even part cannot contain a Schur triple u,v,u+v: the four odd translates requiring z,z+u,z+v,z+u+v∈C would intersect, giving the cube generated by z,u,v. Thus the even part is sum-free. In particular its intersection with the subgroup 4Z_N has size at most N/8. A sum-free subset S of a finite group H has size at most |H|/2, because if s∈S then S and s+S are disjoint; the empty case is automatic. Finally (3) gives

|C|+|A∩L_1|=(N/4)(2c+α_1)≤N/2.

Adding the deep part yields |A|≤N/2+N/8=5N/8. This proves the high-odd branch.

## 4. The new induction closes every remaining case

We prove |A|/2^n≤5/8 by strong induction on n≥0. At n=0 the group is {0}, so A is empty. For n≥1, the high-odd branch settles α_0>2/3. We may therefore assume

α_0≤2/3.                                                (5)

Let γ be the density of A inside the subgroup 16Z_N, and β its density inside 32Z_N. Each of these subgroups, unless trivial, is isomorphic to a strictly smaller cyclic 2-group; cube-freeness is preserved by the isomorphism. The induction hypothesis therefore gives

γ≤5/8,   β≤5/8.                                        (6)

If either subgroup is {0}, its density is zero and (6) is still valid. Splitting 16Z_N into its elements of exact valuation 4 and its doubled subgroup gives

α_4+β=2γ≤5/4.                                          (7)

For n≤4 all three quantities in this identity are zero, so there is no small-order exception.

The exact density decomposition, including zero-extended layers, is

8192 |A|/N =4096α_0+2048α_1+1024α_2+512α_3+256α_4+256β.

Subtract the left-hand side of (2). By (2), (5), (6), (7),

8192 |A|/N
 ≤4131+1190α_0+56α_4+256β
 =4131+1190α_0+56(α_4+β)+200β
 ≤4131+1190·(2/3)+56·(5/4)+200·(5/8)
 =15358/3
 <5120=8192·(5/8).

Thus in this branch we actually have

|A|/N≤7679/12288=5/8−1/12288.

This finishes the induction and proves the universal upper bound. No assumption about an unknown range of n remains.

## 5. Equality construction

For n≥3, take the preimage modulo 8 of

R={1,3,4,5,7}.

It has exactly 5·2^(n−3) elements. It is cube-free already in Z_8. Indeed 0∉R, and its only even member is 4. Two even generators would sum to 0. If there is one even generator 4 and two odd generators, their even pair-sum would have to be 4, making the total sum 0. If all three generators a,b,c are odd, all three pair-sums would have to be 4 modulo 8; subtracting two such equalities from the third forces 2a≡4 mod 8, impossible for odd a. These cases include repeated generators. Any cube in the preimage would project to one in R. Hence equality is attained, completing the source conjecture. ∎


## Prior art and significance

A fresh bounded literature and registry check was performed on 20 November
2026, completed by 20:05 UTC. Long–Wagner's arXiv record still lists only v1;
Meng's arXiv record lists v1 and v2 (latest 3 April 2025); Ranđelović's record
still lists only v1 (17 November 2026). No full earlier resolution was found.

The closest prior work is Ranđelović, *3-Cube-Free Sets in Cyclic Groups*,
[arXiv:2611.23559v1](https://arxiv.org/html/2611.23559v1).
Its Proposition 2 proves the five-eighths bound when the odd-layer density is
at least two-thirds; its general theorem improves two-thirds by an absolute
positive constant when the group order is not divisible by three. It leaves
the intermediate odd-density interval open. Section 3 above reproves the
strict high-odd case needed here.

Meng, *On Cube-Free Problems*, [Electronic Journal of Combinatorics 33(1)
(2026), P1.16](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v33i1p16/pdf/),
proves the two-thirds bound and still discusses five-eighths as conjectural.
The journal text, including its Section 3, was read in this refresh.
The public Prove2Me high-odd theorem and the October Q1961 attempt notes also
supply partial results, not the full bound. A separate CoPEER search hit
concerns cardinalities of layered constructions, not their extremality.

The arXiv recent listing (16–20 November), latest-updated keyword API search,
Semantic Scholar citation list, supplied Principia list, four local registry
clones, GitHub code searches, and omega issue and PR searches yielded no prior
full proof. Local clones and search indexing can lag. OpenAlex returned HTTP
429; the source journal host returned HTTP 403; the WPI thesis body remained
inaccessible. Those bodies were not read or inferred to be unchanged.
These bounded searches establish no absolute priority guarantee. Detailed
queries and results are in FINAL-REVIEW-340621.md and its accompanying logs.

The high-odd argument above reproduces a published branch and receives no
novelty credit. The proposed new ingredient is the certified 36-coefficient
weighted inequality matched to inductive bounds on two proper subgroups.
Uniform fractional occupancy 2/3 satisfies every raw cube-edge inequality,
yet has weight 4460, exceeding 4131. The delivered certificate uses integrality
beyond a single global nonnegative combination of those inequalities.
The method still uses standard integer optimization and finite dilation ideas.
A specialist and root must assess significance independently. This packet
certifies neither novelty nor campaign acceptance.

## Formal architecture and reproducibility

All Lean sources are in src/ and reproduced byte for byte in
LEAN-SOURCE-APPENDIX.md in import order. The finite lemma and inherited
averaging chain are copied unchanged. The induction is generalized to every
finite cyclic additive group of order 2^n. Pullback along a subgroup inclusion
preserves the seven-sum predicate, and the subgroup's cardinality is
2^(n−min n j). Thus no unformalized cyclic-group equivalence is assumed.

The proof data are declarations checked by the ordinary Lean kernel.
The single checker's soundness is proved semantically; no optimization
program is trusted. The supplied generators and exact JSON certificate
are retained. The independent Python verifier is an extra check, not a premise.

Every module is compiled with check32.sh, then its olean checked with
checker32.sh under the pinned 32 GiB runner and its stricter RSS/CPU guards.
Only propext, Classical.choice, and Quot.sound are permitted.
REPORT.md and the source-bound receipt manifest give the actual results.
The final axiom reports, source hashes, resource receipts and endpoint
statements are recorded in REPORT.md and logs/receipt-manifest.json.
