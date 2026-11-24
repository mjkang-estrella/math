# A sharp linear bound for monochromatic Thue–Morse progressions

## Abstract

For every positive difference d and every nonnegative starting point, a monochromatic arithmetic progression in the Thue–Morse sequence has at most d+5 terms. The maximum is d+5 exactly for d=2^k−1 with even k≥2. This proves Conjecture 3 of Sobolewski, arXiv:2204.05287. The proof puts a large binomial support inside a forced-change set and uses multiplicity at 1 over F₂ to bound its cyclic span. An affine rigidity argument and three obstruction families exclude every other equality case. A Lean 4 certificate includes the source's uncapped extended-natural infimum and supremum, their bridge to monochromatic progressions, and both clauses of the conjecture.

## Source statement, definitions, and conventions

The primary source is Bartosz Sobolewski, *On monochromatic arithmetic progressions in binary words associated with pattern sequences*, [arXiv:2204.05287v2](https://arxiv.org/pdf/2204.05287v2), 17 July 2023. In §1, printed pages 1–2, the source describes **t** = (tₙ)ₙ≥₀ by tₙ = s₂(n) mod 2, where s₂ is the binary sum-of-digits function (paraphrased here). The quotations below reproduce its progression and length conventions, with mathematical typography restored.

Its monochromatic progressions are:

> “progressions n, n + d, . . . , n + ld such that tₙ = tₙ₊d = · · · = tₙ₊ld.”

The source then specifies the length function:

> “Here and in the sequel we let Aₜ(n, d) denote the maximal length of a monochromatic arithmetic progression in **t** of difference d starting at n, that is,
> Aₜ(n, d) = inf{l ≥ 1 : tₙ₊ld ≠ tₙ}.”

On printed page 2 it says “More precisely, define” and displays

> Aₜ(d) = supₙ∈ℕ Aₜ(n, d).

The initial arXiv v1 introduction instead printed a supremum over indices whose sampled letter equals the initial letter, without requiring the intervening letters to match. That expression does not define a monochromatic-run length. The v2 and journal definitions correct it to the infimum above; throughout this paper we follow those corrected definitions. The text of Conjecture 3 is unchanged across the versions.

The corresponding general-pattern definition explicitly allows infinite values. We interpret the empty infimum as infinity, and take both infimum and supremum in ℕ∞. No finite cutoff enters the definitions.

The source's displayed sample progression through n+ld has l+1 terms. In the subsequent *definition of Aₜ(n,d)*, however, l is the index of the **first differing** term. Thus when that first index is l, the matching terms have indices 0,…,l−1, and their number is l, not l+1. Our `Mono n d L` therefore means L matching terms. This is exactly the convention of the source's length function and supplementary table; no shift is made.

These source definitions are represented in Lean, next to their mathematical counterparts, as follows. `TmCore.F` is the abbreviation `ZMod 2`:

```lean
def tm (n : ℕ) : F := ((Nat.digits 2 n).sum : F)
def Mono (n d L : ℕ) : Prop :=
  ∀ i : ℕ, i < L → tm (n + i * d) = tm n
noncomputable def Atn (n d : ℕ) : ℕ∞ :=
  ⨅ (l : ℕ) (_ : 1 ≤ l ∧ tm (n + l * d) ≠ tm n), (l : ℕ∞)
noncomputable def At (d : ℕ) : ℕ∞ := ⨆ n : ℕ, Atn n d
```

Zero-based indexing includes n=0 and t₀=0. Equality of residues in ZMod 2 is equality of the source's binary colours. The following bridge is proved for **all** n,d,L, with no positivity or finiteness premise:

```lean
natCast_le_Atn_iff (n d L : ℕ) :
  (L : ℕ∞) ≤ Atn n d ↔ Mono n d L
```

Indeed, every differing positive index must be at least L exactly when all indices below L match. Index zero always matches. This handles L=0 and an empty set of differing indices as well.

On printed page 25, §6, the conjecture reads:

> **Conjecture 3.** For all d ≥ 1 we have
> Aₜ(d) ≤ d + 5.
> Moreover, equality occurs if and only if d = 2ᵏ − 1 for some even k ≥ 2.

MathDB record 354240 agrees. We prove the conjecture with all starting points and both colours, not only progressions starting at zero.

## Prior work and scope

Morgenbesser, Shallit and Stoll, *Thue-Morse at multiples of an integer*, J. Number Theory 131 (2011), 1498–1512, prove Aₜ(0,d)≤d+4 and classify sharpness; their start is fixed at zero (Sobolewski, Theorem 1.1). Parshina, *On arithmetic index in the generalized Thue-Morse word*, LNCS 10432 (2017), 121–131, gives the dyadic bound max_{1≤d≤2^k−2} Aₜ(d)≤2^k and the Mersenne values recorded in Sobolewski's Theorem 1.2. Aedo, Grimm, Nagai and Staynova, *Monochromatic arithmetic progressions in binary Thue-Morse-like words*, Theor. Comput. Sci. 934 (2022), 65–80, give another proof of the Mersenne values and Aₜ(2^k+1)=2^k+2 for k≥2 (Sobolewski, Theorem 1.3). These known special-family values are rederived where needed here; none is an assumption of the Lean proof.

Sobolewski's Theorem 1.7 is a general dyadic bound for pattern sequences of pattern length at least two: for differences d<2^k the displayed bound is 2^{k+|v|−ν₂(d)−1}. Its Remark 2 discusses when the same expression extends to the one-letter Thue–Morse pattern. This is not the asserted individual bound d+5. [Joshi and Rust, arXiv:2501.05830v2](https://arxiv.org/abs/2501.05830), study lower bounds, maximal-length fibres and earliest starting positions, including the separate Conjecture 3.8 about first starts. Their results do not assert the present all-d upper bound. These comparisons use Sobolewski's actual statements, Joshi–Rust §§1 and 3.2 in the supplied source text, and the independent review; no new exhaustive literature search is claimed by this packaging lane.

All parity equations in the proof below are in F₂. We use s(n)=tₙ, and write cyclic intervals by their **span**: an interval of span H contains H+1 possible integer residues.

## 1. Binary and polynomial preliminaries

Write s(n)=t(n). If 0≤r<2^e, then

(1) s(2^e m+r)=s(m)+s(r), and s(2^e−1−r)=e+s(r).

Also s(2m)=s(m), s(2m+1)=1+s(m).

There are no three consecutive equal letters of t, since every interval of three consecutive indices contains an aligned pair (2a,2a+1), whose letters differ.

There is no palindromic factor of length five. Indeed, if its center is 2a, equality of the inner pair gives s(a−1)=s(a), and equality of the outer pair gives s(a−1)=s(a+1). If its center is 2a+1, the inner pair gives s(a)=s(a+1), and the outer pair gives s(a−1)=s(a+1). Each case contradicts the absence of three consecutive equal letters. The center of a length-five factor is at least 2, so these indices are nonnegative.

For a nonnegative integer D, let

S_D={z≥0 : every 1-bit of z is a 1-bit of D}.

Factoring (1+X)^D in F₂[X] by the binary digits of D gives

(2) (1+X)^D = ∏_{i: bit_i(D)=1}(1+X^{2^i}) = Σ_{z∈S_D}X^z.

Every subset sum is distinct. For z∈S_D the subtraction D−z has no borrows, so s(z)+s(D−z)=s(D).

## 2. A binomial cube inside each reflection class

For odd c≥3 and ε∈F₂, put N=c−1 and

E_ε(c)={0≤r<c : s(r)+s(N−r)=ε}.

There exist j∈{0,1,2} and D=N−2j such that

(3) j+S_D ⊆ E_ε(c), and D≥c−5.

More precisely:

* If ε=s(N), choose j=0 and D=N.
* If ε≠s(N) and ν₂(N) is odd, choose j=1 and D=N−2.
* If ε≠s(N) and ν₂(N) is even, choose j=2 and D=N−4.

Proof: The first case follows from (2). In the second case D is even; adding j=1 to either z or D−z introduces a separate low 1-bit. In the third case N is divisible by 4 and D is divisible by 4; adding j=2 likewise introduces a separate 1-bit. Thus in either latter case, for r=j+z,

s(r)+s(N−r)=s(z)+s(D−z)=s(D).

If v=ν₂(N), binary subtraction gives

s(N−2) = s(N)+v modulo 2,

and, for v≥2,

s(N−4) = s(N)+v+1 modulo 2.

The designated parity of v makes this equal to 1+s(N). The displayed D's are nonnegative, including N=2 and N=4. This proves (3).

## 3. Multiplicity obstructs compression on a dyadic circle

Let B be a power of two, 0≤D<B, and u odd. If the residue set u(j+S_D) modulo B is contained in a cyclic interval of integer span H<B, then

(4) H≥D.

Here an interval of span H is a set {a,a+1,…,a+H} modulo B, containing H+1 possible residues.

To prove this, work in R=F₂[X]/(X^B−1)=F₂[X]/((X+1)^B). The polynomial

X^{uj}(1+X^u)^D

has support precisely u(j+S_D) modulo B: u is a permutation of the residues, so there is no cancellation. As 1+X divides 1+X^u, its residue class is divisible by (X+1)^D. Multiplying by a power of X to move the containing interval to [0,H] gives a nonzero representative Q of degree at most H. Powers of X are units modulo (X+1)^B, and (X+1)^B is itself divisible by (X+1)^D. Consequently the ordinary polynomial Q is divisible by (X+1)^D. Hence deg Q≥D.

We shall need the following rigidity in the equality case.

**Affine cube rigidity.** Suppose 0<D<B/2, u odd, and uS_D is a translate of S_D modulo B. Put v=ν₂(D). Then

(5) u≡1 or −1 modulo B/2^v.

Proof: Every element of S_D is divisible by 2^v, so the translation is also divisible by 2^v. Divide all residues by 2^v and write M=B/2^v, E=D/2^v. Then E is odd, E<M/2, and for some a, with u reduced to an odd representative 1≤u<M,

(6) (1+X^u)^E ≡ X^a(1+X)^E modulo (X+1)^M.

The derivation X d/dX preserves the ideal ((X+1)^M), since M is a power of two in characteristic two. Differentiate (6), multiply by 1+X^u, substitute (6) again, cancel the unit X^a and the factor (X+1)^{E−1}. We obtain, modulo (X+1)^{M−E+1},

X^u(1+X) = a(1+X)(1+X^u)+X(1+X^u).

Thus, if a is even, X^u+X is divisible by (X+1)^{M−E+1}; if a is odd, 1+X^{u+1} is divisible by that power. The required multiplicity is greater than M/2. For any positive integer h, the multiplicity of X+1 in 1+X^h over F₂ is exactly 2^{ν₂(h)}: factor h=2^b h₀, h₀ odd, and use Frobenius followed by the nonzero derivative of 1+X^{h₀} at 1. If u≠1 in the first case, 0<u−1<M, so the multiplicity is at most M/2. If u≠M−1 in the second case, 0<u+1<M and the same contradiction applies. This proves (5).

## 4. The upper bound for non-Mersenne odd differences

The bound is immediate for a progression of length zero; assume its length L is positive. Let d>1 be odd and let B=2^e be the least power of two exceeding d. Thus B/2<d<B. Set c=B−d, which is odd. In this section c≥3.

Define the forced-change residues

F={0≤r<c : s(r)≠s(r+d)}.

For such r, adding d stays within the same length-B block, so (1) shows that an occurrence of residue r in a progression cannot be followed by another letter of the same color. Reflection in (1) gives

s(r+d)=e+s(c−1−r).

Therefore F=E_ε(c), with ε=1+(e mod 2).

Choose j,D from Section 2 and let u=d^{-1} modulo B. The set F is nonempty. A monochromatic progression of length L cannot have L>B, since its first B transitions would visit every residue modulo B and include a forced change. Its L−1 transition starts omit F. Multiplication by u turns their residues into L−1 consecutive residues of the cyclic group. Hence uF is contained in the complementary cyclic interval, of span B−L.

Since u(j+S_D)⊆uF, Section 3 gives D≤B−L. Thus

(7) L≤B−D≤B−c+5=d+5.

This establishes the desired bound for all odd non-Mersenne differences.

Uniform variant used by the Lean implementation: the bound argument above does not use B/2<d; it only needs odd c≥3 and d+c=B. Thus one may choose any dyadic B≥d+3, obtaining the same bound even for Mersenne differences. The least-block choice is needed below for D<B/2 in the equality analysis. Section 6 supplies odd-exponent strictness and the even-exponent attainment construction.

## 5. Equality is impossible in Section 4

Suppose a progression in Section 4 has length L=d+5. Equality must hold at every stage of (7). In particular

(8) ε≠s(N), ν₂(N) is even, j=2, D=N−4=c−5,

and

(9) s(N)=e mod 2.

First assume D>0. The polynomial Q in Section 3 has degree at most D and is divisible by (1+X)^D, so Q=(1+X)^D. Consequently uS_D is a translate of S_D modulo B. We may apply (5), since D<c<B/2.

Write t=ν₂(N), an even positive integer.

### 5.1. The case t≥4

Then ν₂(D)=2. Put M=B/4. Since N≥16 and N+1=c<B/2, M is divisible by 4. Also d=B−N−1≡−1 modulo 4. By (5), d≡±1 modulo M; the plus sign is impossible modulo 4. Thus M divides N. Since 0<N<B/2=2M, N=M. Then t=e−2 is even, so e is even, whereas s(N)=1. This contradicts (9).

### 5.2. The case t=2

Now v=ν₂(D)≥3. Put M=B/2^v and E=D/2^v. We have M>2E≥2, so M≥4. The congruence d≡1 modulo M would imply M divides D+6, impossible because ν₂(D+6)=1. Therefore d≡−1 modulo M, and M divides D+4. Since ν₂(D+4)=2, this forces M=4, E=1. Hence

(10) D=2^v, B=4D, N=D+4, d=3D−5.

Here s(N)=0 and e=v+2, so (9) forces v even. Thus v≥4.

If v=4, then (B,c,d,u)=(64,21,43,3). The residues 2,6,18 all lie in F (directly, their reflection parities against N=20 are 1). Their u-images are 6,18,54 modulo 64. The gaps are 12,36,16, so no cyclic interval of span D=16 contains them: the minimum span is 64−36=28. This contradicts the containing arc of span D.

If v≥6, put m=D/8≥8. The set F contains every r=8h+6, 0≤h<m. Indeed

s(8h+6)=s(h),
s(N−8h−6)=s(8(m−1−h)+6)=s(m−1−h)=1+s(h),

because m=2^{v−3} and v−3 is odd. All these residues are therefore forced changes. Their u-images lie in an interval of span D. Removing their common residue modulo 8 and dividing by 8 shows that

{0,u,2u,…,(m−1)u} modulo 4m

lies in an interval of span at most m. Choose representatives in this interval. Every successive difference is the unique representative of u modulo 4m in [−m,m], since 2m<4m. If this integer is h, then (m−1)|h|≤m. Because m≥3 and u is a unit, h=±1. Therefore d≡±1 modulo 4m=D/2. But d≡−5 modulo D/2, and D/2≥32 divides neither 4 nor 6. Contradiction.

### 5.3. The case D=0

Here c=5, N=4, and (9) says that e is odd. Since c<B/2, B≥32. A direct calculation gives F={2}. If L=B=d+5, all B−1 transition residues must avoid 2. Their unique missing residue is the one immediately before the start. Therefore the starting residue is 2+d=B−3. Write the start as n=Bm+(B−3).

If B=32 (d=27), the progression indices i=5,7,8 have quotient/remainder pairs, on division by B,

(m+5,4), (m+6,26), (m+7,21).

All three remainders have binary parity 1. Monochromaticity forces three consecutive letters t(m+5),t(m+6),t(m+7) to agree, a contradiction.

Otherwise e≥7 and B≥128. Use i=6,7,8. Their quotients are m+6,m+7,m+8 and their remainders are B−33,B−38,B−43. By (1), these have parities 1+s(32),1+s(37),1+s(42), all zero. Again three consecutive letters of t would agree. Contradiction.

This excludes a progression of length d+5 for every non-Mersenne odd d. Section 4 bounds all progression lengths by the finite integer d+5. The nonempty set of attained integer lengths therefore has a largest element; excluding d+5 makes this maximum, and hence A_t(d), strictly smaller than d+5.

## 6. Mersenne differences, including the equality construction

Let d=B−1, B=2^e.

If e is odd, residue 0 is a forced change, since s(0)=0 and s(B−1)=1. The same orbit argument gives A_t(d)≤B=d+1<d+5.

Suppose e is even, so e≥2. The uniform larger-block argument of Section 4 proves the upper bound B+4: apply it to the dyadic block 2B, for which c=2B−d=B+1≥3. This is the route used by `TmOrbit.thueMorse_progression_bound`. The known Mersenne formula is not assumed.

For attainment, take

(11) n=3B²−B+1.

The B+4 indices i=0,…,B+3 all give color 0. For i=0, the quotient/remainder pair is (3B−1,1), whose parities are 1 and 1. For i=1 it is (3B,0), whose parities are 0 and 0. For i=2+a, 0≤a<B, it is (3B+a,B−1−a), whose two parities are both s(a). Finally, at i=B+2 the pair is (4B−1,B−1), with parities 0,0; at i=B+3 it is (4B,B−2), with parities 1,1. Thus A_t(B−1)=B+4=d+5 for every even e≥2.

For d=1, absence of triples gives A_t(1)≤2, so it is not an equality case.

## 7. Even differences and conclusion

For every n,d≥0,

s(n+2id)=s(⌊n/2⌋+id)+(n mod 2).

Thus `Mono n (2d) L` holds exactly when `Mono (⌊n/2⌋) d L` holds; conversely a start can be doubled. In particular the source suprema satisfy A_t(2d)=A_t(d). Write any positive d as 2^a b with b odd. The odd-difference result gives

A_t(d)=A_t(b)≤b+5≤d+5.

If a>0 the last inequality is strict. The odd equality cases were proved in Sections 5–6 to be exactly b=2^e−1 with even e≥2. This is precisely the source conjecture, including all small parameters.

## 8. Literal Lean endpoints and the source maximum

The uncapped source quantity is used in the first endpoint, in namespace `Campaign354240Literal`:

```lean
theorem sobolewski_conjecture_three (d : ℕ) (hd : 1 ≤ d) :
    At d ≤ ((d + 5 : ℕ) : ℕ∞) ∧
      (At d = ((d + 5 : ℕ) : ℕ∞) ↔
        ∃ k : ℕ, 2 ≤ k ∧ Even k ∧ d = 2 ^ k - 1)

theorem sobolewski_conjecture_three_bundled (d : ℕ) (hd : 1 ≤ d) :
    (∀ n L : ℕ, Mono n d L → L ≤ d + 5) ∧
      ((∃ n : ℕ, Mono n d (d + 5)) ↔
        ∃ k : ℕ, 2 ≤ k ∧ Even k ∧ d = 2 ^ k - 1)
```

The reviewed modules contain an auxiliary `Campaign354240.A`, the greatest attainable length searched up to d+5. Its bound alone would be tautological. We do not identify this auxiliary definition with the source by stipulation. `Campaign354240.A_is_maximum` proves both its attainment and its bound on **every** actual progression. The new wrapper uses that theorem and the unconditional infimum bridge to prove

```lean
At_eq_maximum (d : ℕ) (hd : 0 < d) :
  At d = (Campaign354240.A d : ℕ∞)
```

For the upper-bound clause the wrapper directly transports `TmOrbit.thueMorse_progression_bound` through the infimum/supremum bridge. For equality it uses the proved maximum bridge and the reviewed equality classification. The natural-number forms d+1=2^k and d=2^k−1 are proved equivalent here, using positivity of 2^k. No numerical experiment enters these arguments.

As sanity theorems for the uncapped definition, the certificate proves At(1)=2, At(2)=2 and At(3)=8, agreeing with the first three rows in the supplement's column “1”. For differences 1 and 2 the upper bound is the no-triples lemma, with the halving identity for 2; explicit two-term witnesses are checked by ordinary `decide` after a finite index split. The value at 3 follows from the equality theorem with k=2.

## 9. Formalization and significance

The 27 reviewed modules are unchanged, byte for byte; only `TmUncapped.lean` is added. The appendix contains every module in import order. Lucas support is implemented by the binomial-coefficient halving recurrence in `TmReflection`; cyclic polynomial reduction and compression are in `TmCyclic` and `TmCube`. `TmFrobenius`, `TmRigidity` and `TmEquality` implement the derivative argument, forcing even translations and descending through Frobenius squares before applying primitive odd-degree rigidity. `TmArcBridge` and `TmQuantitative` connect those lemmas to actual progression transitions. The three equality obstructions are in `TmValArithmetic`, `TmFamily` (including its finite v=4 case and its infinite v≥6 case), and `TmC5`. `TmAttainment` constructs the even-exponent Mersenne examples; `TmFinal` assembles the classification. The proof uses the uniform larger-block variant for its universal bound, rather than needing a special Mersenne upper-bound theorem.

Every one of the 28 modules is compiled afresh and separately kernel-checked using the supplied 32 GiB runner and pinned Lean 4.34.1/Mathlib dependencies. Both literal endpoints have exactly the transitive axioms `propext`, `Classical.choice`, and `Quot.sound`. There are no additional assumptions, proof holes, or native computation certificates. The report records receipts, source comparison, hashes and verification limits.

The mathematical contribution claimed is the sharp all-start, all-d saving from the dyadic bound to d+5, and the exclusion of all other equality cases. The dyadic identities, the special Mersenne values, and their equality family were known. The useful new mechanism in this proof is the high multiplicity of a binomial polynomial on the forced-change set, invariant under odd multiplication and rotation. Its affine equality rigidity makes the sharp classification possible. The polynomial trick is elementary once identified, and a specialist may regard parts of the argument as standard. The supplied cross-model review found no public proof or short deduction from the cited results; that bounded audit is evidence, not a worldwide priority guarantee. This lane corrects the formal endpoint and prepares a certificate packet; it does not claim independent campaign credit for that correction. Independent final replay, updated prior-art adjudication and acceptance remain root decisions. Nothing has been submitted or published.
