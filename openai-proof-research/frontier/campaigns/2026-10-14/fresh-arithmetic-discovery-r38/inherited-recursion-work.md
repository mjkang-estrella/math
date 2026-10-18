> Historical working record. This status marker was added after author proof
> completion; the original text below is retained. Its unresolved/no-nominee
> status is superseded by `candidate205m.md`, pending independent gates.

# T205M inherited-multiplicity work (active, not sealed)

This work follows the first honest scope freeze in `scope205m.md`.
Full T205M remains unproved. All lemmas below that invoke an induction
hypothesis are conditional propagation lemmas, not stand-alone resolutions.
The source/primary credits in `exploratory-screen-205.md` remain operative.

## 1. A stronger asymmetric invariant

For h≥5 let E_h consist of

    T_h=(N_h), S_h=(1^N_h),
    H_h=(h,1^(N_h−h)), J_h=(h,2,1^(N_h−h−2)).

Proposed invariant: R_h(ν)≥h−1 for ν outside E_h, with R_h the exact,
untransposed max-of-quotients recursion of the exploratory report.
This is verified by exact computation at h=5,6,7 only. At those h the two
nonlinear exceptions have R_h(H_h)=1, R_h(J_h)=h−2. Their transposes
have sufficient full-square bounds. Thus this invariant would imply the
frozen target after the small cases; it is stronger than necessary.

The induction tests use the hypothesis at h=m−1,m−2, not a claim that
it has been proved there for arbitrary h. They give every nonexceptional
predecessor weight h−1 and every exceptional predecessor weight 1.

## 2. Uniform propagation for first row greater than m

Assume m≥7 and the proposed invariant at m−1 and m−2. Let λ⊢N_m have
λ_1>m, and suppose λ is not a one-row partition.

### 2.1 Nonrectangles

The number of horizontal m-strip predecessors is the coefficient of x^m in
∏_i(1+x+⋯+x^(λ_i−λ_(i+1))). This follows from the interlacing
λ_i≥ν_i≥λ_(i+1): the removed amount in row i ranges independently from
0 to λ_i−λ_(i+1). If λ is not a rectangle, at least two factors have
positive degree. Every coefficient of their product at an index strictly
between zero and the total degree is at least two. Here 0<m<λ_1, so
there are at least two predecessors.

At least one predecessor lies outside E_h, h=m−1≥6. Indeed:

* If T_h is a predecessor, Pieri forces λ to have at most two rows.
  None of S_h,H_h,J_h then fits in λ, since their lengths exceed two.
* If S_h is a predecessor, Pieri forces λ to be a hook. Its two possible
  predecessor first-row lengths are consecutive. The only other exceptional
  hook is H_h, whose first-row length h is not consecutive to 1. J_h does
  not fit in a hook. Thus not every predecessor can be exceptional.
* The remaining possibility is that distinct predecessors are H_h and J_h.
  Their simultaneous interlacing inequalities force λ_3≤1. Modify J_h by
  moving its row-two final cell to the end of its first row, obtaining
  ν'=(h+1,1^(N_h−h−1)). This is still an interlacing predecessor: its first
  row h+1 fits below λ_1>m=h+1 and above λ_2≤h; its second row 1 lies
  between λ_2 and λ_3; all subsequent entries agree with J_h. It is
  outside E_h because its first row is h+1 and its leg is nonempty.

Therefore the one-band multiplicity sum is at least (m−2)+1=m−1.

### 2.2 Rectangles

Let λ=(a^b), a≥m+1 and b≥2. The two band partitions
η_1=(m+1,m−2) and η_2=(m,m−1) have size 2m−1 and fit in λ.
Their rotated complements are distinct predecessors

    ν_1=(a^(b−2),a−m+2,a−m−1),
    ν_2=(a^(b−2),a−m+1,a−m),

omitting zero final parts. The rectangular-complement LR identity gives
c_(ν_i,η_i)^λ=1. Both ν_i lie outside E_(m−2). If b≥3 their first row
is a>m−2 and they have at least two rows, excluding all four exceptions.
If b=2, their lengths are at most two, excluding S,H,J; and they are not
one-row because a=m+1 with b=2 would imply m=4 from N_m=2(m+1).
Thus the two-band sum is at least 2(m−3)≥m−1.

This proves conditional propagation for ALL λ_1>m other than T_m.
It does not establish the invariant on narrow diagrams.

## 3. The critical narrow family has an LR coefficient two

The coarse predecessor-count induction test through m=9 leaves exactly
λ=(m,m−2,1^(N_m−2m+2)) outside E_m. Put h=m−2 and n=N_h;
then λ=(m,m−2,1^(n+1)). Take ν=(2,1^(n−2)), which is outside E_h
for m≥7. The skew diagram λ/ν is the disjoint union of a bottom column
of four boxes and the two-row skew diagram D=(m,m−2)/(2,1).
Jacobi–Trudi and the two-row Pieri formula give, for m≥5,

    s_D = h_(m−2)h_(m−3) − h_m h_(m−5)
        = s_(m−1,m−4) + s_(m−2,m−3).

Multiplication by e_4 has, for each displayed two-row type (u,v), a
constituent (u+1,v+1,1,1), obtained by adding one cell to each of four
rows. Each coefficient is one, both resulting types have four rows, and
they are distinct. Therefore

    ∑_(ℓ(η)≤4)c_(ν,η)^λ ≥ 2.

The two-band sum is at least 2R_h(ν)≥2(m−3)≥m−1 under the induction
hypothesis. This pays the family uniformly, not merely at the computed
orders. It is a classical LR computation used inside the proposed new
uniform propagation proof, not a separately nominated result.

## 4. The still-unpaid narrow combinatorial lemma

The following sufficient lemma would close the induction for m≥7:
for every λ⊢N_m with λ_1≤m, λ outside E_m and outside the family in §3,
either

(A) K_(λᵗ,ρ_m)≥m−1, or
(B) there are at least two partitions ν⊢N_(m−2), ν outside E_(m−2),
    with λ_i≥ν_i≥λ_(i+4) for all i.

The interlacing condition means λ/ν is a union of at most four horizontal
strips. Repeated Pieri supplies at least one ≤4-row LR constituent for
each such ν, so (B) gives the needed 2(m−3) bound. The lemma is verified
exhaustively through m=9, but is NOT proved. The exact Kostka-number
calculation is only a finite diagnostic, not its proof.

A helpful identity is full-column deletion:
if λ_1=m, then K_(λᵗ,ρ_m)=K_((λ_2,λ_3,…)ᵗ,ρ_(m−1)). The first full
column of every semistandard tableau is 1,…,m, and deleting it subtracts
one from every content count. In particular, long first rows m,m−1 may
force small Kostka numbers even at arbitrarily large m. There is no
uniform lower bound from dominance positivity alone.

## 5. New operative primary comparison: Kirillov

Read the complete ten-page arXiv:hep-th/9304099v2, Generalization of the
Gale–Ryser theorem, including the maximal configuration, equations
(0.1),(1.4),(2.1), and the perturbations in the proof of Theorem 2.1.
This is a stronger relevant quantitative comparator than multiplicity-one
metadata. With λ denoting our original Specht label, its maximal-configuration
bound specializes, when λ is dominated by ρ_m, to

    K_(λᵗ,ρ_m) ≥ ∏_(j=1)^(λᵗ_2)
       binom(D_j+λ_j−λ_(j+1), λ_j−λ_(j+1)),
    D_j=∑_(i≤j)((ρ_m)_i−λ_i).

The diagnostic uses that actual formula, not a guessed weight-multiplicity
bound. It is weaker than the exact Kostka number in some narrow rectangular
and nearly rectangular families; for λ=(2^(N_m/2)) it is only 1 when this
partition exists. Thus the maximal configuration alone does not close (A).
The paper's other configurations/perturbations may provide the needed
quantitative bridge; that work is still active. Any use must be credited
as the published rigged-configuration operation, not a new construction.
