# Littlewood admissibility with prescribed disk-root counts

## Abstract

A Littlewood polynomial of degree $n$ has all $n+1$ coefficients in $\{-1,1\}$. A pair $(k,n)$ with $1\le k\le n-1$ is Littlewood-admissible if some such polynomial has no zeros on the unit circle and exactly $k$ zeros, counted with multiplicity, in the open unit disk. Hare and Jankauskas (arXiv:1910.13994, Conjecture 2.13) conjectured that the only inadmissible pairs are $(2,n)$ and $(n-2,n)$ with $n\equiv1\pmod 6$ and $n\ge13$. They proved this inadmissibility for $n\le31$ by exhaustive computation. We prove the conjecture in full.

The new content has two parts. First, the listed pairs are inadmissible for every such $n$. The proof is computer-assisted: a Schur–Cohn inertia criterion prunes a tree of coefficient prefixes, and a finite exact certificate with a period-12 induction covers all degrees. Second, an explicit even-$k$ family supplies the existence cases that the source's theorems leave open.

The classification is stated and proved in Lean 4 with Mathlib, as the theorem `Littlewood.hare_jankauskas_2_13_final`. The exclusion half, including the whole certificate, is checked in the Lean kernel, and so is the even-$k$ family. Five results printed and proved in the source are links outside Lean: they enter as explicit hypotheses, transcribed literally. They are Proposition 2.6 (attributed there to Mukunda), Theorems 2.7, 2.8 and 2.9, and Corollary 2.11. All of this work was done by AI systems, and no human has checked it.

## Statement and definitions

Hare and Jankauskas, Conjecture 2.13 in arXiv:1910.13994v1 (MathDB 344334).

> Pairs $(2,n)$ and $(n-2,n)$, where $n\equiv 1\pmod{6}$ and $n\ge 13$, are the only non–trivial Littlewood–inadmissible pairs.

The Littlewood part of equation (1.2) reads

> $\mathcal L_n=\{f(z)\in\mathbb Z[z]:a_j\in\{-1,1\},\ 1\le j\le n\}.$

The index range omits the constant coefficient $a_0$. This is a typo. The source's own enumeration in §8.4 uses words of signs including the constant term, and here every coefficient from $a_0$ to $a_n$ is required to be $\pm1$. The source confirms this reading in three more places. Its Table 6.4 is "normalized by $a_0=a_1=1$". Its §4 treats $a_0,\dots,a_n$ as $n+1$ random signs. Its 2 GB data file for $n=31$ matches $2^{32}/4$ records of two bytes, which is one record for each $\pm1$ word of length 32 up to $f(z)\mapsto\pm f(\pm z)$. The literal reading would also contradict the source's Theorem 2.12. With $a_0=0$ allowed, $z\,g(z)$, for a $\pm1$ polynomial $g$ of degree 12 with one zero inside and none on the circle, would realize $(2,13)$.

The source defines the root counts from the factorization $f(z)=a_n(z-\alpha_1)\cdots(z-\alpha_n)$ in equation (1.3).

> $U(f):=\#\{j,\ 1\le j\le n:\ |\alpha_j|=1\},$  
> that counts the unimodular zeros of $f(z)$ in Eq. (1.3). For simplicity, each zero will be counted the number of times it is repeated in equation (1.3)

> $N(f):=\#\{j,\ 1\le j\le n:\ |\alpha_j|<1\}$  
> that counts (with multiplicities) the number of zeros of a polynomial $f(z)\in\mathbb C[z]$ in equation (1.1) in the open unit disk.

The relevant sentences of Definition 1.1 read

> A pair $(k,n)\in\mathbb N^2$, where $1\le k\le n-1$, will be called a valid pair.

> Likewise, a valid pair $(k,n)\in\mathbb N^2$ is Littlewood–admissible if there exist a polynomial $f(z)\in\mathcal L_n$, such that $U(f)=0$, $N(f)=k$. We say that this polynomial $f(z)$ realizes that particular pair $(k,n)$.

The following Lean definitions interpret those sentences with the corrected index range. The multiset of roots retains repeated roots. The pointwise condition `NoCircle` expresses $U(f)=0$ because the polynomial has nonzero leading coefficient and every complex root is represented in that multiset. [Hare–Jankauskas, arXiv v1](https://arxiv.org/abs/1910.13994)

```lean
def IsLittlewood (P : Polynomial ℤ) (n : ℕ) : Prop :=
  P.natDegree = n ∧ ∀ j ≤ n, P.coeff j = 1 ∨ P.coeff j = -1

def NoCircle (P : Polynomial ℂ) : Prop :=
  ∀ z : ℂ, ‖z‖ = 1 → P.eval z ≠ 0

noncomputable def insideCount (P : Polynomial ℂ) : ℕ := by
  classical
  exact (P.roots.filter (fun z => ‖z‖ < 1)).card

def Admissible (k n : ℕ) : Prop :=
  ∃ P : Polynomial ℤ, IsLittlewood P n ∧ NoCircle (P.map (Int.castRingHom ℂ)) ∧
    insideCount (P.map (Int.castRingHom ℂ)) = k
```

### The Lean endpoint

```lean
theorem Littlewood.hare_jankauskas_2_13_final
    (h26 : Mukunda_2_6) (h27 : HareJankauskas_2_7)
    (h28 : HareJankauskas_2_8) (h29 : HareJankauskas_2_9)
    (h211 : HareJankauskas_2_11)
    (k n : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n - 1) :
    ¬ Admissible k n ↔ (13 ≤ n ∧ n % 6 = 1 ∧ (k = 2 ∨ k + 2 = n))
```

The theorem has no other hypotheses. The Schur–Cohn root count, the coprimality lemma, the four finite certificate tables and both root counts for the even-$k$ family are discharged by theorems inside Lean. The five hypotheses are the following source results, quoted from arXiv:1910.13994v1, §2. Fractional bounds are written with cleared denominators.

> Proposition 2.6 (Mukunda). Pairs $(1,n)$ and $(n-1,n)$, $n\ge2$ are Littlewood–admissible.

> Theorem 2.7. If $n\ge3$ and (1) $n\le12$, or (2) $n\not\equiv1\pmod 6$ then the pairs $(2,n)$ and $(n-2,n)$ are Littlewood–admissible.

> Theorem 2.8. Every pair $(k,n)$, $(n-k,n)\in\mathbb N^2$ with $3\le k\le11$, $n\ge k+3$ is Littlewood–admissible.

> Theorem 2.9. Let $n\ge6$ be even. Then, for every odd $k\in[3,n-3]$ and every even $k\in[n/3,2n/3]$, the valid pair $(k,n)$ is Littlewood-admissible. Likewise, suppose that $n>6$ is odd. Then, for every odd $k\in[3,n/2]$ and every even $k\in[n/2,n-3]$, the valid pair $(k,n)$ is Littlewood-admissible.

> Corollary 2.11. Let $n\ge2$. For every even $k\in[n/2,2n/3]$ and for every odd integer $k\in[3,n/2]$, one of the polynomials $h(z)\in\mathcal L_n$ described in Theorem 2.10 satisfies $N(h)=k$, $U(h)=0$.

Theorem 2.10 of the source describes $h$ by the coefficient pattern $(+-+)^m+(-)^l$ of degree $3m+l$, where $m\ge1$ and $l\ge0$. The Lean witness `LittlewoodFamilies.witness LittlewoodFamilies.oddWords (-1) m (n+1)` is exactly this word.

```lean
def Mukunda_2_6 : Prop :=
  ∀ n : ℕ, 2 ≤ n → Admissible 1 n ∧ Admissible (n-1) n

def HareJankauskas_2_7 : Prop :=
  ∀ n : ℕ, 3 ≤ n → (n ≤ 12 ∨ n % 6 ≠ 1) → Admissible 2 n ∧ Admissible (n-2) n

def HareJankauskas_2_8 : Prop :=
  ∀ k n : ℕ, 3 ≤ k → k ≤ 11 → k+3 ≤ n → Admissible k n ∧ Admissible (n-k) n

def HareJankauskas_2_9 : Prop :=
  (∀ k n : ℕ, 6 ≤ n → n % 2 = 0 →
    ((k % 2 = 1 ∧ 3 ≤ k ∧ k ≤ n-3) ∨
      (k % 2 = 0 ∧ n ≤ 3*k ∧ 3*k ≤ 2*n)) → Admissible k n) ∧
  (∀ k n : ℕ, 6 < n → n % 2 = 1 →
    ((k % 2 = 1 ∧ 3 ≤ k ∧ 2*k ≤ n) ∨
      (k % 2 = 0 ∧ n ≤ 2*k ∧ k ≤ n-3)) → Admissible k n)

def HareJankauskas_2_11 : Prop :=
  ∀ k n : ℕ, 2 ≤ n →
    ((k % 2 = 0 ∧ n ≤ 2*k ∧ 3*k ≤ 2*n) ∨
      (k % 2 = 1 ∧ 3 ≤ k ∧ 2*k ≤ n)) →
    ∃ m l : ℕ, 1 ≤ m ∧ n = 3*m+l ∧
      let P := LittlewoodFamilies.witness LittlewoodFamilies.oddWords (-1) m (n+1)
      IsLittlewood P n ∧ NoCircle (P.map (Int.castRingHom ℂ)) ∧
        insideCount (P.map (Int.castRingHom ℂ)) = k
```

In the source, Theorems 2.7 and 2.8 are proved with the regular families of its Tables 6.4 and 6.6. Those proofs are computer-assisted: resolvent computations and Boyd's exit-point formula, described in its §8.3. Corollary 2.11 follows from Theorem 2.10, which is proved with Boyd's formula (Boyd, *Duke Math. J.* 44 (1977)) and the source's Lemmas 7.7 and 7.8. Theorem 2.9 follows from Corollary 2.11 by reflection. Proposition 2.6 is quoted from Mukunda (*J. Number Theory* 117 (2006)); its $k=1$ witness is also derived directly in §3 below.

## Proof overview and provenance

The exclusion is computer-assisted. A finite exact certificate and a periodic induction cover all forbidden degrees. The existence argument uses the source’s Proposition 2.6 (Mukunda), Theorems 2.7–2.9, and Corollary 2.11, together with the even-count family proved below. The five source results enter Lean as named hypotheses. The even-count family’s circle and radial root counts are proved in Lean.

Provenance: GPT-6.2 Sol lanes found the proof and wrote the Lean code and this paper. Claude Opus 5.5 lanes reviewed it: a first adversarial review before the Lean work, which supplied the small repair marked in §2, and a final check of the definitions, the source links and this paper. All of this work is AI-generated, and no human has checked it. The packet's REPORT.md records the kernel replay status of the finite tables and the classification endpoint.

For $n\ge1$, the two extreme counts $k=0,n$ are inadmissible because the product of the root moduli is one. Reciprocation interchanges $k$ and $n-k$. It suffices to construct witnesses for $1\le k\le n/2$ and to exclude the stated degrees with $k=2$.

## 1. Two root-counting tools

### Schur–Cohn sign convention

For a degree-$n$ polynomial $P$ with nonzero constant term, let $P^\#(z)=z^n\overline{P(1/\bar z)}$. Form the Hermitian coefficient matrix $H_P$ of
$$
K_P(z,\bar w)
=\frac{P(z)\overline{P(w)}-P^\#(z)\overline{P^\#(w)}}{1-z\bar w}.
$$
This is a polynomial of degree at most $n-1$ in each variable. The numerator vanishes at $z\bar w=1$ as a Laurent polynomial, and division lowers both degrees. In the real case
$$
H_P=L(a)L(a)^{\mathsf T}-L(b)L(b)^{\mathsf T},
$$
where $L(a),L(b)$ are lower triangular Toeplitz matrices with first columns the first $n$ coefficients of $P,P^\#$. This follows by expanding $1/(1-z\bar w)$ as a geometric series.

When $P,P^\#$ are coprime, $H_P$ is nonsingular and its negative index is the number of roots of $P$ inside the unit circle. For completeness, if $P=CD$, then
$$
K_P(z,\bar w)
=C(z)\overline{C(w)}K_D(z,\bar w)
 +D^\#(z)\overline{D^\#(w)}K_C(z,\bar w).
$$
The coefficient maps of multiplication by $C$ on polynomials of degree less than $\deg D$, and by $D^\#$ on polynomials of degree less than $\deg C$, have complementary images. The intersection is zero by coprimality of $C,D^\#$ and the strict degree bounds. This displays $H_P$ as congruent to the direct sum of $H_D,H_C$. Factor $P$ into linear factors and apply induction, using $K_{z-r}=|r|^2-1$. A nonzero scalar factor of $P$ only scales the kernel by its squared modulus. A common root $r$ of $P,P^\#$ makes $K_P(z,\bar r)$ identically zero and gives a nonzero evaluation vector in the matrix kernel. Thus a nonsingular $H_P$ also implies coprimality.

### Boundary dominance with simple cancelled roots

Suppose $F,G$ do not vanish on the unit circle, $|F|\ge|G|$ there, and at each equality point $\zeta$ the integer $N$ satisfies
$$
N>\operatorname{Re}\left(\frac{\zeta F'(\zeta)}{F(\zeta)}
                  -\frac{\zeta G'(\zeta)}{G(\zeta)}\right).
\tag{1}
$$
Then $F+z^NG$ has exactly as many roots in the open disk as $F$. On $|z|=r<1$ close to one, $\log|F/G|-N\log r>0$. Near the equality points this follows from the strictly negative radial derivative at the boundary and its continuity. Off those neighborhoods it follows from the strict boundary inequality and compactness. Rouché's theorem applies on every such circle, giving the root count in the full open disk. Any circle zero of $F+z^NG$ is an equality point. It is simple because there
$$
\zeta(F+z^NG)'(\zeta)/F(\zeta)=
\zeta F'(\zeta)/F(\zeta)-\zeta G'(\zeta)/G(\zeta)-N,
$$
whose real part is negative by (1).

## 2. Explicit block constructions

Write words by concatenating the signs $+$ and $-$. For a finite prefix $w$ of length $L$ and a constant tail sign $\tau\in\{1,-1\}$, put
$$
F(z)=(1-z)\sum_{j<L}w_jz^j+\tau z^L.
$$
For a desired length $N=n+1\ge L$, the corresponding Littlewood polynomial is $(F-\tau z^N)/(1-z)$. Also $F(1)=\tau$ and
$$
F'(1)/F(1)=2\,|\{j<L:w_j\ne\tau\}|.
\tag{2}
$$

For odd $k=2m+1$ take $w=(+-+)^m+$ and $\tau=-1$. For even $k=2m+4$ take $w=(+,-,+,-,-)(++--)^m-$ and $\tau=1$. Both definitions allow $m\ge0$. The prefixes have lengths $3m+1$ and $4m+6$. Each has exactly $k$ signs opposite to its tail, and $n\ge2k$ gives $N\ge L$ and $N>2k$.

Expanding the geometric sums gives $F_m=(A+z^{L_0+pm}B)/D$ as follows.

| Case | $p$ | $L_0$ | $A(z)$ | $B(z)$ | $D(z)$ |
|---|---:|---:|---|---|---|
| Odd | 3 | 2 | $1-z+z^2$ | $-2(1+z)$ | $1+z+z^2$ |
| Even | 4 | 5 | $(1-z)^2(1+2z^2)$ | $2(-1+z+z^3)$ | $1+z^2$ |

### Unit-circle lower bound

For $z=e^{i\theta}$, let $c=\cos\theta$. Scale the moduli of $A,B,D$ by $u=1$ in the odd case and $u=2$ in the even case. Put $a=|A|^2/u^2$, $b=|B|^2/u^2$, and $|D|/u=|s|$. Direct expansion yields the following identities.

| Case | $a$ | $b$ | $s$ | $Q$ in $b-a=sQ$ | $Q^2+s^2-2(a+b)$ |
|---|---|---|---|---|---|
| Odd | $(2c-1)^2$ | $8(1+c)$ | $2c+1$ | $7-2c$ | $32(1-c)$ |
| Even | $(1-c)^2(1+8c^2)$ | $1+4c+4c^2-8c^3$ | $c$ | $6-5c+8c^2(1-c)$ | $32(1-c)^2(1+2c^2+2c^4)$ |

In both rows $Q\ge|s|$ and $Q>0$ on $[-1,1]$. Let $E=Q^2+s^2-2(a+b)$ be the last column. The adversarial reviewer supplied the following step. As $a,b\ge0$ and $b-a=sQ$ with $Q\ge |s|$, if $s\ge0$ then $b\ge s^2$, and if $s<0$ then $a\ge s^2$. Thus $a+b\ge s^2$ and $Q^2\ge 2(a+b)-s^2\ge a+b$. Also
$$
(Q^2-a-b)^2-4ab=Q^2 E\ge0.
$$
These inequalities imply $Q\ge\sqrt a+\sqrt b$, strictly for $c\ne1$. When $s\ne0$, the reverse triangle inequality yields
$$
|F_m(z)|\ge \frac{|\sqrt b-\sqrt a|}{|s|}
=\frac{Q}{\sqrt a+\sqrt b}.
$$
At $s=0$, the same bound follows by continuity. The denominator on the right is positive there by the displayed formulas, and $F_m$ is a polynomial. One can also evaluate the signed prefixes directly at those points. Their blocks repeat with $z^p=1$, giving $F_m(z)=1-2m-(2+4m)z$ at the two odd-family points, where $\operatorname{Re}z=-1/2$, and $F_m(z)=-3+4mz$ at the two even-family points, where $\operatorname{Re}z=0$. Their squared moduli are $7+12m+12m^2$ and $9+16m^2$. Thus $|F_m|>1$ on the unit circle except at $z=1$, where $|F_m(1)|=1$.

### Two roots per additional block

In both rows $|B|>|A|$ on the arc $-\theta_0<\theta<\theta_0$, with $\theta_0=2\pi/p$, and $|A|>|B|$ on the complementary open arc. This follows from $b-a=sQ$. At the transition points $e^{\pm i\theta_0}$, the derivative of $b-a$ in $\theta$ is nonzero, $A,B\ne0$, and $A+z^{L_0+pm}B=0$ for every $m$ because $D=0$ there.

On the inner arc use
$$
\frac{F_m}{F_0}
=z^{pm}\frac{1+z^{-L_0-pm}A/B}{1+z^{-L_0}A/B}.
$$
On the outer arc use
$$
\frac{F_m}{F_0}
=\frac{1+z^{L_0+pm}B/A}{1+z^{L_0}B/A}.
$$
Each expression inside a bracket has the form $1+X(e^{i\theta})$, with $|X|<1$ on the arc where it occurs. Its argument lies in $(-\pi/2,\pi/2)$. At an arc endpoint $X=-1$, and the derivative of $|X|^2$ is nonzero by the strict crossing of $|A|^2-|B|^2$. The derivative of $1+X$ there has a nonzero real part. The limiting argument from inside the arc therefore also lies strictly in $(-\pi/2,\pi/2)$.

The difference of the two bracket arguments in each ratio has an endpoint limit in $(-\pi,\pi)$. The limits from the two formulas agree at each endpoint, since they represent the same argument of the nonzero continuous ratio and $z^{pm}=1$ there. Hence the bracket contributions cancel over the full circle. The factor $z^{pm}$ advances the argument on the central arc by $pm(2\theta_0)=4\pi m$. The argument principle gives $N(F_m)-N(F_0)=2m$, where $N(F)$ counts roots in the open disk.

In the odd row $F_0=1-2z$ has one root inside. In the even row $F_0=1-2z+2z^2-2z^3+2z^6$. The successive leading principal determinants of its Schur–Cohn matrix, including the empty determinant, are
$$
1,\quad -3,\quad -7,\quad 117,\quad -99,\quad -17199,\quad 123201.
$$
They are nonzero, and four ratios of consecutive determinants are negative. The corresponding diagonal elimination by Schur complements and §1 give four roots inside. Thus $N(F_m)=k$ in both rows.

Apply (1) with $G=-\tau$ and $N=n+1>2k$. The only equality point is $1$, and (2) gives its derivative threshold $2k$. The polynomial $F_m-\tau z^N$ retains $k$ roots inside and has exactly the simple circle root at $1$. Dividing by $1-z$ cancels it and yields the claimed Littlewood witness.

## 3. Existence and the source theorems

By symmetry take $k\le n/2$. Proposition 2.6 handles $k=1$ and Theorem 2.7 handles $k=2$ outside the stated forbidden degrees. If $3\le k\le 11$ and $k+3\le n$, apply Theorem 2.8. For $n$ even, Theorem 2.9 handles odd $k\ge3$ and even $k$ in $[n/3,2n/3]$. For $n>6$ odd its second clause handles odd $k$ in $[3,n/2]$. Corollary 2.11 also gives the odd witnesses in $[3,n/2]$ and even witnesses in $[n/2,2n/3]$, with the coefficient pattern of Theorem 2.10. For any still-uncovered even $k\ge4$, either $n>2k$, when §2 supplies a witness, or $n=2k$, when Theorem 2.9 applies. The case $n\le6$ in this range is covered by the first two source results and the $k=3,n=6$ case of Theorem 2.8. Reflecting the witnesses covers $k>n/2$. The next paragraphs give the direct constructions underlying the one- and two-root ranges.

For $k=1$ and $n\ge2$, use $1-z-\cdots-z^n$. Multiplication by $1-z$ gives $1-2z+z^{n+1}$. At every $r<1$ sufficiently close to one, $1+r^{n+1}<2r$ by the derivative comparison at one. Rouché's theorem gives exactly one root on the inside of those circles. On the unit circle equality in the triangle inequality forces $z^{n+1}=1$, and the equation then forces $z=1$. The original polynomial takes the value $1-n\ne0$ there.

The following constructions for $k=2$ also rederive the needed part of the source's Theorem 2.7.

- If $n\ge4$ is even, use $++(-)^{n-1}$, the coefficient word of $(1-2z^2+z^{n+1})/(1-z)$. In (1), $F=1-2z^2$ has two roots inside, and equality against $G=1$ occurs only at $z=\pm1$. The derivative threshold is four at both. The numerator vanishes only at $1$ among these points since $n+1$ is odd.
- If $n=3m$ with $m\ge1$, use $+(++-)^m$. If $n=3m+2$ with $m\ge1$, use $+++(-++)^m$. Multiplying the respective polynomial by $1-z^3$ gives $A+z^{n+1}G$ with $A=1+z+z^2-2z^3$ and $G=-1-z+z^2$ or $G=1-z-z^2$, respectively. For both cases,
  $$
  |A(e^{i\theta})|^2-|G(e^{i\theta})|^2
      =4(1-c)(2c+1)^2,\qquad c=\cos\theta,
  $$
  and $|G|^2=5-4c^2>0$. The Schur–Cohn matrix of $A$ has diagonal $-3$ and off-diagonal entries $3$, giving negative index two and no zero eigenvalue. For the first $G$, the right-hand side of (1) is $-2$ at $1$ and $5/2$ at the other cube roots of unity. For the second $G$ the values are $-6$ and $3$, respectively. These follow by substituting $z=1$ and $z^2+z+1=0$ into the derivative expressions. All are less than $n+1$. The numerator has two roots inside, with simple roots at the three roots of the factor $1-z^3$ and no other circle roots. Cancellation gives the result.
- For $n=7$, use the source's word $+++-+-+-$. Symmetric elimination of its Schur–Cohn matrix gives two hyperbolic $2\times 2$ pivots, with off-diagonals $2,4$, followed by positive pivots $4,7/4,12/7$. It is nonsingular with negative index two.

For $2\le n<4$, $k=2$ lies outside $k\le n/2$. The remaining $k=2$ cases are precisely the forbidden degrees, which we exclude below.

**How the Lean proof assigns the cases.** For $2k\le n$ and $(k,n)$ not forbidden, the case split in `LittlewoodEndpoint.lean` is as follows. $k=1$ uses Proposition 2.6. $k=2$ uses Theorem 2.7. $3\le k\le11$ uses Theorem 2.8. Odd $k\ge13$ uses the odd branch of Corollary 2.11. Even $k\ge12$ with $n$ even and $n\le3k$ uses the even branch of the first clause of Theorem 2.9. Every remaining even $k\ge12$ uses the new family of §2: these are the cases with $n$ odd and $n>2k$, or with $n$ even and $n>3k$. The cases $k>n/2$ follow by reflection, which is proved in Lean. Only the first conjunct of each of Proposition 2.6, Theorem 2.7 and Theorem 2.8 is used. The second clause of Theorem 2.9 and the even branch of Corollary 2.11 are not used.

## 4. Certified exclusion for all forbidden degrees

### 4.1. The finite-prefix test

Suppose that $P$ is a hypothetical counterexample. It has odd degree $n=2d+1$, where $d\ge6$ and $3\mid d$. Multiplying by a sign and substituting $z\mapsto-z$ if needed normalizes both the constant and leading coefficients to 1. Let $P^\#(z)=z^nP(1/z)$.

The two polynomials are coprime. Every root of a Littlewood polynomial has modulus less than two, by comparing the leading term with the sum of all lower terms when $|z|\ge2$. A monic common factor $G=\gcd(P,P^\#)$ is invariant under reciprocation up to a sign, and has no circle roots. It consequently has even degree, at most four, and half of its roots are inside. If it has degree four, the nonconstant monic integer quotient $P/G$, with constant term of modulus one, would have all its roots strictly outside. This contradicts their product of moduli being one. A monic reciprocal quadratic has constant term 1 and is $z^2+az+1$. Unless it has circle roots, $|a|\ge3$ and its larger root in modulus exceeds two. A monic antireciprocal quadratic has roots $1,-1$. These facts rule out degree two as well.

For arrays $a,b$ of length $N$, let $L(a),L(b)$ be the lower triangular Toeplitz matrices with these first columns, and put
$$
H(a,b)=L(a)L(a)^{\mathsf T}-L(b)L(b)^{\mathsf T}.
$$
For the full Schur–Cohn matrix use the first $n$ coefficients of $P$ and of $P^\#$. Up to sign this is the Hermitian Bézoutian, obtained by taking coefficients of $(P(z)P(w)-P^\#(z)P^\#(w))/(1-zw)$. In this sign convention the negative eigenvalues count the roots of $P$ inside when $P,P^\#$ are coprime. Thus $H$ is nonsingular with negative index exactly two. No principal submatrix of it can have a nonpositive subspace of dimension three, since projection onto the negative eigenspace of a nonsingular form is injective on any nonpositive subspace. Equivalently, every principal submatrix has at most two negative and zero eigenvalues combined. [Heinig–Rost, Theorem 10.9](https://www.tu-chemnitz.de/mathematik/preprint/2008/PREPRINT_09.pdf)

The first unequal coefficient pair occurs at position one or two. To see this, put $a=(P_i)$, $b=(P^\#_i)$, so the formal power series $(a-b)/(a+b)$ is defined with constant term zero. Congruence by the invertible lower Toeplitz matrix of $(a+b)/2$ transforms $H$, up to a positive scalar, into the sum of the lower Toeplitz matrix of this series and its transpose. If the first mismatch is at $j$, the first $j\times j$ block is zero, and the cross block against columns $j,\ldots,2j-1$ is triangular with the first nonzero series coefficient as its diagonal. The combined $2j\times2j$ matrix has negative index $j$, by eliminating the bottom-right block by a congruence. The reversed pairing implies $2j\le n$. If there is no mismatch, $P$ is reciprocal of odd degree and vanishes at $-1$. This proves the asserted bound on $j$.

The first $d+1$ coefficient pairs specify the entire word. Write their alphabet as $0=(+,+)$, $1=(+,-)$, $2=(-,+)$, $3=(-,-)$, including the initial letter 0. Append letters from the outside of the word toward the middle. The leading principal matrix at each stage has entries
$$
 H_{ij}=\sum_{h=0}^{\min(i,j)}(a_{i-h}a_{j-h}-b_{i-h}b_{j-h}).
\tag{1}
$$
The script `scripts/littlewood_forbidden_certificate.py` builds a finite list of possible prefixes through depth 71, where depth is the number of noninitial letters. It discards a prefix by an exact witness for a nonpositive subspace of dimension at least three. The prefix checker keeps an exact integer orthogonal basis, allowing zero diagonal entries. When a row and column are appended, the new coordinate vector is first made orthogonal to the old nonnull vectors using their diagonal entries as pivots. Multiplying by a positive common denominator keeps the coefficients integral. If the resulting vector $z$ is orthogonal to every old null vector, it extends the diagonal basis directly. Otherwise choose an old null vector $x$ with $u=\langle x,z\rangle\ne0$, and set $y=2uz-\langle z,z\rangle x$. Then $x,y$ are isotropic and $\langle x,y\rangle=2u^2>0$. Replacing them by $x+y,x-y$ gives one positive and one negative direction. Subtracting suitable multiples of $x$ from the other null vectors makes them orthogonal to the new pair. All arithmetic, including the separate symmetric elimination used to check stationary witnesses, is exact.

### 4.2. Propagating the finite exclusion lists

At each depth $e\in[59,70]$, define the proposed set of possible prefixes at depths $e+12t$ by taking the computed list for $e$ and inflating each word at index 3 with $t$ copies of its following 12-letter block. Here and below indices start at zero. The certificate checks that the computed depth-71 list equals the inflation of the depth-59 list by one copy. Induction therefore reduces every future extension to a disallowed extension of one of the twelve finite lists. Exactly 4,416 such disallowed extensions have a stationary submatrix witness, and 60 need the kernel check below.

For stationarity, write the inflated paired word as $W_t=U C^t V$, $|U|=S=3$, $|C|=p=12$, with $C$ taken from the start of $V$. Keep a fixed set of early row indices $I$, and a set $J$ of later row indices shifted by $pt$. The following finite conditions suffice to ensure that the resulting principal submatrix is independent of $t$.

1. $\min J-\max I\ge S$.
2. The suffix $V$ starts with the periodic continuation of $C$ through at least $\max(p,\max I+1-S,\max J-\min J)$ letters.
3. The two sign sequences of $C$ have identical cyclic autocorrelations at every lag.

For two fixed indices, the indices in (1) are at most $\max I$. Each of those coefficients is unchanged by condition 2, or by its location before $S$. For a fixed and a moving index, rewrite (1) with the fixed sequence index running from zero to the fixed row, and the other index larger by the difference between the rows. Condition 1 puts that second index in the shifted suffix, so its values repeat the uninflated ones. For two moving indices, their difference $\Delta$ stays fixed. In (1) use the earlier sequence index $h$ and the later index $h+\Delta$. Contributions with $h<S$ are unchanged by condition 2. Contributions with $h\ge S+pt$ match the old suffix terms after subtracting $pt$ from both indices. In the inserted range the two sign sequences are periodic even across the end of the range into the first $\Delta$ letters of $V$. Each added cycle contributes zero by condition 3. This proves stationarity. The verifier checks the three finite conditions before accepting either a prefix or a finished-word witness.

For the 60 remaining disallowed extensions, the stationary matrix already has two strictly negative directions. An exact nonzero kernel vector of the full prefix matrix supplies the third nonpositive direction. Each discovered kernel has first entry $b_0\in[-4,4]$ and entry $\epsilon^j$ at every index $j\ge1$, for $\epsilon=\pm1$. Here is the all-length verification.

For the $a$ sign sequence, let $s_a(i)=\sum_{u\le i}a_u\epsilon^u$. The inserted period has signed sum zero in each sign sequence. As a consequence, relative to the original word, the inflated $s_a$ is obtained by inserting a repeated block of length $p$ at position $S$. This follows by direct partial summation over each inserted block. The coordinates of $L(a)^{\mathsf T}v$ are $\epsilon^i s_a(N-1-i)$, with the constant correction $b_0-1$ at index zero because $a_0=1$. Reversing the sequence moves the insertion to position $N_0-S$, where $N_0$ is the uninflated length. Multiplying by $\epsilon^i$ preserves the repeat because $p$ is even. The same holds for $b$. The verifier computes the inserted block in these transpose products from the once-inflated word, checks the zero signed sums, and checks that the original sequence is recovered by deleting the block.

For any word inflated by repeatedly inserting a fixed coefficient block, its polynomial has the form $(A_0(z)+z^{pt}A_1(z))/(1-z^p)$, by summing a finite geometric series. Apply this to $a,b$ and the two transpose products. The generating function for $Hv$ is the truncation at length $N_0+pt$ of their convolution difference. After multiplying by $(1-z^p)^2$, which does not affect whether the truncated series is zero, the expression is
$$
 E_0(z)+z^{pt}E_1(z)+z^{2pt}E_2(z)
$$
with explicitly computed fixed integer polynomials. The verifier checks that $E_0=0$ and that the coefficients of $E_1$ below degree $N_0$ vanish. This suffices for $pt\ge N_0$. It checks the remaining finitely many values of $t$ directly. These checks prove the kernel identity for every allowed inflation length. A two-dimensional negative subspace plus this kernel vector is a nonpositive subspace of dimension three, so the extension is excluded.

### 4.3. Checking completed words

For all forbidden degrees below the periodic cutoff, test the candidate lists using the full matrix and the two endpoint values. The only surviving word at each forbidden degree is the one-root word described below, checked by exact comparison of signs. For the unbounded part, the four relevant base depths are 60, 63, 66 and 69. Complete a paired prefix $w$ by appending the reverse of $w$ with symbols 1 and 2 exchanged. The full word then has two repeated insertions, with indices on the left and right of the middle. The finite verification uses three cases.

- **Endpoint root.** At $1$ or $-1$, the value of the polynomial is affine in the repetition count because both insertions have even length. If it is zero at the base and once-inflated word, it remains zero for every inflation.
- **Stationary inertia witness.** Use the first 19 indices and 36 indices around the middle for $I$ and $J$. The second insertion is after every selected index and leaves the entries in (1) unchanged. Stationarity above applies to the remaining first insertion. The certificate checks a nonpositive subspace of dimension at least three in each such case.
- **One-root word.** The sole remaining pattern, in each of the four depth classes, becomes $1-z-z^2-\cdots-z^n$ after substituting $-z$ for $z$. The base and once-inflated pattern checks certify all repeats, since the repeated words have even length. Multiplying by $1-z$ gives $1-2z+z^{n+1}$. On a circle of radius $r<1$ sufficiently close to one, $1+r^{n+1}<2r$, by comparing the derivatives at one. Rouché's theorem gives exactly one root inside that circle. This holds for all $r$ sufficiently close to one, so the polynomial has exactly one root in the open unit disk.

The result of executing the full certificate is in `evidence/littlewood-forbidden-certificate.log`. It checks forbidden degrees 13 through 115 outright and then the twelve repeating prefix and four repeating leaf cases for all larger degrees. A separate signed-remainder calculation checks the constructive words independently of the Schur–Cohn certificates. The constructions in §§2–3 supply every other pair.

## Verification and significance

The finite Python checker for the exclusion is `scripts/littlewood_forbidden_certificate.py`. The proving lane recorded 4,416 stationary exclusions and 60 geometric-kernel exclusions at the periodic transitions. The independent review recomputed the transitions and all four periodic leaf counts using integer arithmetic. Its direct checks through degree 169 and the proving lane's finite sweeps are corroboration. The periodic proof supplies the unbounded step. The packet includes the layer data in `evidence/`, the exact audit logs in `receipts/`, and the shard generator in `scripts/`.

The main extension over the arXiv source is the exclusion for every forbidden degree. The source checked it only through degree 31, by exhaustive enumeration. The exclusion uses coprimality to justify a pruning criterion: no principal submatrix may have a three-dimensional nonpositive subspace. Periodic stationary submatrices and the explicit kernel vectors turn the bounded prefix computation into a proof covering every forbidden degree. The method is in the spirit of the periodic-family arguments long used for Pisot and Salem numbers. Its application to this problem, and the finding that the pruned prefix tree becomes exactly periodic, are new as far as we know.

The existence half is a modest extension. Most of it rests on the source's own Proposition 2.6, Theorems 2.7–2.9 and Corollary 2.11. The new content there is one regular even-$k$ pattern, proved by the source's method of boundary dominance and an argument count over two arcs. It covers even $k\ge12$ with $n$ odd and $n>2k$, or with $n$ even and $n>3k$, which the source left open. The result as a whole is computer-assisted.

Prior art. The arXiv record has only v1. A search of arXiv on 2026-11-23 found no later paper by Hare, Jankauskas or Drungilas on this question. OpenAlex lists nine citing works, on Stern polynomials, rational roots, Borwein trinomials, square values, Newman polynomials and related topics. Their titles and topics show no treatment of Conjecture 2.13. Bounded searches of the public Principia, mio-math, OpenAI Math, Omega and mxym/math repositories and registries found no resolution. The earlier Borwein–Choi–Ferguson–Jankauskas paper gives gcd conditions and some lines of admissible pairs. The Borwein-trinomial paper of Drungilas, Jankauskas and Junevičius (2024) treats three-term polynomials only. The journal version, *Mathematics of Computation* 90 (2021), was not read; the probability that it settles or changes Conjecture 2.13 is estimated at about 0.03. [ArXiv v1](https://arxiv.org/abs/1910.13994) [Journal record](https://doi.org/10.1090/mcom/3570) [Borwein–Choi–Ferguson–Jankauskas](https://doi.org/10.4153/CJM-2014-007-1)

The Schur–Cohn inertia theorem used in §1 and §4.1 is classical. See G. Heinig and K. Rost, "Introduction to Bezoutians", *Oper. Theory Adv. Appl.* 199 (2010), linked above in §4.1. Here it is proved in Lean in the form needed.
