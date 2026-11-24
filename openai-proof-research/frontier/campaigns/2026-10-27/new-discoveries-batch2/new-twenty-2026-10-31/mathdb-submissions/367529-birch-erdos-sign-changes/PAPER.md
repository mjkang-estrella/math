# Sign changes of $f_{p,q}(n+1)-f_{p,q}(n)$: a proof of the Ding–Liu–Wang Conjecture 3, with a Lean 4 verification

The proof, Lean code, and first review of MathDB record 367529 are by Claude Opus 5.5. The independent
cross-model review is by GPT-6.2 Sol. This manuscript presents the finite argument formalized in Lean.
Section 6 identifies the corresponding Lean lemmas. The complete Lean source is in the
[Lean source appendix](../sign-changes-fpq-367529-formal-paper-opus55-20261121-r1/LEAN-SOURCE-APPENDIX.md).

## 1. The conjecture

**Source.** Yuchen Ding, Honghu Liu and Zi Wang, "Note on a theorem of Birch–Erdős and $m$-ary partitions",
arXiv:2503.11676 (v3, 11 May 2025); J. Number Theory 279 (2026) 910–928, doi:10.1016/j.jnt.2025.07.009.
The definition and conjecture below follow the independently checked [arXiv v3 introduction](https://arxiv.org/pdf/2503.11676v3).

For coprime integers $q>p>1$, the source counts the representations of $n$ as sums of distinct elements of
$\{p^\alpha q^\beta:\alpha,\beta\in\mathbb N\}$, where $\mathbb N$ includes $0$.

The source states the following conjecture.

> **Conjecture 3.** If $\gcd(p,q)=1$ and $q>p>2$, then the sign of $f_{p,q}(n+1)-f_{p,q}(n)$ changes infinitely many often.

The authors prove that $f_{2,q}$ is nondecreasing for odd $q>2$ (Corollary 4). Corollary 3 gives
$f_{p,q}(n+1)>f_{p,q}(n)$ infinitely often. Immediately after it, the authors ask whether there are also
infinitely many strict decreases. They pose Conjecture 3 for $p>2$ on the basis of computational experiments.

Statement excerpt from MathDB record 367529 (local corpus).

> Let $f_{p,q}(n)$ be the Birch–Erdős representation function, with $p$ and $q$ relatively prime integers satisfying
> $q>p>2$. **Sign-change conjecture.** The sign of $f_{p,q}(n+1)-f_{p,q}(n)$ changes infinitely often.

Here $\mathbb N$ contains $0$, so $1=p^0q^0$ is an admissible term.

**Lean definitions** (`src/FpqStatement.lean`, transcribed from the review's required endpoint):

```lean
def BE (p q : ℕ) : Set ℕ := {s | ∃ α β : ℕ, s = p ^ α * q ^ β}

open Classical in
noncomputable def f (p q n : ℕ) : ℕ :=
  (((Finset.range (n + 1)).filter (· ∈ BE p q)).powerset.filter (fun T => T.sum id = n)).card
```

`f p q n` counts the finite subsets $T$ of $\{p^\alpha q^\beta\}\cap[0,n]$ with $\sum T=n$. This is the source's
count. A sum of distinct terms equal to $n$ uses only terms $\le n$. Different expressions are different sets of
terms. Since $p,q\ge1$, $0$ is not a term (`zero_not_mem_BE`), so no expression is counted twice through an added $0$.
At $n=0$ the count is $1$, contributed by the empty subset. The declaration `open Classical in` supplies
the decidability instance needed by `Finset.filter` for membership in `BE p q`.

**Main theorem** (`Fpq.ding_liu_wang_conj3`). Let $p,q$ be integers with $2<p<q$ and $\gcd(p,q)=1$. Then
$f_{p,q}(n+1)<f_{p,q}(n)$ for infinitely many $n$, and $f_{p,q}(n)<f_{p,q}(n+1)$ for infinitely many $n$.

```lean
theorem ding_liu_wang_conj3 (p q : ℕ) (hp : 2 < p) (hpq : p < q) (hcop : Nat.Coprime p q) :
    (∀ N, ∃ n ≥ N, f p q (n + 1) < f p q n) ∧ (∀ N, ∃ n ≥ N, f p q n < f p q (n + 1))
```

Both strict signs occur arbitrarily far out, so there are infinitely many switches between positive and negative
differences in the subsequence of nonzero differences. This answers the source's explicit question about
infinitely many strict decreases as well as its sign-change formulation. The argument also applies when the
order of the coprime parameters $p,q\ge3$ is reversed.

## 2. Notation and finite generating products

Fix coprime $p\ge3$, $q\ge3$ and write $S=\{p^aq^b:a,b\ge0\}$ and $f=f_{p,q}$. For a finite set $A\subset\mathbb N$ let
$\mathrm{cnt}(A,n)$ be the number of subsets $T\subseteq A$ with $\sum T=n$. Put $A_M=S\cap[0,M]$; then
$f(n)=\mathrm{cnt}(A_n,n)$ by definition.

**Lemma 1.** (a) If $n\le M$ then $\mathrm{cnt}(A_M,n)=f(n)$. (b) If $n>\sum A$ then $\mathrm{cnt}(A,n)=0$.
(c) In every commutative semiring, for $L>\sum A$,
$$G_A(z):=\prod_{s\in A}(1+z^s)=\sum_{n<L}\mathrm{cnt}(A,n)\,z^n .$$
(d) In every commutative ring, if $c_L=0$ then
$(1-z)\sum_{n\le L}c_nz^n=\sum_{n\le L}(c_n-c_{n-1})z^n$ with $c_{-1}=0$.

*Proof.* (a) A subset of $A_M$ with sum $n$ has all elements $\le n$, so it is a subset of $A_n$, and conversely
$A_n\subseteq A_M$. (b) Every subset sum is at most $\sum A$. (c) Expand $\prod(1+z^s)=\sum_{T\subseteq A}z^{\sum T}$
and group the subsets by their sum. (d) Shift the index. $\square$

**Lemma 2.** (a) If $p^aq^b=p^{a'}q^{b'}$ then $a=a'$ and $b=b'$. (b) The elements of $A_M$ not divisible by $q$ are
exactly the powers $p^a\le M$.

*Proof.* (a) If $a<a'$, cancel $p^a$: $q^b=p^{a'-a}q^{b'}$, so $p\mid q^b$, which contradicts coprimality. The case $a>a'$ follows by exchanging the two pairs. Thus $a=a'$,
and then $q^b=q^{b'}$ gives $b=b'$. (b) If $b\ge1$ then $q\mid p^aq^b$. Conversely $q\nmid p^a$ because $\gcd(q,p^a)=1$ and $q>1$. $\square$

## 3. The root of unity

**Lemma 3.** There is $c>0$ such that for every $N\ge0$ there is $\omega\in\mathbb C$ with $\omega^q=1$,
$|\operatorname{Im}\omega|\ge c$, and $\prod_{a=0}^{N}|1+\omega^{p^a}|\ge1$.

*Proof.* Write $q=2^v o$ with $o$ odd.

*Case $o\ge3$.* Let $R$ be the set of $o$-th roots of unity other than $1$. It is nonempty, and $\xi^q=1$ for
$\xi\in R$. From $X^o-1=\prod_{\xi^o=1}(X-\xi)$ at $X=-1$ and $o$ odd, $-2=(-2)\prod_{\xi\in R}(-1-\xi)$, so
$\prod_{\xi\in R}|1+\xi|=1$. For $e$ coprime to $o$, the map $\xi\mapsto\xi^e$ is a bijection of $R$: take $e'$ with
$ee'\equiv1\pmod o$; then $\xi\mapsto\xi^{e'}$ is its inverse, and $\xi^e=1$ forces $\xi=(\xi^e)^{e'}=1$.
Since $\gcd(p^a,o)=1$,
$$\prod_{\xi\in R}\prod_{a=0}^N|1+\xi^{p^a}|=\prod_{a=0}^N\prod_{\xi\in R}|1+\xi^{p^a}|=\prod_{a=0}^N\prod_{\xi\in R}|1+\xi|=1,$$
so some $\xi\in R$ has $\prod_{a\le N}|1+\xi^{p^a}|\ge1$. (Otherwise every factor of the outer product lies in
$[0,1)$ and the product is $<1$.) This $\xi$ may depend on $N$. No $\xi\in R$ is real: a real $\xi$ with $\xi^o=1$
and $o$ odd equals $1$. So $c:=\min_{\xi\in R}|\operatorname{Im}\xi|>0$ works for every $N$.

*Case $o=1$.* Then $q=2^v\ge3$, so $v\ge2$ and $4\mid q$, and $p$ is odd. Take $\omega=i$ and $c=1$. Then $i^q=1$.
Each $p^a$ is odd, so $i^{p^a}=\pm i$ and $|1+i^{p^a}|\ge|\operatorname{Re}(1\pm i)|=1$. $\square$

The root can be chosen separately for each $N$. The finite set of eligible roots gives a uniform constant $c$.

## 4. Elementary estimates

**Lemma 4.** Let $|\zeta|=1$ and $y\ge0$. Then (a) $|1+\zeta y|\ge\frac{1+y}2|1+\zeta|$, and
(b) $|1+\zeta y|\ge(1-2y)(1+y)$.

*Proof.* (a) With $a=\operatorname{Re}\zeta$:
$4|1+\zeta y|^2-(1+y)^2|1+\zeta|^2=4(1+2ay+y^2)-(1+y)^2(2+2a)=2(1-a)(1-y)^2\ge0$.
(b) $|1+\zeta y|\ge1-y\ge1-y-2y^2$. $\square$

**Lemma 5.** If $u_i\in[0,1]$ then $\prod(1-u_i)\ge1-\sum u_i$ (induction).

**Lemma 6 (Bernoulli).** For an integer $m\ge1$ and $x=1-1/m$: $x^m\le\frac12$, and $x^s\ge1-s/m$ for every integer $s\ge0$.

*Proof.* $(1+1/m)^m\ge2$ and $\bigl((1-1/m)(1+1/m)\bigr)^m\le1$. The second bound is Bernoulli's inequality. $\square$

**Lemma 7 (finite Pringsheim bound).** Let $c_n\ge0$ with $c_L=0$, $0\le x\le1$, $|z|=x$, and suppose
$c_n\le c_{n+1}$ for $n_0\le n<M$. Set $c_{-1}=0$. Then
$$\Bigl|(1-z)\sum_{n\le L}c_nz^n\Bigr|\le(1-x)\sum_{n\le L}c_nx^n+2\sum_{1\le n\le n_0}c_{n-1}+2\sum_{M\le n<L}c_nx^n .$$

*Proof.* By Lemma 1(d) the left side is $|\sum d_nz^n|\le\sum|d_n|x^n$ with $d_n=c_n-c_{n-1}$, and
$\sum d_nx^n=(1-x)\sum c_nx^n$. Write $|d_n|=d_n+(|d_n|-d_n)$ and note $0\le|d_n|-d_n\le2c_{n-1}$. For $n_0<n\le M$,
$d_n\ge0$ and the excess vanishes. For $n\le n_0$, bound $x^n\le1$. For $n>M$, use $c_{n-1}x^n\le c_{n-1}x^{n-1}$ and shift the index. $\square$

**Lemma 8 (tails).** Let $0\le x<1$ and $y=\sqrt x$. For every finite $A$, $G_A(y)\le\exp(1/(1-y))$, and for
$c_n=\mathrm{cnt}(A_M,n)$, $\sum_{M\le n<L}c_nx^n\le y^M G_{A_M}(y)$. Hence for every $M_0$ there is $M\ge M_0$
such that $\sum_{M\le n<L}\mathrm{cnt}(A_M,n)x^n\le\frac14$ for all $L$.

*Proof.* $1+t\le e^t$ and $\sum_{s\in A}y^s\le\sum_{s\ge0}y^s=1/(1-y)$. For $n\ge M$,
$x^n=y^ny^n\le y^My^n$, and $\sum_nc_ny^n=G_{A_M}(y)$ by Lemma 1(c). Choose $M$ with $y^M\exp(1/(1-y))<\frac14$. $\square$

The proof uses finite generating products $G_{A_M}$. Lemma 8 gives the tail estimate needed to compare their
coefficients with $f$, without using the source's asymptotic for $f$.

## 5. The twisted product, growth, and the two halves

**Lemma 9 (twisted product).** Let $p^N\le M$, $\omega^q=1$, $\prod_{a\le N}|1+\omega^{p^a}|\ge1$, $0\le x\le1$ and
$x^{p^N}\le\frac12$. Then $|G_{A_M}(\omega x)|\ge2^{-(N+2)}G_{A_M}(x)$.

*Proof.* We have $|\omega|=1$ and $(\omega x)^s=\omega^sx^s$. Define $h(s)=1$ if $q\mid s$; $h(s)=|1+\omega^s|/2$ if
$q\nmid s$ and $s\le p^N$; and $h(s)=1-2x^s$ otherwise. For $s\in A_M$ we have $h(s)\ge0$ and
$|1+(\omega x)^s|\ge h(s)(1+x^s)$. If $q\mid s$ then $\omega^s=1$. In the middle case use Lemma 4(a). In the last
case $s=p^a$ with $a>N$ by Lemma 2(b), so $x^s\le x^{p^N}\le\frac12$, and Lemma 4(b) applies. Multiplying,
$|G_{A_M}(\omega x)|\ge\prod_{s\in A_M}h(s)\cdot G_{A_M}(x)$. By Lemma 2(b), and since $a\mapsto p^a$ is injective,
$$\prod_{s\in A_M}h(s)=\prod_{a=0}^{N}\frac{|1+\omega^{p^a}|}{2}\cdot\prod_{a>N,\ p^a\le M}(1-2x^{p^a}).$$
The first factor is $\ge2^{-(N+1)}$. For $a>N$, $x^{p^a}=(x^{p^N})^{p^{a-N}}\le2^{-p^{a-N}}\le2^{-(a-N+2)}$, because
$p^j\ge j+2$ for $j\ge1$ and $p\ge3$. So $\sum_{a>N}2x^{p^a}\le\sum_{j\ge1}2^{-(j+1)}\le\frac12$, and by Lemma 5 the
second factor is $\ge\frac12$. $\square$

**Lemma 10 (growth).** Let $k\ge0$, $p^{2qk}\le M$, and suppose $x\ge0$ with $x^s\ge\frac12$ for all $s\le p^{2qk}$. Then
$G_{A_M}(x)\ge(3/2)^{k^2}$.

*Proof.* The numbers $p^aq^b$ with $a<qk$, $b<k$ are distinct (Lemma 2(a)). They are at most
$p^{a+qb}\le p^{2qk}$, since $q\le p^q$. So they lie in $A_M$, and each contributes a factor $1+x^s\ge\frac32$. All
other factors are $\ge1$. There are $qk\cdot k\ge k^2$ of them. $\square$

**Lemma 11.** For $C,b\ge0$ and $\varepsilon>0$ there is $k_0$ with $C\,b^k(2/3)^{k^2}<\varepsilon$ for all $k\ge k_0$.
(For large $k$, $b(2/3)^k\le\frac12$, so $b^k(2/3)^{k^2}=(b(2/3)^k)^k\le2^{-k}$.)

**Setup for both halves.** For $k\ge0$ put $N=2qk+1$, $m=p^N$ and $x=1-1/m$. Then $\frac12\le x<1$ and $1-x=1/m$.
Also $x^{p^N}=x^m\le\frac12$ by Lemma 6. For $s\le p^{2qk}=m/p$ we have $x^s\ge1-s/m\ge1-1/p\ge\frac12$.

**Theorem A.** $f(n+1)<f(n)$ for infinitely many $n$.

*Proof.* Suppose $f(n)\le f(n+1)$ for all $n\ge n_0$. Let $K=\sum_{1\le n\le n_0}f(n-1)$ and let $c$ be the constant
of Lemma 3. Choose $k$ large enough that $8(2/3)^k<c/2$ and, by Lemma 11, $16(2K+1)(4^q)^k(2/3)^{k^2}<c/2$. Take $N,m,x$ as above
and $\omega$ from Lemma 3 for this $N$. The first inequality for $k$ follows from $(2/3)^k\to0$.
By Lemma 8, choose $M\ge\max(n_0,m)$ with tails $\le\frac14$. Let
$c_n=\mathrm{cnt}(A_M,n)$, $L=\sum A_M+1$ and $G=G_{A_M}(x)$. By Lemma 1, $c_n=f(n)$ for $n\le M$, so the
hypothesis of Lemma 7 holds with this $n_0$ and $M$. Its middle term is $2K$. With $z=\omega x$, Lemma 1(c) turns
Lemma 7 into
$$|1-\omega x|\,|G_{A_M}(\omega x)|\le\frac{G}{m}+2K+\tfrac12 .$$
Also $|1-\omega x|\ge|\operatorname{Im}(\omega x)|\ge cx\ge c/2$. Lemma 9 gives $|G_{A_M}(\omega x)|\ge2^{-(N+2)}G$. So
$$c\,G\le\frac{2^{N+3}}{m}G+2^{N+3}(2K+1).$$
Now $2^{N+3}/m=8(2/p)^N\le8(2/3)^k$. By Lemma 10, $G\ge(3/2)^{k^2}$, so
$2^{N+3}(2K+1)=16(2K+1)(4^q)^k\le16(2K+1)(4^q)^k(2/3)^{k^2}G$. Hence $cG<(c/2+c/2)G$, a contradiction since $G>0$. $\square$

**Theorem B.** $f(n)<f(n+1)$ for infinitely many $n$.

*Proof.* Suppose $f(n+1)\le f(n)$ for all $n\ge n_0$. Then $f(n)\le B:=\sum_{n\le n_0}f(n)$ for all $n$. Choose $k$
by Lemma 11 with $(Bp+1)(p^{2q})^k(2/3)^{k^2}<1$. Take $N,m,x$ as above and $M\ge m$ from Lemma 8. Bound each
coefficient by $c_nx^n\le Bx^n$ for $n<M$, and keep the tail for $n\ge M$. Then
$G=G_{A_M}(x)\le B/(1-x)+\frac14=Bm+\frac14\le(Bp+1)(p^{2q})^k$, since $m=p(p^{2q})^k$. Lemma 10 gives
$(3/2)^{k^2}\le G$, so $1\le(Bp+1)(p^{2q})^k(2/3)^{k^2}<1$, a contradiction. $\square$

Theorems A and B together give the main theorem: the conjecture holds for every coprime $q>p>2$.

**Differences from the proof lane's write-up.** The proof lane works with infinite products and the radius
$x_N=e^{-p^{-N}}$. Here we use finite truncations with an explicit tail bound, the rational radius $1-p^{-N}$, a root
of unity chosen per $N$ (no cosets or periods), and Theorem B via boundedness on the same finite products. The key
idea is unchanged. If $\omega^q=1$, twisting by $\omega$ only affects the factors $1+z^{p^a}$. Lemma 9 bounds the ratio of the twisted modulus to the
real product below by $2^{-(N+2)}$. The coefficient comparison contributes $1-x=p^{-N}$, which decays
faster for $p\ge3$.

## 6. Lean verification

Lean 4.34.1 with Mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612`. Six modules, 1,234 lines, specific
Mathlib imports only. `#print axioms Fpq.ding_liu_wang_conj3` gives `[propext, Classical.choice, Quot.sound]`.

| Statement here | Lean name (module) |
|---|---|
| Definitions, endpoint | `Fpq.BE`, `Fpq.f`, `Fpq.Conj3`, `Fpq.ding_liu_wang_conj3`, `Fpq.conj3` (`FpqStatement`, `FpqMain`) |
| Fidelity and sanity | `zero_not_mem_BE`, `hyp_nonvacuous`, `f_3_4_0`, `f_3_4_1`, `f_3_4_2`, `f_3_4_decrease` (`FpqStatement`) |
| Lemma 1 | `cnt_A_eq`, `cnt_eq_zero`, `prod_eq_sum`, `one_sub_mul_sum` (`FpqCount`) |
| Lemma 2 | `BE_inj`, `A_filter_not_dvd`, `eq_pow_of_mem_BE`, `not_dvd_pow` (`FpqCount`) |
| Lemma 3 | `exists_roots`, `exists_good_R`, `prod_R_neg_one_sub`, `prod_R_pow`, `im_ne_zero_of_mem_R` (`FpqRoots`) |
| Lemmas 4–8, 11 | `step4`, `tail_factor`, `one_sub_sum_le_prod`, `pow_m_le_half`, `one_sub_le_pow`, `pringsheim`, `tail_le`, `sum_le_of_bdd`, `prod_le_exp`, `small_eventually` (`FpqAnalysis`); `exists_M` (`FpqMain`) |
| Lemma 9, 10 | `twisted_ge`, `prod_ge_growth` (`FpqRatio`) |
| Theorems A, B | `decreasing_io` (with `core_decreasing`, `arith_decreasing`), `increasing_io` (`FpqMain`) |

## 7. Significance

The result establishes infinitely many strict decreases for all coprime $q>p>2$, complementing the strict
increases in the source's Corollary 3. The proof compares the finite generating product on the positive real
axis and at a root-of-unity twist. Taking the order of the root to divide $q$ leaves every factor with
$q\mid s$ unchanged. Averaging over roots then gives the lower bound needed for the factors with $s=p^a$.
The theorem is qualitative. It establishes that each strict sign occurs arbitrarily far out.
Section 6 records the Lean verification of the two strict-sign assertions.

## 8. Prior work

Ding, Liu and Wang's arXiv v3 states Conjecture 3 as open. The indexed journal preview also presents it as a
conjecture. The journal text in full was unread. [arXiv v3](https://arxiv.org/abs/2503.11676v3) ·
[Journal record](https://doi.org/10.1016/j.jnt.2025.07.009)

The indexed citing paper is Honghu Liu, *The Birch–Erdős theorem on exponential type sequences*,
Period. Math. Hungar. 92 (2026), 327–337. Its abstract describes a representation-existence theorem with
a lower bound on the size of each summand. The citing paper in full was unread.
[Liu's journal record](https://doi.org/10.1007/s10998-026-00707-y)

The independent review searched for later work and checked public problem registries by source and by the
local MathDB record. Those searches found no prior resolution of Conjecture 3 as of 23 November 2026.
