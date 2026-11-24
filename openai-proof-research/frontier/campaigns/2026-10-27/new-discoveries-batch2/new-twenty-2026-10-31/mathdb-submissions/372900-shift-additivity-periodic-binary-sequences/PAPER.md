# A proof of the Yuan–Li–Zeng right-shift conjecture for binary sequences of high nonlinear complexity

*Claude Opus 5.5 produced the proof, the Lean 4 formalization, and the first review. GPT-6.2 Sol independently reviewed the proof, verified the Lean statement against the source, and revised this manuscript.*

## Abstract

Yuan, Li and Zeng study $n$-periodic binary sequences of high nonlinear complexity through finite representatives in sets $B(n,c,d)$. They conjecture that when $c\ge\lceil n/2\rceil$, $s\in B(n,c,n-c)$ and a right circular shift $R^b(s)$ lies in $B(n,c,d_2)$ with strictly more added terms than $s$, the shift is $b=d_2$. Their Corollary 1 allows equality of the added-term counts when $c\ge\lceil(2n-1)/3\rceil$. Their Lemma 7 also treats individual inputs below that threshold. The authors report experimental evidence for the half-length range and say their technique does not establish it. We prove the conjecture for all $n$ and all $c\ge\lceil n/2\rceil$.

The proof reformulates the problem in terms of maximal periodic runs of the bi-infinite periodic word. Four local comparisons and a reversal symmetry reduce it to one configuration. That configuration is excluded by a new *Run Lemma*: for an $e$-periodic binary word $W$ with shift-difference words $a_s(j)=W_j\oplus W_{j+s}$, consecutive ones $f<f'$ of $a_{d+m}$ (with $0\le m<e$) and consecutive ones $g<g'$ of $a_d$ with $g\le f'$ satisfy $(g-f)+(g'-f')\le e+m$. Its proof compares two readings of one period of $a_m$ via a rotation-invariant count of zero-runs of a fixed length.

The whole argument is formalized in Lean 4 with Mathlib. The formal definitions follow the preprint, with the zero added-term count used in its later results. Lean verifies instances with a strict increase and a counterexample to the non-strict version.

## 1. The conjecture and the source definitions

**Source.** Q. Yuan, C. Li, X. Zeng, *The structure and enumeration of periodic binary sequences with high nonlinear complexity*, arXiv:2602.01134v1 (1 Feb 2026), §2 and §3.1. A journal version appeared in IEEE Trans. Inf. Theory 72(8):6189–6203 (2026), DOI 10.1109/TIT.2026.3695307. We did not read the journal text (see §8).

**Conjecture 1 (verbatim).** "For $c \ge \lceil n/2\rceil$ and $s_n \in B(n, c, n-c)$, if there exists an integer $0 < b < n$ such that $R^b(s_n) \in B(n, c, d_2)$ satisfies $\mathrm{add}(R^b(s_n)) > \mathrm{add}(s_n)$, then $b = d_2$."

The source definitions are quoted below from arXiv v1 (the PDF text, with the typeset formulas restored), each followed by its Lean transcription from `src/RightShiftDefs.lean`. Sequences are `Fin n → Bool`. On the domain of each source definition, `get s i` returns $s_i$ at an index $i<n$. The source works over $\mathbb Z_2$. In this alphabet, $\bar s_r=s_r\oplus1$ is `!(get s r)`.

**Aperiodic.**
> "A sequence $(s_0, s_1, \dots , s_{n-1})$ is called a periodic finite-length sequence if it is formed by multiple repetitions of a short sequence of length $e$, where $e$ is a proper divisor of $n$; otherwise, it is termed an aperiodic finite-length sequence, or simply said to be aperiodic."

```lean
def Aperiodic {n : ℕ} (s : Fin n → Bool) : Prop :=
  ¬ ∃ e : ℕ, e < n ∧ 0 < e ∧ e ∣ n ∧ ∀ i < n, get s i = get s (i % e)
```

**Definition 2.**
> "For $c \ge \lfloor n/2\rfloor$ and $1 \le d \le \min\{n - c, \lfloor n/2\rfloor\}$, we denote by $B(n, c, d)$ the set of aperiodic binary sequences $s_n$ starting with $s_{c+d}$, defined as follows:
> $B(n,c,d)=\{\, s_n = s_{c+d}\, s[c+d:n] = ((s_0,\dots,s_{d-1})^q\,(s_0,\dots,s_{r-1},\bar s_r)\, s[c+d:n]) \,\}$ (1), where $q=\lfloor (c+d-1)/d\rfloor$, $0\le r=(c+d-1)-qd<d$, $s_d=(s_0,\dots,s_{d-1})$ is aperiodic, $(s_0,\dots,s_{d-1})^q$ denotes $q$ repetitions of $s_d$, $\bar s_r=s_r\oplus 1$, and the subsequence $s[c+d:n]$ is chosen from $\mathbb Z_2^{n-c-d}$ arbitrarily. The parameter $d$ is called the spacing of $s_n$." (The source adds: "since $c \ge \lfloor n/2\rfloor$, the structure in (1) ensures that the sequence $s_n$ is aperiodic.")

```lean
def pre {n : ℕ} (d : ℕ) (s : Fin n → Bool) : Fin d → Bool := fun i => get s i.val

def InBStruct (n c d : ℕ) (s : Fin n → Bool) : Prop :=
  n / 2 ≤ c ∧ 1 ≤ d ∧ d ≤ min (n - c) (n / 2) ∧ Aperiodic (pre d s) ∧
  (∀ j < (c + d - 1) / d, ∀ i < d, get s (j * d + i) = get s i) ∧
  (∀ i < (c + d - 1) - (c + d - 1) / d * d,
      get s ((c + d - 1) / d * d + i) = get s i) ∧
  get s ((c + d - 1) / d * d + ((c + d - 1) - (c + d - 1) / d * d))
    = !(get s ((c + d - 1) - (c + d - 1) / d * d))

def InB (n c d : ℕ) (s : Fin n → Bool) : Prop := Aperiodic s ∧ InBStruct n c d s
```

The three block clauses say $s_{jd+i}=s_i$ for $j<q$ and $i<d$, $s_{qd+i}=s_i$ for $i<r$, and $s_{qd+r}=\bar s_r$. `InB` keeps "aperiodic binary sequences $s_n$" literally. The main theorem is also proved for `InBStruct` alone, without aperiodicity of the whole sequence.

**Definition 3.**
> "Given a certain positive integer $t$, if a sequence $s_n$ in $B(n, c, d)$ with $c \ge \lfloor n/2\rfloor$ satisfies $s_{n-1-i} = s_{(d-1-i) \bmod d}$ for $0 \le i < t$, and $s_{n-1-t} \ne s_{(d-1-t) \bmod d}$, then we call $s_{n-t},\dots, s_{n-1}$ the added terms of $s_n$ and denote by $\mathrm{add}(s_n)$ the number $t$ of the added terms of $s_n$."

```lean
def IsAdd (n d : ℕ) (s : Fin n → Bool) (t : ℕ) : Prop :=
  t < n ∧ (∀ i < t, get s (n - 1 - i) = get s ((((d : ℤ) - 1 - i) % d).toNat)) ∧
  get s (n - 1 - t) ≠ get s ((((d : ℤ) - 1 - t) % d).toNat)
```

The residue $(d-1-i)\bmod d\in[0,d)$ is computed in $\mathbb Z$, and $t<n$ makes $s_{n-1-t}$ exist. The source says "positive integer $t$" but uses $\mathrm{add}(s_n)=0$ elsewhere (Lemma 5 with $\omega=\lceil n/2\rceil$, and the decomposition (3), where $\mathrm{add}(s_n)=0$ appears). `IsAdd` allows $t=0$, so the theorem covers both readings. Theorem 2 (§2) shows that `IsAdd n d s t` has exactly one solution $t$ for every $s\in B(n,c,d)$, so $\mathrm{add}$ is a well-defined function. Lean also defines it as one (`add`).

**Right circular shift.**
> "the right circular shift operators $R^i(s_n) = (s_{n-i},\dots, s_{n-1}, s_0,\dots, s_{n-i-1})$ for $i \ge 1$."

```lean
def rotR (n b : ℕ) (s : Fin n → Bool) : Fin n → Bool :=
  fun j => if j.val < b then get s (n - b + j.val) else get s (j.val - b)
```

**The statement.**
```lean
def Conjecture1 : Prop :=
  ∀ (n c : ℕ) (s : Fin n → Bool), (n + 1) / 2 ≤ c → InB n c (n - c) s →
    ∀ b d₂ : ℕ, 0 < b → b < n → InB n c d₂ (rotR n b s) →
      ∀ t₁ t₂ : ℕ, IsAdd n (n - c) s t₁ → IsAdd n d₂ (rotR n b s) t₂ → t₁ < t₂ → b = d₂
```

Here $\mathrm{add}(s)$ is taken with spacing $n-c$ and $\mathrm{add}(R^b(s))$ with spacing $d_2$, as in the conjecture. $\lceil n/2\rceil$ is `(n + 1) / 2`.

## 2. Results

**Theorem 1 (`RightShift.conjecture1 : Conjecture1`).** Conjecture 1 holds for all $n$, all $c\ge\lceil n/2\rceil$, all $s\in B(n,c,n-c)$, all $0<b<n$ and all $d_2$.

The proof uses only the structural part of $B$ (`conjecture1_struct`). `conjecture1_add` states the same result with $\mathrm{add}$ as a function.

**Theorem 2.** Let $s\in B(n,c,d)$ (structural part).
1. (`isAdd_unique`) At most one $t$ satisfies Definition 3.
2. (`isAdd_exists`, `isAdd_lt`, `add_well_defined`) Such a $t$ exists, and it satisfies $t<n-c$. We prove existence and recover the bound from the source’s Lemma 3(ii).

**Non-vacuity and sharpness (kernel-checked by `decide`).**
- `instance11`: all hypotheses hold for $n=11$, $c=6$, $s=10010100100$, $b=d_2=3$, $\mathrm{add}(s)=1$, $\mathrm{add}(R^3 s)=4$. The spacing drops from $5$ to $3$. `instance4` is a second instance, with $n=4$.
- `strict_needed`: for $n=6$, $c=3$, $s=101100$, $b=1$, $d_2=2$, both add values are $0$ and $b\neq d_2$. So "$>$" cannot be weakened to "$\ge$" in the range $c<\lceil(2n-1)/3\rceil$. (The source's Corollary 1 uses $\ge$ in its smaller range.)

## 3. Setting up the proof

Throughout, $n\ge 2$, $\lceil n/2\rceil\le c$, $d:=n-c\ge 1$ (so $d\le c$), $s\in B(n,c,d)$ with $\mathrm{add}(s)=t$, $0<b<n$, and $v:=R^b(s)\in B(n,c,e)$ with $e:=d_2$, $1\le e\le d$, and $\mathrm{add}(v)=t'>t$. Let $X:\mathbb Z\to\{0,1\}$ be the periodic extension $X_i=s_{i\bmod n}$. Then $v_j=X_{j+k}$ with $k:=n-b$ (`ext_rotR`).

**Lemma 3.1 (run data; `runData`).** Let $w\in B(n,c,\delta)$ with $\mathrm{add}(w)=\tau$, $c\ge1$, and let $Y$ be its periodic extension. Then
(i) $Y_i=Y_{i+\delta}$ whenever $-\tau\le i$ and $i+\delta\le c+\delta-2$;
(ii) $Y_{c+\delta-1}\neq Y_{c-1}$;
(iii) $Y_{-\tau-1}\neq Y_{-\tau-1+\delta}$.

*Proof.* First, $Y_i=w_{i\bmod\delta}$ for $-\tau\le i\le c+\delta-2$.
- For $0\le i\le c+\delta-2$ this is the block structure. Write $i=j\delta+i'$; either $j<q$, or $j=q$ and $i'<r$ (`InBStruct.blk`).
- For $i=-1-m$ with $m<\tau$, we have $Y_i=w_{n-1-m}=w_{(\delta-1-m)\bmod\delta}$ by Definition 3, and $\delta-1-m\equiv i \pmod\delta$.

(i) follows at once.

For (ii): $Y_{c+\delta-1}=w_{qd+r}=\bar w_r$ with $r=(c+\delta-1)\bmod\delta=(c-1)\bmod\delta$, while $Y_{c-1}=w_r$.

For (iii): $Y_{-\tau-1}=w_{n-1-\tau}\neq w_{(\delta-1-\tau)\bmod\delta}$, and the right side equals $Y_{\delta-1-\tau}$ because $\delta-1-\tau\in[-\tau,c+\delta-2]$. ∎

Applied to $s$ (with $\delta=d$, so $c+d=n$), Lemma 3.1 says:

**(A)** $X$ has period $d$ on $A_0=[-t,n-2]$, and $X_{n-1}\neq X_{n-1-d}$, $X_{-t-1}\neq X_{-t-1+d}$.

Applied to $v$ and translated by $k$, it says:

**(B)** $X$ has period $e$ on $B=[\beta,\varepsilon]$ with $\beta=k-t'$ and $\varepsilon=k+c+e-2$; moreover $X_{\varepsilon+1}\ne X_{\varepsilon+1-e}$, $X_{\beta-1}\neq X_{\beta-1+e}$, and $L:=\varepsilon-\beta+1=c+e-1+t'\ge c+e+t$.

**Lemma 3.2 (weak Fine–Wilf; `fine_wilf`).** If $X$ has periods $p,q>0$ on an interval of length at least $p+q$, it has period $\gcd(p,q)$ there.

*Proof.* Index the interval by $[0,\ell)$. Induct on $p+q$, with $p=q$ immediate and the periods interchanged if necessary to make $p<q$. For $0\le i<i+q-p<\ell$, compare $i$ and $i+q-p$ through $i-p$ if $i\ge p$, and through $i+q$ if $i<p$. In the second case $i+q< p+q\le\ell$. Thus $q-p$ is a period, and induction on $p$ and $q-p$ gives period $\gcd(p,q-p)=\gcd(p,q)$. ∎

**Lemma 3.3 (primitivity; `fw_of`).** If $0<e<d$, no window $[a,a+d+e-1]\subseteq[-t,n-2]$ has period $e$.

*Proof.* Such a window also has period $d$ by (A), so by Lemma 3.2 it has period $g=\gcd(d,e)$, with $0<g\le e<d$ and $g\mid d$. Every residue $k$ modulo $d$ is represented in $[a,a+d)$. Using $X_j=s_{j\bmod d}$ on $A_0$, this gives $s_k=s_{(k+g)\bmod d}$ for all $k<d$. Induction then gives $s_k=s_{k\bmod g}$ for $k<d$, so $s_d$ is a repetition of a block of length $g$, a proper divisor of $d$. This contradicts aperiodicity. ∎

**Theorem 3.4 (abstract form; `Config.main`).** Suppose an $n$-periodic word $X$ satisfies the period and break data of (A) and (B), with $1\le e\le d\le c$, $n=c+d$, $t\ge0$, $L\ge c+e+t$, and with the conclusion of Lemma 3.3 when $e<d$. Then $\varepsilon\equiv c-2\pmod n$.

**Proof of Theorem 1 from Theorem 3.4.** Here $\varepsilon=n-b+c+e-2$, so $n\mid n-b+e$. Since $0<n-b+e<2n$, this forces $b=e=d_2$. ∎

## 4. Proof of Theorem 3.4

Translate $B$ by a multiple of $n$ so that $-t\le\beta\le n-t-1$ (`Config.translate`). The congruence class of $\varepsilon$ is unchanged, and we show $\varepsilon=n+c-2$ (`Config.normalized`).

All index checks below are linear inequalities, which Lean discharges with `omega`. We write $P\ge e$ for $\beta\le n-1-e$ (the run $B$ meets $A_0$ in at least $e$ positions) and $P^*\ge e$ for $\varepsilon\ge n-t-1+e$ (it meets $A_1=A_0+n$ in at least $e$ positions).

**Case $e=d$.**
- If $\beta\le n-1-d$: since $L\ge n+t$ gives $\varepsilon\ge n-1$, both $n-1-d$ and $n-1$ lie in $B$. So $X_{n-1-d}=X_{n-1}$, contradicting (A).
- Otherwise $\beta\ge n-d$, so $\varepsilon\ge 2n-d+t-1\ge n-t-1+d$. Then $X_{n-t-1}=X_{n-t-1+d}$, i.e. $X_{-t-1}=X_{-t-1+d}$, contradicting (A).

So $e<d$ from now on.

**Step 1 (`Config.bounds`): $n-1\le\varepsilon\le 2n-3$.**
- If $\varepsilon\le n-2$, the window $[\beta,\beta+d+e-1]\subseteq B\cap A_0$ has period $e$ (note $L\ge d+e$), contradicting Lemma 3.3.
- If $\varepsilon\ge 2n-2$, the window $[n-t,\,n-t+d+e-1]\subseteq B\cap A_1$ has period $e$; translating by $-n$ again contradicts Lemma 3.3.

**Step 2: four claims.** Each claim is proved by a chain of equalities that contradicts a break. Each step of a chain uses $B$-periodicity, $A_0$-periodicity, or $n$-periodicity at indices that are checked to lie in the relevant interval.

- **Claim U** ($P\ge e\Rightarrow \varepsilon\le n+c-2$). If $\varepsilon\ge n+c-1$, then $X_{n-1}=X_{n-1-e}=X_{c-1-e}=X_{n+c-1-e}=X_{n+c-1}=X_{c-1}=X_{n-1-d}$, contradicting (A).
- **Claim L** ($\varepsilon\le n+c-3\Rightarrow\varepsilon\le n+e-t-2$). If $n+e-t-1\le\varepsilon\le n+c-3$, then $X_{\varepsilon+1}=X_{\varepsilon+1-n}=X_{\varepsilon+1-c}=X_{\varepsilon+1-c-e}=X_{\varepsilon+1-e-n}=X_{\varepsilon+1-e}$, contradicting the right break of $B$. The middle step uses $L\ge c+e$.
- **Claim U\*** ($P^*\ge e\Rightarrow\beta\ge d-t$). If $\beta\le d-t-1$, then $X_{-t-1}=X_{n-t-1}=X_{n-t-1+e}=X_{e-t-1}=X_{e-t-1+d}=X_{d-t-1}$, contradicting (A).
- **Claim L\*** ($\beta\ge d-t+1\Rightarrow\beta\ge n-e$). If $d-t+1\le\beta\le n-e-1$, then $X_{\beta-1}=X_{\beta-1-d}=X_{\beta-1+c}=X_{\beta-1+c+e}=X_{\beta-1+e-d}=X_{\beta-1+e}$, contradicting the left break of $B$.

**Step 3: case analysis.** Since $(n-1-\beta)+(\varepsilon-n+t+1)=L+t-1\ge c+e+2t-1\ge 2e$, at most one of $P$, $P^*$ is below $e$.

- **(a) $P\ge e$ and $P^*\ge e$.** By U and L, either $\varepsilon=n+c-2$ or $\varepsilon\le n+e-t-2$. In the second alternative, U\* and L\* give $\beta=d-t$ or $\beta\ge n-e$. These give $L\le c+e-1$ or $L\le 2e-t-1$ respectively, and both are less than $c+e+t$. So $\varepsilon=n+c-2$.
- **(b) $\beta\ge n-e$.** Impossible by Proposition 4.1.
- **(c) $\varepsilon\le n-t-2+e$.** Apply the reversal $\tilde X_i:=X_{2n-2-t-i}$ (`Config.reflect`). It maps $A_0$ onto $A_1$. By $n$-periodicity, the reflected word on $A_0$ satisfies (A) with its two breaks exchanged, and the exclusion in Lemma 3.3 is preserved. The reflection maps $B$ to $[\tilde\beta,\tilde\varepsilon]=[2n-2-t-\varepsilon,\,2n-2-t-\beta]$, with the breaks exchanged and the same length. By Step 1, $-t\le\tilde\beta\le n-t-1$, and $\tilde\beta\ge n-e$. So the reflected data are in case (b), which is impossible. ∎

**Proposition 4.1 (`Config.caseB`).** In the normalized setting with $e<d$, $\beta\ge n-e$ is impossible.

*Proof.* Step 1 gives $\varepsilon\le 2n-3$, and $L\ge c+e+t$ gives $\varepsilon\ge n+c+t-1$. Put $\kappa=\varepsilon-n$ and $W_j:=X_{\beta+((n+j-\beta)\bmod e)}$. Then $W$ is $e$-periodic, and $W_j=X_{n+j}$ whenever $n+j\in B$ (`Config.runB_mod`). Let $a_s(j)=W_j\oplus W_{j+s}$. The following facts all come from (A), (B) and $n$-periodicity:

- $a_d(-t-1)=1$, since $X_{n-t-1}=X_{-t-1}\ne X_{-t-1+d}=X_{n-t-1+d}$.
- $a_d(j)=0$ for $-t-1<j<\kappa-d+1$, by (A) at $j$.
- $a_d(\kappa-d+1)=1$. Here $W_{\kappa+1}=W_{\kappa+1-e}=X_{\varepsilon+1-e}\neq X_{\varepsilon+1}=X_{\varepsilon+1-d}$; the last step is (A) translated, using $\varepsilon\le 2n-3$.
- $a_c(-1)=1$, since $X_{n-1}\ne X_{n-1-d}=X_{c-1}=X_{n+c-1}$.
- $a_c(j)=0$ for $\beta-n-1<j<-1$. Here $X_{n+j}=X_{n+j-d}=X_{n+j+c}$, where $n+j-d\ge c-e\ge1$.
- $a_c(\beta-n-1)=1$. Here $W_{\beta-n-1}=X_{\beta-1+e}\ne X_{\beta-1}=X_{\beta-1-d}=X_{\beta-1+c}=W_{\beta-n-1+c}$.

Let $m=(c-d)\bmod e$, so $0\le m<e$, $m\le c-d$, and $a_c=a_{d+m}$. Apply the Run Lemma with $f=\beta-n-1$, $f'=-1$, $g=-t-1$, $g'=\kappa-d+1$ (here $g\le f'$). It gives $(n-t-\beta)+(\kappa-d+2)\le e+m\le e+c-d$, that is, $L\le c+e+t-1$. This contradicts $L\ge c+e+t$. ∎

## 5. The Run Lemma

**Run Lemma (`run_lemma`).** Let $W:\mathbb Z\to\{0,1\}$ be $e$-periodic ($e>0$), and let $a_s(j)=W_j\oplus W_{j+s}$. Let $0\le m<e$. Let $f<f'$ satisfy $a_{d+m}(f)=a_{d+m}(f')=1$ and $a_{d+m}=0$ on $(f,f')$. Let $g<g'$ satisfy $a_d(g)=a_d(g')=1$ and $a_d=0$ on $(g,g')$. If $g\le f'$, then $(g-f)+(g'-f')\le e+m$.

*Tools.*
- (Parity; `dw_even`, `dw_next`.) Every window of length $e$ of $a_s$ contains an even number of ones. Modulo 2 the XOR sum is $\sum_{j}(W_j+W_{j+s})=2\sum_j W_j=0$ over a period. Sums of periodic functions over a period do not depend on the starting point (`cntI_period`). Hence two consecutive ones of $a_s$ are at most $e-1$ apart.
- (XOR identities.) $a_m(j)=a_{d+m}(j)\oplus a_d(j+m)$ (β) and $a_m(j+d)=a_{d+m}(j)\oplus a_d(j)$ (α).
- (Invariants.) For an $e$-periodic word $F$, the number of ones in a window of length $e$ does not depend on the window. Neither does $N_y(F)$, the number of $j$ in a window with $F_j=1$, $F_{j+1}=\dots=F_{j+y}=0$ and $F_{j+y+1}=1$ (`gapInd`, `gapInd_period`). We apply both to $F_1=a_m$ and $F_3=a_m(\cdot+d)$, which are two readings of the same periodic word.

*Proof.*
**Case $m=0$.** Here $a_{d+m}=a_d$, and $f'-f\le e-1$. Since a one of the word cannot lie strictly between two consecutive ones:
- if $g<f$ then $g'\le f$;
- if $g=f$ then $g'=f'$;
- if $g>f$ then $g=f'$ and $g'\le f+e$.

In every case the sum is at most $e$.

**Case $m\ge1$.** Suppose the sum is at least $e+m+1$. The two summands are individually at most $e-1$ by parity and $g\le f'$. Hence $g\ge f+m+2$ and $g'\ge f'+m+2$. Put $A=g'-e$, $x=f'-g+m-1$, and $y=A-m-f-1$. The assumed sum bound gives $A\ge f+m+1+(f'-g)$, so $y\ge f'-g$. We have
\[
g-e<f\le f+m<A<g\le f'<f+e,\qquad f+e+m<g'.
\]
Here $A<g$ follows from $g'-g\le e-1$, and the last bound follows from $A\ge f+m+1$. Let $Y_1$ be $a_d$ on $(A,g)$ and $Y_2$ be $a_{d+m}$ on $(f',f+e)$. We read both words on $[f,f+e)$.

By (β), $a_m(f)=1$. The shift by $m$ takes $(f,A-m)$ into $(g-e,A)$, where $a_d$ is zero. On $[A-m,g-m]$ the shift reads $1Y_1 1$ while $a_{d+m}$ is zero. On $(g-m,f']$ the shift lies in $(g,g')$, so this portion of $a_m$ has $x$ zeros followed by the one at $f'$. The remaining positions read $Y_2$, again because their shifts lie in $(g,g')$. In all, $a_m$ reads
\[
1\,0^y\,1\,Y_1\,1\,0^x\,1\,Y_2 .
\]

By (α), $F_3(f)=1$. On $(f,f')$ the identity reduces to $F_3=a_d$, and on $(g,f+e)$ it reduces to $F_3=a_{d+m}$. If $g=f'$, the two ones at $g$ cancel in (α), so $F_3$ reads
\[
1\,0^{y+m}\,1\,Y_1\,0\,Y_2 .
\]
This has two fewer ones in one period than $a_m$, a contradiction.

If $g<f'$, the one at $g$ comes from $a_d$ and the one at $f'$ comes from $a_{d+m}$. In this case $F_3$ reads
\[
1\,0^{y+m}\,1\,Y_1\,1\,0^{x-m}\,1\,Y_2 .
\]
The gaps in the common portions $1Y_1 1$ and $1Y_2 1$ contribute equally to $N_y$ in both readings. The terminal one following $Y_2$ is the initial one of the next period. The first reading contributes at least one additional gap of length $y$. Since $m>0$, the gap of length $y+m$ in the second reading cannot account for it. Invariance of $N_y$ therefore forces $x-m=y$. But $x-m=f'-g-1<y$ by the assumed bound. This is a contradiction. ∎

(The run-length count replaces the comparison of zero-run multisets in the original write-up. Only the single length $y$ is needed.)

## 6. Proof of Theorem 2 (add is well defined; Lemma 3(ii))

Uniqueness is immediate: if $t_1<t_2$ both satisfied Definition 3, the matches for $t_2$ would include position $t_1$, where $t_1$ has a mismatch.

For existence with $t<n-c$, suppose no mismatch occurs for $t<n-c$. Let $U_k=w_{k\bmod\delta}$ be the $\delta$-periodic word on $w_\delta$. The matches give $w_k=U_{k-n}$ for $c\le k\le n-1$. By the block structure $w_k=U_k$ for $c\le k\le c+\delta-2$, while $w_{c+\delta-1}=\bar U_{c+\delta-1}$. So on the window $[c,c+\delta)$ the shift-difference word $U_k\oplus U_{k-n}$ has exactly one $1$, against parity (`isAdd_exists`). The least mismatch is then $\mathrm{add}(w)$, and $\mathrm{add}(w)<n-c$. For $w=s$ and $\delta=d=n-c$ this gives $t\le d-1$. This bound is independent of the main argument.

## 7. Formalization

Lean 4.34.1 with Mathlib at revision `d13f23b7…`, specific imports only. There are no `sorry`, `admit`, `axiom`, `unsafe` or `native_decide`. Every endpoint depends only on `propext`, `Classical.choice` and `Quot.sound`, and the `decide` instances use only `propext` and `Quot.sound`. The nine modules total 1476 lines and are listed in import order in `LEAN-SOURCE-APPENDIX.md`.

| Module | Content |
|---|---|
| RightShiftDefs | Source definitions (§1) and `Conjecture1` |
| RightShiftCount | Interval sums, period invariance, parity of shift-difference words |
| RightShiftRun | Zero-run counts, transfer, XOR identities, `run_lemma` |
| RightShiftCore | `Config` (facts (A), (B)), translation, reversal, Claims U/L/U\*/L\*, `caseB`, `normalized`, `main` |
| RightShiftBridge | Periodic extension, block lemmas, `runData` (Lemma 3.1), `ext_rotR` |
| RightShiftFineWilf | `fine_wilf`, `fw_of` (Lemma 3.3) |
| RightShiftAdd | `isAdd_unique`, `isAdd_exists`, `isAdd_lt`, the function `add` |
| RightShiftMain | `conjecture1_struct`, `conjecture1`, `conjecture1_add`, `add_well_defined` |
| RightShiftExamples | `instance4`, `instance11`, `instance6_equal_add`, `strict_needed`, `hypotheses_satisfiable`, axiom prints |

**Differences from the original write-up.**
- The case $e=d$ is closed directly by the breaks of (A), without the "two maximal runs coincide" step.
- The bound $t\le d-1$ is proved by parity but is not used.
- The Run Lemma uses the single count $N_y$ instead of multisets.
- Case (c) is reduced to case (b) by an explicit reversal of the abstract data.

## 8. Prior art

The only arXiv version is v1, submitted 1 February 2026. It states Conjecture 1 as open. The IEEE version appeared online on 20 May 2026. The available metadata does not establish the acceptance date. The journal abstract describes the same structure and enumeration results in the $\lfloor 3n/4\rfloor$ regime. The journal full text was unavailable for review.

Liang, Zeng and Tang study sequences of nonlinear complexity at least $n/2$ using companion vertices in de Bruijn cycles. Their ISIT 2026 abstract describes a construction for cycles with a diameter constraint. The full text was unavailable for review, and the deposited bibliography does not establish a forward citation to Yuan, Li and Zeng. OpenAlex returned no citing works for the journal and preprint cluster. The Omega and Principia searches returned no matching solution. The cross-model review found no published full-range proof or equivalent of the Run Lemma in the sources checked. [arXiv v1](https://arxiv.org/abs/2602.01134) · [Journal record](https://doi.org/10.1109/TIT.2026.3695307) · [ISIT record](https://doi.org/10.1109/ISIT62367.2026.11653661)

## 9. Significance

Lemma 7 of the preprint proves $b=d_2$ under the additional condition $d+d_2\le c+t+t'+1$. Its proof compares Hamming weights of binary windows. The full-range argument uses the lengths of the zero-runs of a shift-difference word to exclude the short-overlap configuration. The conjecture serves the authors’ classification and enumeration of sequences of high nonlinear complexity. They identify extensions of Proposition 1 and Corollary 3 as applications. The theorem proved here is the shift-distance conclusion.

## 10. Checks

An independent exact check enumerated every primitive starting block for $2\le n\le24$, every admissible $c$, every nonzero right shift, and every allowed target spacing. All 308 strict increases gave $b=d_2$, including 234 at $c=\lceil n/2\rceil$. The same check found 1168 failures of the non-strict variant.

For the Run Lemma the check considered every binary word of period $1\le e\le12$ and every pair of shift residues. Translating $f$ to zero and testing the greatest break $g\le f'$ suffices because moving to an earlier break decreases both $g$ and its successor. All 416,922 tested pairs met the bound, and 2,090 attained equality. The script and output accompany the cross-model review.
