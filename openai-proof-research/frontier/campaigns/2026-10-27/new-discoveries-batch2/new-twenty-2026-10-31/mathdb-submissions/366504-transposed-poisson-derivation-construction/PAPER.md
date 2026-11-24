# A counterexample to the derivation construction for transposed Poisson 3-Lie algebras

*Manuscript for MathDB 366504. Claude Opus 5.5 produced the proof, the Lean formalization, the original manuscript, and the first review. GPT-6.2 Sol performed the cross-model review and edited this manuscript. The declaration names in brackets identify formal statements used in the proof. The appendix contains the unchanged Lean source.*

## Abstract

We address the signed version of the derivation construction conjecture of Bai, Bai, Guo and Wu, as stated by Mashurov. Given a transposed Poisson $n$-Lie algebra $(L,\cdot,[\cdot,\dots,\cdot])$ and a derivation $D$ of both operations, the conjecture asserts that
$$\mu(a_1,\dots,a_{n+1})=\sum_{i=1}^{n+1}(-1)^{i-1}D(a_i)[a_1,\dots,\hat a_i,\dots,a_{n+1}]$$
makes $(L,\cdot,\mu)$ a transposed Poisson $(n+1)$-Lie algebra. We show that this fails for $n=3$ over every field of characteristic $\neq2$.

The counterexample is $L=M_3(K)\otimes_K K[t]$ with $D=d/dt$, where $M_3$ is an explicit 15-dimensional graded transposed Poisson 3-Lie algebra with integer structure constants. At seven explicit elements, the 4-ary Filippov identity for $\mu$ has defect $-2f_{14}\neq0$. So $(L,\mu)$ is not even a 4-Lie algebra. Lean 4 with Mathlib defines the signed statement and proves its negation for every field of characteristic zero. It also proves the failure of the unsigned formula in characteristic zero.

## 1. The conjecture and the definitions

### 1.1 Source text

MathDB record 366504 states the signed derivation construction in Conjecture 1.1 of Mashurov’s arXiv v3 [3]. For any integer $n\ge 2$, take a transposed Poisson $n$-Lie algebra $(L,\cdot,[\cdot,\ldots,\cdot])$ and a common derivation $D$ of its two operations. Form
$$\mu(a_1,\dots,a_{n+1})=\sum_{i=1}^{n+1}(-1)^{i-1}D(a_i)[a_1,\dots,\hat a_i,\dots,a_{n+1}],$$
where $\hat a_i$ denotes omission. The conjecture asserts that $(L,\cdot,\mu)$ is a transposed Poisson $(n+1)$-Lie algebra.

In the arXiv version of Bai–Bai–Guo–Wu [1], Conjecture 4.9 prints the sum without $(-1)^{i-1}$. In the same work, the binary-to-ternary formula (38) is the signed cyclic sum $[x,y,z]=D(x)[y,z]+D(y)[z,x]+D(z)[x,y]$. Huang–Chen–Chen–Ding, Mashurov, and Beites–Ferreira–Kaygorodov all state the general construction with the sign. Section 5 treats the unsigned formula separately.

The bracket of an $n$-Lie algebra is skew-symmetric and multilinear and satisfies the Filippov identity (Mashurov, Def. 2.1)
$$[[x_1,\ldots,x_n],y_2,\ldots,y_n]=\sum_{i=1}^n[x_1,\ldots,x_{i-1},[x_i,y_2,\ldots,y_n],x_{i+1},\ldots,x_n]. \quad (1)$$
Transposed Poisson $n$-Lie algebras additionally carry a commutative associative product with
$$n\,h\,[a_1,\ldots,a_n]=\sum_{i=1}^n[a_1,\ldots,h a_i,\ldots,a_n] \quad (3)$$
for every $h,a_1,\ldots,a_n$ (Mashurov, Def. 2.4 and Bai–Bai–Guo–Wu, Def. 4.8). A common derivation is a $K$-linear map $D$ satisfying
$$D(uv)=D(u)v+uD(v),\qquad D([x_1,\ldots,x_n])=\sum_{i=1}^n[x_1,\ldots,D(x_i),\ldots,x_n]$$
(Huang–Chen–Chen–Ding, Def. 3.1). Mashurov works over $\mathbb C$ and discusses fields of characteristic zero. The conjecture permits a nonunital product and an infinite-dimensional vector space.

### 1.2 Lean transcription (module `TPDefs`)

Lean indexes the arguments by `Fin n`, that is $0,\dots,n-1$. Source index $i$ is Lean index $i-1$, so $(-1)^{i-1}$ becomes `(-1)^(i : ℕ)`. The tuple with the $i$-th entry omitted, $(a_1,\dots,\hat a_i,\dots,a_{n+1})$, is `a ∘ i.succAbove`. The tuple $(z,y_2,\dots,y_n)$ of identity (1) is `headTail z y` with `y : Fin (n-1) → L`. Replacing the $i$-th argument is `Function.update x i _`.

```lean
def headTail {n : ℕ} (z : L) (y : Fin (n - 1) → L) : Fin n → L :=
  fun j => if h : (j : ℕ) = 0 then z else y ⟨(j : ℕ) - 1, by have := j.isLt; omega⟩

structure IsNLie (n : ℕ) (br : (Fin n → L) → L) : Prop where
  multilinear : ∀ (x : Fin n → L) (i : Fin n) (c : K) (u v : L),
    br (Function.update x i (c • u + v)) =
      c • br (Function.update x i u) + br (Function.update x i v)
  skew : ∀ (x : Fin n → L) (i j : Fin n), i ≠ j → br (x ∘ Equiv.swap i j) = -br x
  jacobi : ∀ (x : Fin n → L) (y : Fin (n - 1) → L),
    br (headTail (br x) y) = ∑ i, br (Function.update x i (br (headTail (x i) y)))

structure IsTPnLie (n : ℕ) (mul : L →ₗ[K] L →ₗ[K] L) (br : (Fin n → L) → L) : Prop where
  comm : ∀ x y : L, mul x y = mul y x
  assoc : ∀ x y z : L, mul (mul x y) z = mul x (mul y z)
  nLie : IsNLie K n br
  leibniz : ∀ (h : L) (a : Fin n → L),
    (n : K) • mul h (br a) = ∑ i, br (Function.update a i (mul h (a i)))

structure IsDerivation {n : ℕ} (mul : L →ₗ[K] L →ₗ[K] L) (br : (Fin n → L) → L)
    (D : L →ₗ[K] L) : Prop where
  mul_rule : ∀ u v : L, D (mul u v) = mul (D u) v + mul u (D v)
  br_rule : ∀ x : Fin n → L, D (br x) = ∑ i, br (Function.update x i (D (x i)))

def mu {n : ℕ} (mul : L →ₗ[K] L →ₗ[K] L) (br : (Fin n → L) → L) (D : L →ₗ[K] L) :
    (Fin (n + 1) → L) → L :=
  fun a => ∑ i : Fin (n + 1), ((-1 : K) ^ (i : ℕ)) • mul (D (a i)) (br (a ∘ i.succAbove))

def DerivationConstructionConjecture (K : Type) [Field K] : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ (L : Type) [AddCommGroup L] [Module K L]
    (mul : L →ₗ[K] L →ₗ[K] L) (br : (Fin n → L) → L), IsTPnLie K n mul br →
    ∀ D : L →ₗ[K] L, IsDerivation K mul br D → IsTPnLie K (n + 1) mul (mu K mul br D)
```

Notes on fidelity:
- **The product.** A commutative associative algebra over $K$ has a $K$-bilinear product, `L →ₗ[K] L →ₗ[K] L`.
- **The bracket.** It is a function on $n$-tuples. Its multilinearity and its skew-symmetry ("exchanging two arguments changes the sign") are fields of `IsNLie`, as in the source. The conclusion of the conjecture therefore requires $\mu$ to be multilinear, skew-symmetric, and to satisfy (1) and (3). The counterexample violates (1).
- **The derivation.** $D$ is a $K$-linear map.
- **`muUnsigned`.** The unsigned operation of BBGW is `muUnsigned`, and `DerivationConstructionConjectureUnsigned` is the same statement with `muUnsigned` in place of `mu`.

Three lemmas display the indexing by unfolding it completely:
- `jacobi_three_iff` and `jacobi_four_iff` show that the `jacobi` field for $n=3$ and $n=4$ is exactly identity (1) written out. For example, for $n=4$ it reads
  $$[[x_1,x_2,x_3,x_4],y_2,y_3,y_4]=[[x_1,y_2,y_3,y_4],x_2,x_3,x_4]+[x_1,[x_2,y_2,y_3,y_4],x_3,x_4]+[x_1,x_2,[x_3,y_2,y_3,y_4],x_4]+[x_1,x_2,x_3,[x_4,y_2,y_3,y_4]].$$
- `mu_three_apply` shows that for $n=3$
  $$\mu(a_1,a_2,a_3,a_4)=D(a_1)[a_2,a_3,a_4]-D(a_2)[a_1,a_3,a_4]+D(a_3)[a_1,a_2,a_4]-D(a_4)[a_1,a_2,a_3].$$

## 2. Main result

**Theorem.** Let $K$ be a field of characteristic $0$. The derivation construction conjecture fails over $K$ for $n=3$. There is a transposed Poisson 3-Lie algebra $(L,\cdot,[\cdot,\cdot,\cdot])$ over $K$ and a derivation $D$ of both operations such that $(L,\mu)$ violates the 4-ary generalized Jacobi identity (1). [`not_derivationConstructionConjecture`, with the instances `mathdb366504_rat` for $\mathbb Q$ and `mathdb366504_complex` for $\mathbb C$]

The structure identities and defect calculation hold over any commutative ring $K$. Since the defect coefficient is $-2$, the same counterexample works over every field of characteristic other than two. The Lean refutation is stated for characteristic zero.

### 2.1 The algebra $M_3$

Let $R$ be a commutative ring and write $M_3(R)=R^{15}$ with basis $f_0,\dots,f_{14}$. Use the following integer structure constants, interpreted in $R$. The commutative product has entries
$$f_0f_1=f_2,\quad f_1f_3=f_4,\quad f_1f_5=-f_6,\quad f_1f_{11}=f_{12},\quad f_1f_{13}=f_{14},$$
$$f_3f_3=f_7,\quad f_3f_5=f_8,\quad f_3f_9=-f_{12},\quad f_3f_{10}=-f_{14},\quad f_5f_9=-f_{14}.$$
The alternating bracket has the following entries on increasing index triples
$$\begin{aligned}
&[f_0,f_1,f_3]=-f_5,\ [f_0,f_1,f_7]=-3f_8,\ [f_0,f_1,f_9]=-f_{10},\ [f_0,f_1,f_{11}]=-4f_{13},\ [f_0,f_1,f_{12}]=-3f_{14},\\
&[f_1,f_2,f_3]=-3f_6,\ [f_1,f_2,f_{11}]=9f_{14},\ [f_1,f_3,f_4]=-f_9,\ [f_1,f_3,f_6]=f_{10},\ [f_1,f_3,f_7]=-f_{11},\\
&[f_1,f_3,f_8]=-f_{13},\ [f_1,f_4,f_5]=f_{10},\ [f_1,f_4,f_7]=-3f_{12},\ [f_1,f_4,f_8]=-3f_{14},\ [f_1,f_5,f_7]=-f_{13},\ [f_1,f_6,f_7]=3f_{14}.
\end{aligned}$$
The two tables specify all entries, with unlisted entries zero up to commutativity or alternation. In coordinates, the $f_o$-coefficient of $[u,v,w]$ is $\sum c^{o}_{ijk}\det\begin{pmatrix}u_i&u_j&u_k\\v_i&v_j&v_k\\w_i&w_j&w_k\end{pmatrix}$, summed over the listed entries $[f_i,f_j,f_k]=c^o_{ijk}f_o$. [`mulR`, `brR`, `det3`; the two coordinate tables are generated by `scripts/gen_m3.py` from the proof lane's `out/M3int.json`, and the generated text occurs verbatim in `TPM3.lean`.]

**Proposition 1.** For every commutative ring $R$, $(M_3,\cdot,[\cdot,\cdot,\cdot])$ is a transposed Poisson 3-Lie algebra over $R$.

*Proof.* The coordinate formulas give a commutative bilinear product and an alternating trilinear bracket. For associativity, the transposed Leibniz rule $3h[u,v,w]=[hu,v,w]+[u,hv,w]+[u,v,hw]$, and
$$[[a,b,c],d,e]=[[a,d,e],b,c]+[a,[b,d,e],c]+[a,b,[c,d,e]],$$
multilinearity reduces each identity to tuples of basis vectors. The differences vanish over $\mathbb Z$ when evaluated with the displayed tables, hence after extension to $R$. The accompanying [integer checker](verify_witness.py) verifies all 3,375 ordered associativity triples, 50,625 ordered Leibniz tuples, and the 47,775 Filippov tuples with increasing triples and pairs. For that last check the difference is alternating in each of the two groups of arguments, so this range suffices. The Lean lemmas check the identities directly in coordinates. [`mulR_comm`, `mulR_assoc`, `mulR_left`, `mulR_right`, `brR_first`, `brR_second`, `brR_third`, `brR_swap12`, `brR_swap13`, `brR_swap23`, `brR_leibniz`, `brR_jacobi`] ∎

The table is graded by multidegree in $a=f_3$, $b=f_1$, $c=f_0$. In basis order the degrees are
$$ (0,0,1),(0,1,0),(0,1,1),(1,0,0),(1,1,0),(1,1,1),(1,2,1),(2,0,0), $$
$$ (2,1,1),(2,2,0),(2,3,1),(3,1,0),(3,2,0),(3,2,1),(3,3,1). $$

The proof lane found the table over $\mathbb Q$ by truncating the free algebra on $a,b,c$ at multidegree $(3,3,1)$ and taking the quotient by the largest graded ideal on which a top-component functional vanishes. The table itself gives a way to see this characterization. Its basis is generated by $a,b,c$, and the functional extracting the $f_{14}$ coefficient pulls back to the free truncation. Each basis line, of a distinct multidegree, admits an iterated product or bracket with basis elements that has nonzero $f_{14}$ coefficient, as checked by the accompanying script. The largest graded ideal annihilated by the pulled-back functional is therefore the kernel of this quotient. In the quotient $f_5=[a,b,c]$ and $f_{14}=\frac{1}{9}[[a^2,ab,b],b,c]$. The explicit verification of the table above suffices for the result.

### 2.2 Polynomial extension and the derivation

**Proposition 2.** Let $K$ be a commutative ring and $L=M_3(K)\otimes_K K[t]$. Concretely, $L=K[t]^{15}$, with the operations of $M_3$ applied over the coefficient ring $K[t]$, viewed as a $K$-module. Then $(L,\cdot,[\cdot,\cdot,\cdot])$ is a transposed Poisson 3-Lie algebra over $K$, and $D=d/dt$, applied coordinatewise, is a $K$-linear derivation of both operations. [`witness_isTP`, `witness_isDerivation`]

*Proof.* Proposition 1 with $R=K[t]$ gives every identity in Definitions 2.1 and 2.4 for $K[t]$-coefficients, hence for $K$-coefficients: restrict scalars along the constant polynomial map $C:K\to K[t]$, so $c$ acts by multiplying the coordinates by $C(c)$. The structure constants are integers, so $D$ kills them. The product rule $\frac{d}{dt}(pq)=p'q+pq'$ then shows, coordinate by coordinate, that $D(uv)=D(u)v+uD(v)$ and $D[u,v,w]=[Du,v,w]+[u,Dv,w]+[u,v,Dw]$. [`derivative_mulR`, `derivative_brR`, each by `ring` after `Polynomial.derivative_mul`.] ∎

The witness $L$ is infinite-dimensional over $K$. It also contains a 59-dimensional witness over $K$: take the span of $f_i t^j$ with $0\le j\le\deg_a f_i+\deg_b f_i$. Summing the upper bounds plus one for each $i$ gives 59. The bounds add under either operation and are preserved by $D$, which lowers $t$-degree. This subalgebra contains the displayed inputs. The Lean proof uses the full polynomial extension.

### 2.3 The defect

Put $a=f_3$, $b=f_1$, $c=f_0$ (all in $M_3\otimes1$), and $at=f_3\otimes t$, $bt=f_1\otimes t$. Then $Da=Db=Dc=0$, $D(at)=a$ and $D(bt)=b$. Also $Df_6=Df_8=0$. [`Dl_ea`, …, `Dl_f6`]

**Proposition 3.** At $x=(a,b,at,c)$ and $y=(bt,a,b)$,
$$\mu(\mu(x_1,x_2,x_3,x_4),y_2,y_3,y_4)-\sum_{i=1}^4\mu(x_1,\dots,\mu(x_i,y_2,y_3,y_4),\dots,x_4)=-2f_{14}\neq0 .$$
[`filippov_defect`, `filippov_defect_ne_zero`]

*Proof.* We use $\mu(a_1,a_2,a_3,a_4)=D(a_1)[a_2,a_3,a_4]-D(a_2)[a_1,a_3,a_4]+D(a_3)[a_1,a_2,a_4]-D(a_4)[a_1,a_2,a_3]$. A term whose $D$-factor is $0$ drops out. We need these brackets and products from the table, using alternation for reordered entries. [`br_abc`, `br_f8ab`, `br_cab`, `br_abf6`, `mul_af5`, `mul_bf13`, `mul_bf5`, `mul_anf10`]
- $[a,b,c]=[f_3,f_1,f_0]=f_5$ and $a\cdot f_5=f_8$.
- $[f_8,a,b]=[f_8,f_3,f_1]=f_{13}$ and $b\cdot f_{13}=f_{14}$.
- $[c,a,b]=[f_0,f_3,f_1]=f_5$ and $b\cdot f_5=-f_6$.
- $[a,b,f_6]=[f_3,f_1,f_6]=-f_{10}$ and $a\cdot(-f_{10})=f_{14}$.
- $[a,a,b]=[b,a,b]=0$, and also $[at,a,b]=t[a,a,b]=0$ and $[bt,a,b]=0$.

Now evaluate each piece. [`mu_x`, `mu_lhs`, `mu_r0`–`mu_r3`, `mu_s0`–`mu_s3`]
- $\mu(a,b,at,c)=D(at)[a,b,c]=a\cdot f_5=f_8$.
- **Left side:** $\mu(f_8,bt,a,b)=-D(bt)[f_8,a,b]=-b\cdot f_{13}=-f_{14}$.
- $i=1$: $\mu(a,bt,a,b)=-b[a,a,b]=0$, so the summand is $\mu(0,b,at,c)=0$.
- $i=2$: $\mu(b,bt,a,b)=-b[b,a,b]=0$, so the summand is $\mu(a,0,at,c)=0$.
- $i=3$: $\mu(at,bt,a,b)=a[bt,a,b]-b[at,a,b]=0$, so the summand is $\mu(a,b,0,c)=0$.
- $i=4$: $\mu(c,bt,a,b)=-b[c,a,b]=-b\cdot f_5=f_6$, and the summand is $\mu(a,b,at,f_6)=D(at)[a,b,f_6]=a\cdot(-f_{10})=f_{14}$.

Hence the right side is $f_{14}$, and the defect is $-f_{14}-f_{14}=-2f_{14}$, whose $f_{14}$-coordinate $-2$ is nonzero when $2\ne0$ in $K$. ∎

*Proof of the Theorem.* Suppose the conjecture held over $K$. Apply it with $n=3$ to $(L,\cdot,[\cdot,\cdot,\cdot])$ and $D$ from Proposition 2. Then $(L,\cdot,\mu)$ would be a transposed Poisson 4-Lie algebra. In particular, identity (1) for $n=4$ would hold at $x=(a,b,at,c)$, $y=(bt,a,b)$, and the defect in Proposition 3 would be $0$, a contradiction. [`mu_not_jacobi`, `not_derivationConstructionConjecture`] ∎

## 3. Why it fails: the defect identity

This section explains the counterexample and is not needed for the proof. Huang, Chen, Chen and Ding proved the conjecture for *strong* transposed Poisson $n$-Lie algebras. Their condition, in Mashurov's Definition 2.6 for $n=3$, is the vanishing of
$$S(h;y_1,y_2,x_1,x_2)=y_1[hy_2,x_1,x_2]-y_2[hy_1,x_1,x_2]+hx_1[y_1,y_2,x_2]-hx_2[y_1,y_2,x_1].$$
The following specialization of the Filippov defect identifies where the strong condition enters.

Let $L$ be a TP 3-Lie algebra with derivation $D$, and suppose $D$ vanishes on $x_1,x_2,x_4,y_3,y_4$ while $D^2x_3=D^2y_2=0$. Then
$$\mathrm{Fil}_\mu(x_1,x_2,x_3,x_4;y_2,y_3,y_4)=S([x_1,x_2,x_4];Dx_3,Dy_2,y_3,y_4).$$

*Proof sketch.* Write $p=Dx_3$, $q=Dy_2$, $u=y_3$, $v=y_4$, $w=[x_1,x_2,x_4]$. Expanding $\mu$ term by term gives
$$\mathrm{Fil}_\mu=-q[pw,u,v]+p\big([q[x_1,u,v],x_2,x_4]-[q[x_2,u,v],x_1,x_4]+[q[x_4,u,v],x_1,x_2]\big)-pw[q,u,v]+qw[p,u,v].$$
Here $D$ kills $pw$, the left inner value. On the right, the inner replacement at position 3 contributes $w(p[q,u,v]-q[p,u,v])$, and the other three positions give the bracketed sum with the displayed signs after subtraction. By identity (4) of Mashurov's Prop. 2.5, that bracketed sum is $[qw,u,v]$. Subtracting $S(w;p,q,u,v)$ now leaves
$$-w\big(p[q,u,v]-q[p,u,v]+u[p,q,v]-v[p,q,u]\big)=0$$
by identity (5) on $(p,q,u,v)$.

In the counterexample, the defect equals $S([a,b,c];a,b,a,b)=a[[a,b,c]b,a,b]-b[[a,b,c]a,a,b]=-2f_{14}$, computed in $M_3$.

The obstruction is the strong-condition polynomial evaluated at a bracket $h=[x_1,x_2,x_4]$. Mashurov’s rank computation establishes the nonvanishing of $S(h,\dots)$ with $h$ a free generator in degree five. The specialization $h=[x_1,x_2,x_4]$ lies in total degree seven and involves two brackets. Its nonvanishing is certified by the table of $M_3$.

## 4. Remarks on scope

- **Range.** The signed construction fails at $n=3$ in the conjectured range $n\ge2$. Bai et al. proved the signed $n=2$ case.
- **Product.** The witness is nilpotent and nonunital. The source permits this. Mashurov’s §3 proves strongness for unital algebras under its additional compatibility conditions.
- **Characteristic.** The defect is $-2f_{14}$, so the counterexample works over every field of characteristic $\neq2$, in particular over $\mathbb Q$ and $\mathbb C$.
- **The Leibniz rule.** The raised bracket is multilinear and alternating by the signed omission sum. It still satisfies (3) for general $n$. In the sum of $\mu$ with $h a_i$ inserted in each slot, the terms where $D$ hits $h$ are $D(h)\sum_i(-1)^{i-1}a_i[a_1,\ldots,\hat a_i,\ldots,a_{n+1}]$, which is zero by (5). For each derivative factor $D(a_j)$, the insertions in the other $n$ slots sum to $n h$ times the original bracket by (3). The insertion in slot $j$ contributes the remaining $h$, giving the coefficient $(n+1)h$ on $\mu$. The Lean proof uses the separate Filippov failure.

## 5. The unsigned version (BBGW's printed formula)

On the same $L$ and $D$, the unsigned operation $\mu'(x_1,\dots,x_4)=\sum_iD(x_i)[x_1,\dots,\check x_i,\dots,x_4]$ is not skew-symmetric. Indeed, $[c,b,a]=[f_0,f_1,f_3]=-f_5$, so $\mu'(c,bt,b,a)=D(bt)[c,b,a]=b\cdot(-f_5)=f_6$, and $\mu'(bt,c,b,a)=D(bt)[c,b,a]=f_6$ as well. [`br_cba`, `mul_bnf5`] So exchanging the first two arguments does not change the sign, and $f_6\neq-f_6$ when $2\neq0$. Hence the literal BBGW statement is also false over every field of characteristic 0. [`muU_x`, `muU_swap`, `muU_not_skew`, `not_derivationConstructionConjectureUnsigned`] This separate failure concerns the missing alternating signs in the unsigned formula.

## 6. Significance

The signed construction generalizes the first arity step of Bai, Bai, Guo and Wu. The counterexample isolates a Filippov obstruction at the next arity. The polynomial extension and sparse coordinate checks are standard. The extra calculation is to exhibit a nonzero strong-condition value with its first argument itself a bracket, so that the value occurs in the Filippov defect of the raised bracket.

## 7. Prior work

Bai–Bai–Guo–Wu proved the signed $n=2$ case in Theorem 4.5 and Proposition 4.7 of [1]. Huang–Chen–Chen–Ding proved the conjecture on strong inputs in Theorems 3.3–3.4 of [2]. Mashurov’s Proposition 5.1 establishes failure of strongness in the free ternary algebra using a rank comparison of 46 and 47 in degree five [3]. The 15 November 2026 arXiv v6 of Beites–Ferreira–Kaygorodov still poses the signed problem in Question 37, citing the strong-case theorem and the free-algebra obstruction [4].

The comparison with Mashurov uses arXiv v3, dated 15 April 2025. The indexed journal record reports acceptance on 8 June 2026 and online publication on 3 July 2026. The journal full text was unavailable for comparison. The detailed literature checks are in the accompanying cross-model review.

## 8. Formalization

The six modules are `TPDefs`, `TPM3`, `TPM3Jacobi`, `TPWitness`, `TPEval` and `TPCounterexample`, 743 lines in all. The original packet’s `LEAN-SOURCE-APPENDIX.md` lists them byte for byte. They were built with Lean 4.34.1 and Mathlib `d13f23b7…` through the 32 GiB runner, pinned to cores 16 and 17, then kernel-checked with `leanchecker`.

The main endpoint is

```lean
theorem not_derivationConstructionConjecture (K : Type) [Field K] [CharZero K] :
    ¬ DerivationConstructionConjecture K
```

It depends only on `propext`, `Classical.choice` and `Quot.sound`. Full statements, the axiom output and receipts are in the original packet’s `REPORT.md`. The root replay independently rebuilt all six modules from the appendix and kernel-checked each one.

## References

1. C. Bai, R. Bai, L. Guo, Y. Wu, *Transposed Poisson algebras, Novikov–Poisson algebras and 3-Lie algebras*, arXiv:2005.01110; J. Algebra 632 (2023) 535–566.
2. J. Huang, X. Chen, Z. Chen, M. Ding, *On a conjecture of transposed Poisson n-Lie algebras*, arXiv:2312.04010; AIMS Math. 9(3) (2024) 6709–6733.
3. F. Mashurov, *On the transposed Poisson n-Lie algebras*, arXiv:2501.01714; Comm. Algebra (2026).
4. P. D. Beites, B. L. M. Ferreira, I. Kaygorodov, *Transposed Poisson structures*, arXiv:2207.00281 (v6, 15 Nov 2026); Results Math. 79 (2024), no. 2, 93.
5. V. T. Filippov, *n-Lie algebras*, Sib. Mat. Zh. 26 (1985) 126–140.
