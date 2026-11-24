# Three sporadic entropy comparisons on the ordered six-simplex

## Formal certification scope

Stage-2 continuation manuscript. The literal theorem `McConnell.mcconnell_conj19` has been proved in Lean with no hypotheses beyond `InD6`, and prints only `[propext, Classical.choice, Quot.sound]`. All 17 modules have been rebuilt and independently kernel-checked from the byte-exact appendix in a fresh empty replay directory; REPORT.md records the receipts. The nine stage-1 source modules are retained verbatim.

## Source definitions, verbatim mathematical transcription

Source: G. McConnell, arXiv:1209.2674v1, §§I.A, I.C and II.G.2.
The source defines the probability simplex as
“∆_N = {(p_1, p_2, …, p_{N+1}) ∈ ℝ^{N+1} : ∑_{i=1}^{N+1} p_i = 1 and p_i ≥ 0 for all i}.”
Its entropy and mutual information definitions are:
“We will often write H(x) = −x log x for x ∈ [0, 1]”
and “I(P) = ∑_{i=1}^m H(r_i) + ∑_{j=1}^n H(c_j) − ∑_{k=1}^{mn} H(p_k).”
Here r_i and c_j are the row and column sums. The explicit convention paragraph states:
“In order to keep the notation consistent with that of majorisation, we have adopted the convention that σ ▷ σ′ corresponds to I(P^σ) ≤ I(P^σ′) for all P ∈ M_{mn}.”
The earlier non-negative-difference sentence has a sign typo; the convention and displayed entropy inequality fix the intended direction.
The source’s displayed definition (3) is “D_{mn} = { p ∈ ∆_{mn−1} : p_1 ≥ p_2 ≥ … ≥ p_{mn} }”, described as “the topological closure of a fundamental domain”. Thus for six entries the closed ordered domain is a≥b≥c≥d≥e≥f≥0 with sum 1. SOURCE-EXCERPTS.txt preserves the original cached text and its hash.

Adjacent Lean transcription:
```lean
noncomputable def cmi (M : Matrix (Fin 2) (Fin 3) ℝ) : ℝ :=
  (∑ i, negMulLog (∑ j, M i j)) + (∑ j, negMulLog (∑ i, M i j))
    - ∑ i, ∑ j, negMulLog (M i j)
def InD6 (p : Fin 6 → ℝ) : Prop :=
  (∀ i j, i ≤ j → p j ≤ p i) ∧ 0 ≤ p 5 ∧ ∑ i, p i = 1
```
Real.negMulLog is −x log x, with value zero at zero. The source's arrays in Conjecture 19, quoted below, correspond row by row to the following Lean definitions, with a,…,f mapped to p 0,…,p 5:

```lean
def M11 (p : Fin 6 → ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  !![p 0, p 1, p 3; p 5, p 2, p 4]
def M37 (p : Fin 6 → ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  !![p 0, p 2, p 5; p 1, p 3, p 4]
def M43 (p : Fin 6 → ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  !![p 0, p 3, p 4; p 1, p 2, p 5]
def M49 (p : Fin 6 → ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  !![p 0, p 3, p 5; p 1, p 2, p 4]
```

 The proved cmi_gap37/43/49 lemmas cancel the entry entropy in Lean for every p; the bridge uses no simplex hypothesis.

## MathDB conjecture, verbatim

The three conjectural sporadics in the entropic order on a parabolic quotient of $S_6$
In the above notation, let the displayed arrays denote the corresponding elements of the parabolic quotient, and let $\rhd$ denote the entropic partial order.

**Three sporadic entropic-order conjectures.** The following three relations hold:

$$
\begin{array}{rcl}
\mathbf{37}\rhd\mathbf{11}:\quad \left(\begin{array}{ccc}a & c & f\\b & d & e\end{array}\right)&\rhd&\left(\begin{array}{ccc}a & b & d\\f & c & e\end{array}\right),\\
\mathbf{43}\rhd\mathbf{11}:\quad \left(\begin{array}{ccc}a & d & e\\b & c & f\end{array}\right)&\rhd&\left(\begin{array}{ccc}a & b & d\\f & c & e\end{array}\right),\\
\mathbf{49}\rhd\mathbf{11}:\quad \left(\begin{array}{ccc}a & d & f\\b & c & e\end{array}\right)&\rhd&\left(\begin{array}{ccc}a & b & d\\f & c & e\end{array}\right).
\end{array}
$$

These are the remaining sporadic relations identified in the paper; the preceding discussion explains that the author was unable to prove them and that their structure does not yield to the techniques used for the other relations.
Gary McConnell, “An entropic partial order on a parabolic quotient of S6”, arXiv:1209.2674 (2012). https://arxiv.org/abs/1209.2674

## Bounded prior-art paragraph supplied by the independent review

The review dated 2026-11-20 found only arXiv v1 and no journal reference for the exact source. Semantic Scholar returned one citing companion, McConnell–Jennings, QIC 14 (2014), 857–887, arXiv:1205.3517; its maximum-CMI theorem is not array 11 and does not resolve these three comparisons. Principia and the campaign record inventory had no duplicate. Four live omega issue/PR searches and two web queries found no resolution. ProbXiv access returned 402 in the proof lane and OpenAlex returned 429. This lane inherits that bounded investigation and claims no fresh exhaustive literature search. The reviewer rated non-routineness at 0.60 and significance low: the source is an obscure 2012 arXiv paper with one self-citation. The source specialist reported failure on these comparisons, but a specialist could still view the solution as a careful elementary calculus verification.


**Status:** corrected ordinary proof, independently reviewed; the full literal Lean endpoint is proved. The fresh extracted rebuild and all kernel checks pass; REPORT.md records the receipts. Prior-art qualification is recorded below and is bounded, not a guarantee of novelty.

## Source and exact statement

Gary McConnell, *An entropic partial order on a parabolic quotient of S6*, arXiv:1209.2674, Conjecture 19 (p.26 in the cached v1). The source says: “Unfortunately I have been unable to prove 37 B 11, 43 B 11 and 49 B 11”. Its displayed conjecture is

```
37 ▷ 11 : [a c f; b d e] ▷ [a b d; f c e]
43 ▷ 11 : [a d e; b c f] ▷ [a b d; f c e]
49 ▷ 11 : [a d f; b c e] ▷ [a b d; f c e].
```

Here a≥b≥c≥d≥e≥f≥0 and a+b+c+d+e+f=1. The entropic relation means that the sum of the Shannon entropies of the row and column marginal vectors on the left is at most the corresponding sum on the right (equivalently, the left mutual information is at most the right, since the six-entry entropy is invariant). This includes equalities and zero entries by the source's closed fundamental domain D6 and entropy continuity.

We prove these three inequalities in the full range. Write φ(t)=t log t for t>0 and φ(0)=0. For each i let F_i be the sum of φ on its five row/column marginals minus the corresponding sum for array 11. Thus the assertion is F_i≥0. We prove it on the whole nonnegative ordered cone; each F_i is homogeneous of degree one, since the coefficients of the log-scale term cancel (both lists have total 2(a+b+c+d+e+f)).

## 1. Reduce to equal largest entries and one inequality

In the positive interior, the a-derivatives are logarithms of the following quotients:

```
37: (a+c+f)(a+b) / ((a+b+d)(a+f))
43: (a+d+e)(a+b) / ((a+b+d)(a+f))
49: (a+d+f)(a+b) / ((a+b+d)(a+f)).
```

Their numerators minus denominators are, respectively,

```
a(c−d)+bc−df,
d(b−f)+(a+b)(e−f),
d(b−f),
```

all nonnegative. Consequently decreasing a to b cannot increase F_i, without any need to renormalize. At a=b=A, F_37=F_43. The column marginals of 49 and 37 agree there, while the row pair for 49 is more spread: its difference has absolute value (c−d)+(e−f), whereas that for 37 has absolute value |(c−d)−(e−f)|. Convexity of φ therefore gives F_49≥F_37.

It remains to prove F≥0 for A≥c≥d≥e≥f≥0, where

```
F(A,c,d,e,f) = φ(A+c+f)+φ(A+d+e)+φ(2A)+φ(c+d)+φ(e+f)
             −φ(2A+d)−φ(c+e+f)−φ(A+f)−φ(A+c)−φ(d+e).
```

We first work with positive variables. All subsequent boundary uses extend by continuity, as explained in §8.

## 2. The d=e face

Put d=e=D. Differentiation in c gives

```
F_c = log[(A+c+f)(c+D) / ((c+D+f)(A+c))] ≤ 0,
```

since the numerator minus denominator is f(D−A). Thus F is minimized at c=A. Write K(A,D,f)=F(A,A,D,D,f). Its f-derivative is

```
K_f = log[(2A+f)(D+f) / ((A+D+f)(A+f))].
```

The difference between numerator and denominator is A(D−A)≤0, independent of f. Thus K is non-increasing in f on [0,D] and K(A,D,f)≥K(A,D,D)=0. An optional direct verification of f=0 (not needed by the formal certificate) is:

```
K(A,D,0)=φ(2A)+φ(A+2D)+φ(D)−φ(2A+D)−φ(A)−φ(2D).
```

This is zero at A=D, and its A-derivative is

```
log[4A(A+2D)/(2A+D)²] ≥ 0,
```

because the difference is D(4A−D)≥0. This proves F≥0 on d=e, including D=0 by continuity.

## 3. The f=0 face

Cancellation gives

```
F(A,c,d,e,0)=φ(A+d+e)+φ(2A)+φ(c+d)+φ(e)
            −φ(2A+d)−φ(c+e)−φ(A)−φ(d+e).
```

Its c-derivative is log[(c+d)/(c+e)]≥0. Hence it suffices to take c=d=D. Call the resulting function J(A,D,e). For 0<e≤D,

```
J_e = log[e(A+D+e)/(D+e)²],
```

whose sign is the sign of e(A−D)−D². If D≤A≤2D, this is nonpositive throughout [0,D], so J is minimized at e=D, already handled in §2. If A>2D, the minimum is attained at

```
e*=D²/(A−D) ∈ (0,D).
```

Let M(A)=J(A,D,e*(A)). Since J_e=0 there, the chain rule yields

```
M'(A)=log[4A(A+D+e*)/(2A+D)²]
     =log[4A³/((A−D)(2A+D)²)] > 0.
```

Indeed `(A−D)(2A+D)²=4A³−3AD²−D³<4A³`. Thus M(A)≥M(2D)=J(2D,D,D)≥0 by §2. Continuity deals with e=0, D=0, and the junction A=2D. This proves the whole f=0 face.

## 4. The pair-equal face: a two-variable calculus certificate

Put c=d=C and e=f=E. Then

```
G(A,C,E)=2φ(A+C+E)+φ(2A)+φ(2C)+φ(2E)
       −φ(2A+C)−φ(C+2E)−φ(A+E)−φ(A+C)−φ(C+E).
```

We must show G≥0 for A≥C≥E≥0.

### 4.1 The E=0 edge

Using φ(2t)=2φ(t)+2t log2, cancellation gives

```
G(A,C,0)=φ(A+C)+φ(A)−φ(2A+C)+2(A+C)log2.
```

Convexity of φ, applied to A and A+C, gives

`φ(A)+φ(A+C) ≥ φ(2A+C)−(2A+C)log2`.

Therefore G(A,C,0)≥C log2≥0.

### 4.2 Normalize E=1, and prove its two boundary edges

For E>0 use degree-one homogeneity to put E=1. Let g(A,C)=G(A,C,1) on A≥C≥1.

On C=1,

```
g_A = log[4A²(A+2)²/((2A+1)²(A+1)²)],
```

and the numerator minus denominator factors as `(A−1)(4A²+7A+1)`. Thus this edge is nonnegative, starting at g(1,1)=0.

On A=C=t, the derivative of g(t,t) is

```
log[(2t+1)^4(2t)² / ((3t)^3(t+2)(t+1)²)].
```

The numerator minus denominator is

`t²(t−1)(37t³+57t²+18t−4) ≥ 0` for t≥1.

This edge also starts at zero and is nonnegative.

### 4.3 A weighted derivative is nonnegative

Put S=A+C+1 and define the positive quantities

```
P_A=4A²S²,       Q_A=(2A+C)²(A+1)(A+C),
P_C=4C²S²,       Q_C=(2A+C)(C+2)(A+C)(C+1).
```

Then g_A=log(P_A/Q_A) and g_C=log(P_C/Q_C). The elementary inequality `log x≥1−1/x` for x>0 gives

```
2A g_A+C g_C ≥ 2A(1−Q_A/P_A)+C(1−Q_C/P_C)
             = (2A+C) R / (4AC S²),
```

where the exact polynomial identity has the following nonnegative decomposition:

```
R = (A−C)²(C−1)(C+2)
  + (A−C)C(C+1)(3C−2)
  + 2C³(C−1).
```

Every factor here is nonnegative for A≥C≥1. The rational identity is verified by multiplying by the positive denominators and expanding; `gradient_identity` proves it in Lean and `R_nonneg` proves the displayed decomposition is nonnegative. We conclude that

`2A g_A+C g_C≥0` throughout the positive ordered domain.

### 4.4 Follow a curve to a proved boundary edge

Fix any point (A₀,C₀) with A₀≥C₀≥1 and put k=A₀/C₀²>0. Let

`c₀=max(1,1/k)`.

Then c₀≤C₀: indeed C₀≥1 and A₀≥C₀ gives 1/k=C₀²/A₀≤C₀. For t∈[c₀,C₀], the point `(kt²,t)` satisfies kt²≥t≥1. By the chain rule and §4.3,

```
d/dt g(kt²,t) = 2kt g_A(kt²,t)+g_C(kt²,t)
              = [2(kt²)g_A(kt²,t)+t g_C(kt²,t)]/t ≥0.
```

Thus `g(A₀,C₀)≥g(kc₀²,c₀)`. If k≥1 then c₀=1, so the latter point lies on C=1. If k≤1 then c₀=1/k and kc₀²=c₀, so it lies on A=C. Both boundary edges were proved nonnegative in §4.2. Hence g≥0 everywhere. With §4.1 and homogeneity, this proves G≥0 for A≥C≥E≥0.

## 5. The c=d face

Put c=d=C. Vary e and f with e+f fixed. The second derivative in the direction (e,f)→(e+t,f−t) is

```
[1/(A+C+e)−1/(C+e)] + [1/(A+C+f)−1/(A+f)] ≤ 0.
```

Consequently F is concave on the interval determined by C≥e≥f≥0. Its minimum is at an endpoint, where either e=f, e=C, or f=0. These cases are §4, §2, and §3, respectively. Thus this face is proved.

## 6. The c=A face, and then the e=f face

On c=A, differentiation in d gives

```
F_d=log[(A+d+e)(A+d)/((2A+d)(d+e))].
```

The numerator minus denominator is A(A−e)≥0. Hence the function is non-decreasing in d on e≤d≤A, and its minimum is at d=e, proved in §2. This proves c=A.

On e=f=E, vary c and d at fixed c+d. The directional second derivative is

```
1/(A+c+E)+1/(A+d+E)
−1/(2A+d)−1/(c+2E)−1/(A+c)−1/(d+E) ≤ 0.
```

Indeed `1/(A+c+E)≤1/(A+c)` and `1/(A+d+E)≤1/(d+E)`, with two additional nonpositive summands. Thus F is concave along this segment, and its minimum is at c=d, c=A, or d=E. These have just been proved in §§4–6 and §2. This proves e=f.

## 7. Finish by a concave fiber

For general A≥c≥d≥e≥f≥0, vary

`(c,d,e,f)→(c+t,d−t,e+t,f−t)`.

Every positive marginal in F stays fixed, while all negative marginals are affine in t. Since φ is convex, F is concave on its feasible interval

`max((d−c)/2,(f−e)/2) ≤ t ≤ min(A−c,(d−e)/2,f)`.

At the left endpoint either c=d or e=f. At the right endpoint either c=A, d=e, or f=0. All these faces were proved in §§2–6. The value at t=0 is at least the smaller endpoint value and hence is nonnegative. Section 1 now proves all three source inequalities.

## 8. Degenerate cases and analytic justification

The proof uses φ on [0,∞), continuous with φ(0)=0 and convex, with φ'=1+log t and φ''=1/t on (0,∞). Every differentiation or use of second derivatives above takes place in the positive interior of the relevant face (except a face's identically zero φ terms, which have already been canceled). Extend concavity and monotonicity to closed segments by continuity. For instance adding a common ε>0 to A,c,d,e,f preserves all order and tie relations and then letting ε↓0 proves the original endpoint. In §3, the identically zero final coordinate has already been removed from the formula; use positive A,D,e there and let positive variables tend to zero. The ordinary proof in §4 gives an explicit E=0 bound. The Lean certificate instead uses the common-epsilon closure theorem for G; neither route scales by zero. These arguments include the all-zero unnormalized tuple, for which every F_i=0. Homogeneity then includes every normalized source distribution.

## Validation

The following script paths refer to the supplied discovery lane, not this formalization folder. The lane-local numerical direction check is sanity.py; formal checks and their exact receipts are listed in REPORT.md.

- `scripts/entropy_gradient_certificate.py`: exact verification of the weighted-gradient rational identity and its nonnegative polynomial decomposition.
- `scripts/entropy_certificates.py`: the two one-variable boundary factorizations and an alternative stationary-point certificate from an earlier complete proof route, retained as supplementary evidence.
- `scripts/entropy_face_graph.py`: ancillary source-based boundary routes found earlier; the final proof above does not need them.
- `scripts/validate_entropy.py` uses **no Sympy**: an independent standard-library sparse polynomial implementation checks the weighted-gradient identity and the earlier Bezout identity. It also checks the derivative quotients and directional Hessians against the original marginal lists on 1,000 positive ordered tuples with 60-digit decimal logarithms/exact rational Hessians. The three original gaps were checked on 3,000 tuples including zeros/ties, and the pair face on every integer 1≤A≤30, 1≤C≤A, 0≤E≤C. All passed; see `entropy-validation.log`.
- The full formal endpoint is `McConnell.mcconnell_conj19` in `EntropicEndpoint.lean`. The source appendix contains every local dependency; REPORT.md lists compilation and kernel-check receipts. Numerical checking is supplementary only.

## Prior art and self-assessment

The dated checks and access limits are inherited from the supplied proof lane and the independent review, as summarized in the bounded prior-art paragraph above. Only v1 is listed by arXiv. The Semantic Scholar citing list returned one companion paper, whose publisher body was read and does not resolve the three relations; no journal publication of the exact source title was located. Live omega issue/PR and openai/math index/code screens gave no relevant hit. OpenAlex returned 429 and ProbXiv returned 402; these limits remain explicit. The source's own proof methods use identric means and comparison of majorization; §1's largest-entry reduction is short, but the full proof needs concave marginal fibers, a second series of face reductions, and a weighted-gradient inequality and its order-preserving quadratic curves. No application of a source theorem is needed for the final proof. The shortest route found from the source's published results alone stops at the five-variable boundary inequality. The complete route above is longer than a routine replay of the source's sporadic proofs.

A specialist's significance judgment remains for independent review. The algebraic certificate itself is mechanical once the analytic reduction is found; the claimed substantive step is the concave-fiber reduction followed by the nonnegative weighted derivative that transports the surviving pair-equal face to its two edges.


## Exact Lean endpoint and certification

```lean
theorem mcconnell_conj19 (p : Fin 6 → ℝ) (hp : InD6 p) :
    cmi (M37 p) ≤ cmi (M11 p) ∧ cmi (M43 p) ≤ cmi (M11 p) ∧ cmi (M49 p) ≤ cmi (M11 p)
```

The theorem is in namespace `McConnell`. Its only hypothesis is the source's closed fundamental domain. `InD6_uniform` proves this domain is inhabited. `cmi_gap37`, `cmi_gap43` and `cmi_gap49` prove in Lean that the joint-entropy terms cancel, without changing the definition of cmi. The common-epsilon closure includes all ties and zero entries.

For §5 the formal certificate uses the identity into a constant plus increments with base arguments A+f−t and C+e+t and shifts C and A, respectively. For §6 it uses increments with base arguments A+c+t and d−t+E and shifts E and A, plus the two affine negative-phi terms. The reusable increment lemma is concave on the closed nonnegative half-line, so these face proofs are valid at zero without taking derivatives there.

The largest-entry reduction uses a common product difference
`(a+b)(u-d-f)+d(b-f)`, with u=c+f, d+e, d+f for 37, 43, 49. The row-spread comparison is certified by the nonnegative derivative of t↦φ(A+c+t)−φ(A+d+t), an equivalent calculus form of convexity. This discharges all three scalar gaps before applying the source-faithful cmi bridge.

At the review's ordered, normalized point (.4677,.3204,.0767,.0682,.0588,.0082), 80-digit Decimal evaluation of the full cmi gives I(11)−I(37)=0.0575395842291577056431…, I(11)−I(43)=0.0700407966428131458063…, and I(11)−I(49)=0.0558904909681483476869…. These strict values are a documented numeric direction check, not a formal inequality certificate; the weak inequalities are proved uniformly by the theorem.
