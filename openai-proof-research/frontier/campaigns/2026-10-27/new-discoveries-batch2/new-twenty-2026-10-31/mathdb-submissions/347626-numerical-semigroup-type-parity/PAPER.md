# Type parity of numerical semigroups at fixed Frobenius number

## Abstract

Among all numerical semigroups with Frobenius number \(F\), the proportion whose type is congruent to \(F\) modulo two tends to \(1/2\). This proves Conjecture 7.2 of Deepesh Singhal. We toggle the membership of \(\lfloor 3F/4\rfloor\) in the range of multiplicities that carries asymptotically all the mass. Disjoint pairs of membership tests bound the fraction for which this toggle can fail to reverse type parity. We give a proof of the one-sided concentration estimate needed for the argument, following Backelin's counting method, and formalize the proof in Lean 4.

## Statement and definitions

Conjecture 7.2 in Singhal's notation is
$$
\lim_{F\to\infty}\frac{\#\{S\mid F(S)=F,\ t(S)\equiv F\pmod{2}\}}{\#\{S\mid F(S)=F\}}=\frac12.
$$
[Singhal, §7](https://arxiv.org/pdf/2008.08110#page=16)

In Singhal's §1, a numerical semigroup is a subset of the naturals that “contains \(0\), is closed under addition and has a finite complement.” “The largest gap” is the Frobenius number \(F(S)\). A pseudo-Frobenius number \(x\) is a gap whose sum \(x+s\) belongs to \(S\) “for any nonzero \(s\) in \(S\).” The set of these gaps is \(PF(S)\), and their number is “its type,” \(t(S)\). Here are the corresponding Lean definitions. [Singhal, §1](https://arxiv.org/pdf/2008.08110#page=1)

```lean
def IsNumSg (S : Set ℕ) : Prop :=
  0 ∈ S ∧ (∀ a ∈ S, ∀ b ∈ S, a + b ∈ S) ∧ Sᶜ.Finite

def HasFrob (S : Set ℕ) (f : ℕ) : Prop :=
  f ∉ S ∧ ∀ n, f < n → n ∈ S

def PF (S : Set ℕ) : Set ℕ :=
  {g | g ∉ S ∧ ∀ s ∈ S, 0 < s → g + s ∈ S}

noncomputable def sgType (S : Set ℕ) : ℕ := (PF S).ncard

def All (f : ℕ) : Set (Set ℕ) := {S | IsNumSg S ∧ HasFrob S f}

def Same (f : ℕ) : Set (Set ℕ) := {S ∈ All f | sgType S % 2 = f % 2}
```

In what follows \(f\ge 1\) is an integer, \(\mathcal S_f\) is the set counted by the denominator, \(N(f)=|\mathcal S_f|\), and \(m(S)\) is the least positive element of \(S\). An encoding of \(S\in \mathcal S_f\) is \(A=S\cap [1,f-1]\). It determines \(S=\{0\}\cup A\cup (f,\infty )\). A subset \(A\subseteq [1,f-1]\) is an encoding exactly when sums of two elements of \(A\) avoid \(f\) and belong to \(A\) if they are less than \(f\). To see sufficiency, sums involving 0 preserve membership, and those with a summand above \(f\) are above \(f\). The complement is finite. Necessity follows from closure and the gap \(f\). The pseudo-Frobenius test in this encoding takes \(g\in [1,f]\setminus A\) and asks whether \(g+s\in A\) or \(g+s>f\) for every \(s\in A\). Positive elements above \(f\) give automatic tests. This proves the bridge to the original type. For every \(f\ge 1\), the empty encoding is valid. The case \(f=0\) has no such numerical semigroups and plays no role in the limit.

## 1. Concentration on the side below \(f/2\)

Put \(a=\lfloor (f-1)/2\rfloor\). Every subset of \(U=[f-a,f-1]\) gives a valid encoding since any sum of two of its elements exceeds \(f\). Consequently
$$
N(f)\ge 2^a.
$$
Let \(N(f,m)=|\{S\in\mathcal S_f:m(S)=m\}|\). We will bound this count in the two ranges of multiplicity considered by Backelin. The sum of the bounds is enough to prove
$$
\frac{|\{S\in\mathcal S_f:m(S)\le \lfloor f/2\rfloor-\lfloor f/40\rfloor\}|}{N(f)}
\longrightarrow 0.
$$
[Backelin, §I.2, pp. 201–204](https://journals.msp.org/mscand/article/download/1319/1318)

### 1.1. The range \(f/4<m<f/2\)

Fix an encoding of multiplicity \(m\). Its part \(X\) in \([1,\lfloor f/2\rfloor]\) lies in \([m,a]\) and contains \(m\). Indeed, when \(f\) is even, \(f/2\) is excluded because doubling it gives \(f\). Write \(X=\{m\}\cup Z\) with \(Z\subseteq [m+1,a]\). For a fixed \(X\), use the following three sets of positions in \(U\), with \(b=\max X\).
$$
D=m+X,\qquad C=b+Z,\qquad B=f-X.
$$
The first two sets are present by closure and the last is absent since \(f\) is a gap. Membership of these positions in \(U\) follows from \(2m>f/2\) and \(2a<f\) for the sums, and from \(1\le x\le a\) for each reflected point \(f-x\). The sets \(D\) and \(C\) are disjoint since elements of \(D\) are at most \(m+b\) while elements of \(C\) exceed \(m+b\). If a valid encoding exists for \(X\), both are disjoint from \(B\). If the fiber for \(X\) is empty, every upper bound below holds for it.

For each \(t\in T=[f-a,f-m-1]\), the implication \(t\in A\Rightarrow t+m\in A\) restricts the two memberships to three patterns. The tails and heads belong to \(U\). These \(|T|=a-m\) pairs are disjoint, since their first head is at least \(f-a+m\) and their last tail is at most \(f-m-1\), with \(2m>a\). The head positions lie strictly above \(m+a\), so \(D\) contains no heads. All other coordinates of \(U\) are singleton blocks.

Before prescribing bits, the block counts multiply to \(2^a(3/4)^{a-m}\). Prescribing presence on each point of \(D\) multiplies this bound by \(1/2\) per point. Prescribing the bits at \(B\cup C\) multiplies it by \(2/3\) per point. These factors hold simultaneously within each block. A prescribed singleton gives one choice out of two. A pair with one ordinary prescription has at most two of its three choices, and one whose tail is prescribed present has at most one. If both bits in a pair are prescribed, at most one choice remains, and multiplying the baseline three by the two indicated factors gives at least one. At most one point of \(D\) lies in any pair.

Set \(z=|Z|\). Then \(|D|=z+1\) and \(|B\cup C|=2z+1\), so the number of upper patterns for \(Z\) is at most
$$
2^a(3/4)^{a-m}(1/2)^{z+1}(2/3)^{2z+1}
\le 2^a(3/4)^{a-m}(2/9)^z.
$$
Summing over \(Z\subseteq [m+1,a]\) multiplies \(2^a(3/4)^{a-m}\) by \((1+2/9)^{a-m}\). We obtain
$$
N(f,m)\le 2^a(11/12)^{a-m}.
$$

### 1.2. The range \(0<m\le f/4\)

Write \(f=nm+r\) with \(0\le r<m\) and \(n\ge 4\). If \(r=0\), the closure of \(S\) under addition would put \(f\) in \(S\), so \(N(f,m)=0\). Suppose \(r>0\). In each residue class \(i\) modulo \(m\) with \(0<i<m\), membership of \(km+i\) is a tail in \(k\) because \(m\in S\). Let \(\theta_i\) be the smallest \(k\ge 0\) with \(km+i\in S\). Such \(k\) exists since all integers greater than \(f\) are in \(S\). All multiples of \(m\) are present, and the residue class \(r\) is absent through \(f\). Indeed, any member \(km+r\) with \(k\le n\) would give \(f\) upon adding \((n-k)m\).

For \(1\le i<r\) we have \(\theta_i\le n+1\). Record the value \(v_i=n+1-\theta_i\). The reflected partner of \(i\) is \(r-i\). If \(\theta_i+\theta_{r-i}\le n\), the elements at indices \(\theta_i\) and \(\theta_{r-i}\), together with the needed nonnegative multiple of \(m\), would sum to \(f\). Thus \(v_i+v_{r-i}\le n+1\).

For \(r<i<m\) we have \(\theta_i\le n\). Record \(v_i=n-\theta_i\), with reflected partner \(m+r-i\). The partners have residues adding to \(m+r\), so their indices cannot sum to \(n-1\) or less. Thus \(v_i+v_{m+r-i}\le n\). These inequalities apply to midpoint classes as well, where one residue is its own partner. All the recorded values together determine \(S\) by recovering each threshold and using the two fixed residue classes.

Write \(B_j=(j+1)(j+2)/2\), the number of ordered pairs \((u,v)\) of nonnegative integers with \(u+v\le j\). This count follows by summing \(j+1-u\) for \(0\le u\le j\). In the lower classes there are \(\lfloor r/2\rfloor\) orbit representatives, including the midpoint if present, and each has at most \(B_{n+1}\) possibilities. In the upper classes there are \(\lfloor (m-r)/2\rfloor\) representatives and at most \(B_n\) possibilities for each. Counting a midpoint by the pair bound only increases the estimate.

Take \(\rho=63/32\). We have \(B_4=15\le \rho^4\), and for \(j\ge 4\) the ratio \((j+3)/(j+1)\) is at most \(7/5<\rho\). Thus \(B_j\le \rho^j\) for \(j\ge 4\). Squaring the product bound and using \(2\lfloor d/2\rfloor\le d\) gives
$$
N(f,m)^2\le \rho^{(n+1)r+n(m-r)}=\rho^f.
$$
Since \(f\le 2a+2\) and \(\rho<2\), it follows that \(N(f,m)\le 2\rho^a\).

### 1.3. The tail bound

Let \(L=\lfloor f/40\rfloor\), \(\mu =\lfloor f/2\rfloor-L\), and \(q_f=\lfloor f/80\rfloor\). For \(f\ge 80\) and \(m\le \mu\), we have \(2m<f\) and \(a-m\ge q_f\), since \(a\ge \lfloor f/2\rfloor-1\) and \(\lfloor f/40\rfloor\ge 2q_f\). Also \(a\ge q_f\). Divide the medium and small bounds by \(2^a\) and sum over at most \(f\) possible multiplicities. Using \(N(f)\ge 2^a\) gives
$$
\frac{|\{S\in\mathcal S_f:m(S)\le\mu\}|}{N(f)}
\le f\bigl(2(\rho/2)^{q_f}+(11/12)^{q_f}\bigr).
$$
For each \(0<q<1\), \(f q^{q_f}\to0\) since \(f<80(q_f+1)\) and \((q_f+1)q^{q_f}\to0\). This proves the concentration estimate.

## 2. The toggle and the parity count

Keep \(f\ge 80\) and the choices of \(L,\mu ,q_f\). Define
$$
M=[\lfloor f/2\rfloor+L+1,f-2L],\qquad
x=\lfloor3f/4\rfloor,\qquad h=\max(f-x,x-\mu-1).
$$
Here \(x\in M\), \(M\subseteq [1,f-1]\), and its size is \(k=f-\lfloor f/2\rfloor-3L\). Subtracting floors gives
$$
\lfloor3f/4\rfloor-\lfloor f/2\rfloor\le(f+1)/4,
$$
as is seen by writing \(f=4q+r\), \(0\le r\le 3\), and checking the four remainders. Consequently \(x-\mu -1\le f/4+L-3/4\). Since \(f-x=\lceil f/4\rceil\), we have \(h\le f/4+L+1\). In particular \(h\le f\) and \(h\le f-2L\).

### 2.1. Free membership and the high pseudo-Frobenius gaps

Let \(\mathcal G=\{S\in \mathcal S_f:m(S)>\mu \}\). For any \(y\in M\) and any positive member \(s\) of \(S\in \mathcal G\), we have
$$
y+s\ge 2\lfloor f/2\rfloor+2>f.
$$
A sum of two positive members is at least \(2\mu +2>f-2L\), so it never belongs to \(M\). Therefore, for any fixed outside part \(S\setminus M\) occurring in \(\mathcal G\), any choice of subset of \(M\) gives a member of \(\mathcal G\). In detail, the zero element and all elements above \(f\) remain present, \(f\) remains absent, and all positive members exceed \(\mu\). Sums involving a new member of \(M\) exceed \(f\), and sums of two positive members outside \(M\) were already in \(S\) and cannot land in \(M\). Thus each such fiber has exactly \(2^k\) members.

Pair \(S\) with \(S'=S\cup \{x\}\) when \(x\notin S\). The gap \(x\) belongs to \(PF(S)\) since \(x+s>f\) for every positive \(s\in S\), and it is present in \(S'\). For any other gap \(g>h\) there are two implications. If \(g\in PF(S)\), the new test at \(s=x\) passes because \(g+x>f\). If \(g\in PF(S')\) then the tests at all old positive summands pass in \(S\) too, since a sum \(g+s=x\) would require \(s\le \mu\). Hence the pseudo-Frobenius sets in the two members differ exactly by the singleton \(\{x\}\) provided neither contains a gap in \([1,h]\).

### 2.2. Counting the exceptional patterns

Fix a gap candidate \(1\le g\le h\). If \(g\) is pseudo-Frobenius in either member of a toggle pair, its shared membership bits on \(M\setminus\{x\}\) satisfy the implications
$$
s\in S\quad\Longrightarrow\quad s+g\in S
\qquad(s,s+g\in M\setminus\{x\}).
$$
Indeed, these points have the same membership in both members, and \(s\) is positive. The implications depend only on their shared bits. Mark a pattern in \(M\) as exceptional if it satisfies these implications for at least one \(g\).

There are \(k-g\) possible tails \(s\) with \(s,s+g\in M\) before exclusions. To verify this number is positive here, use \(k\ge f/2-3L\) and \(g\le f/4+L+1\), so that
$$
k-g-2\ge f/4-4L-3\ge 3f/20-3\ge3q_f
\qquad(f\ge80).
$$
Deleting tails \(x\) and \(x-g\) takes out at most two pairs. Choose greedily a pair among those remaining and remove every remaining pair that meets it. For a chosen tail \(s\), a conflicting tail can only be \(s-g\), \(s\), or \(s+g\). Thus at least \(q_f\) disjoint pairs can be chosen. Each pair forbids the pattern present/absent and leaves three of four patterns. Counting the other coordinates freely gives at most \(2^k(3/4)^{q_f}\) patterns for this \(g\), including the independent choice at \(x\). The union bound over \(g\le h\le f\) bounds the fraction of exceptional patterns in each fiber by \(f(3/4)^{q_f}\).

### 2.3. Cancellation

Give \(S\) weight \(+1\) if \(t(S)\equiv f\pmod 2\) and \(-1\) otherwise. The unmarked portion of every fiber is stable under toggling at \(x\), because the marking depends only on bits away from \(x\). Each of its pairs contributes zero weight since its types differ by one. Writing \(D(f)\) for the sum of weights over \(\mathcal S_f\), we obtain
$$
\frac{|D(f)|}{N(f)}
\le
\frac{|\{S\in\mathcal S_f:m(S)\le\mu\}|}{N(f)}
+f(3/4)^{q_f}.
$$
The first term vanishes by the concentration estimate and the second by geometric decay. If \(N_{=}(f)\) is the numerator in the conjecture, then \(D(f)=2N_{=}(f)-N(f)\), so \(N_{=}(f)/N(f)\to1/2\).

## Scope and prior work

The new step is the choice of one free coordinate near \(3f/4\) and the analysis of the two ways changing that bit affects a pseudo-Frobenius test. Its two distances, from \(f\) and from the lower bound on positive members, balance the range of affected gaps. The parity conclusion uses standard finite counting and a sign-reversing involution, and the short argument beyond Backelin fits the scope of a note. Conjecture 7.1 on strict dominance at every \(F\) and the conjectures with genus fixed are separate questions. [Singhal, §7](https://arxiv.org/pdf/2008.08110#page=16)

Backelin's 1990 Proposition 2(2) gives concentration on both sides of \(f/2\) in a window of fixed width for each error tolerance, together with the normalization in his equation (1). Section 1 proves the weaker one-sided concentration estimate used here. Lean also proves this estimate as `Singhal.lowMult_tendsto_zero` from the finite counts in the accompanying modules. The formal argument does not assume Backelin's concentration theorem. Its medium and small counts are adaptations of Backelin's bounds. Singhal's fixed-Frobenius genus paper describes the free middle choices in related fibers. Kaplan and Singhal use shifted membership constraints for low pseudo-Frobenius gaps in Lemmas 23–24 of their fixed-genus study, the closest precedent for the local counting device. Li's depth counts, the shape theorem of Bras-Amorós, Kaplan, and Singhal, and the fixed-Frobenius counting formulas of Bras-Amorós and Torra concern depth, shape, multiplicity, or genus. The final search found no earlier fixed-Frobenius type-parity limit in the texts reviewed. The comparison with Conjecture 7.2 uses the sole arXiv version. The published journal text was unavailable for inspection. [Bras-Amorós and Torra](https://arxiv.org/abs/2611.11559) · [Singhal, journal version](https://doi.org/10.1142/S0218196721500417) [Backelin](https://doi.org/10.7146/math.scand.a-12304) · [Singhal on fixed-Frobenius genus](https://arxiv.org/abs/2008.02963) · [Kaplan and Singhal](https://arxiv.org/abs/2211.07811) · [Li](https://arxiv.org/abs/2208.14587) · [Bras-Amorós, Kaplan, and Singhal](https://arxiv.org/abs/2604.26127)

## Formal certificate

`Singhal.singhal_7_2` proves the literal set-cardinality formulation of the limit. `Singhal.singhal_7_2_encoded` proves its finite encoding. The equivalence and positivity of the denominator are proved in `SinghalStatement`, which also checks the total and same-parity counts at \(f=2,\ldots ,6\) with `decide`. The weighted pair count, concentration, greedy matching and toggle are formalized in the accompanying modules. Both endpoints depend only on `propext`, `Classical.choice`, and `Quot.sound`. [Lean source appendix](../semigroup-type-parity-347626-formal-paper-sol62-20261123-r1/LEAN-SOURCE-APPENDIX.md)

The proof and first review were by Claude Opus 5.5. The cross-model review, Lean formalization, and manuscript preparation were by GPT-6.2 Sol. A separate GPT-6.2 Sol lane performed the final check.
