# Exact classical bridge for the q-Hoggatt candidate

Independent preliminary review, 2026-10-28 UTC. This is a derivation from old
theorems, not a claim that an earlier author printed the Hoggatt conclusion.
Use Q>1 for the candidate parameter and p=1/Q for Lamprecht's parameter.

## 1. Conventions verified in the actual source

Lamprecht, arXiv:1210.1102v1, Sections 2.1, 3, 5, 6, 7, defines

\[
 R_d(p;t)=\prod_{j=0}^{d-1}(1+p^j t)
         =\sum_{k=0}^d C_k^d(p)t^k,
 \qquad C_k^d(p)=p^{\binom{k}{2}}{d\brack k}_p.
\]

His weighted convolution has kth coefficient f_k h_k/C_k^d(p).
It is NOT the ordinary coefficientwise product used in the candidate.
His order f preceq g means f'g-fg'<=0 on the real line; prec_0 additionally
forbids common zeros except at 0. These definitions allow negative leading
coefficients. His Nbar_d(p) consists of polynomials of degree at most d with
nonpositive, weakly p-separated roots, allowing zero roots. An extremal
polynomial is a nonzero scalar multiple of R_d(p;a t), a!=0. Its constant
coefficient is nonzero.

For negative increasing roots r_i, the candidate condition
r_i/Q<r_(i+1) is exactly strict p-separation: r_(i+1)/r_i<p.
There is no reversal or loss of strictness in this conversion.

## 2. Theorem 25 subsumes q-Rolle

Lamprecht's operator is

\[
 \Delta_{p,d}f(t)=\frac{f(t)-f(p^{-1}t)}{(p^{d-1}-p^{-1})t}
       =\frac{D_Q f(t)}{[d]_p}.
\]

Here [d]_p=(1-p^d)/(1-p)>0. Theorem 25 preserves strict/weak p-separation
and the relevant negative-root order. The detailed endpoint brackets in the
candidate can also be proved directly; they are consistent with this theorem.
Equation (29) of Lamprecht gives

\[
 D_Q R_d(p;t)=[d]_p R_{d-1}(p;t).
\]

## 3. Exact Theorem 30 specialization subsumes q-Markov, including strictness

This is stronger evidence than merely noticing that both papers discuss
q-differentiation. For d>=2 put

\[
 K_d(t):=tD_Q R_d(p;t)=[d]_p tR_{d-1}(p;t).
\]

Its roots are 0,-1,-Q,...,-Q^(d-2). Consequently K_d is in Nbar_d(p).
It is nonextremal: K_d(0)=0 whereas every extremal polynomial above has
nonzero constant coefficient. Its kth coefficient is [k]_Q C_k^d(p), with
[0]_Q=0. Therefore, for EVERY polynomial h of degree at most d,

\[
 h *_p^d K_d=tD_Qh.                                      \tag{A}
\]

Let f have degree d, positive leading coefficient, and strictly Q-separated
negative roots. Let g have degree d-1, positive leading coefficient, and
weakly interlace f. Then g preceq f and f preceq -g in Lamprecht's Wronskian
order: both inequalities are g'f-gf'<=0. Take his Theorem 30 with

\[
 F=f,\qquad G=-g,\qquad H=K_d,\qquad n=d,\qquad q=p.
\]

Every hypothesis holds:

* F is in R_d(p), hence in its closure; G is real-rooted of degree <=d.
* F preceq G, as just checked.
* F and G are not proportional, because their degrees differ.
* H is in Nbar_d(p) and is not extremal.
* The strict clause applies because F is in R_d(p), even when g weakly
  interlaces f and H itself is only weakly separated.

The conclusion, using (A), is

\[
 tD_Qf\prec_0 -tD_Qg.
\]

Both polynomials have exactly one zero at 0: D_Qf(0)=f_1>0 and
D_Qg(0)=g_1>0 (g is a positive multiple of factors t-s with s<0; d>=2).
Cancelling t removes the only permitted common root. The Wronskian identity

\[
 W(tu,-tv)=t^2W(u,-v)=t^2W(v,u)
\]

shows that the resulting orientation is D_Qg preceq D_Qf. Their degrees
are d-2 and d-1 and they have no common roots, so this is exactly strict
interlacing. The d=2 result is the positive constant/linear case.

Thus the candidate's entire q-Markov lemma, with its advertised weak input
and strict output, is an immediate specialization of the actual Theorem 30.
It does not require a new q-interlacing theorem or an unproved symbol claim.

## 4. The separation invariant is also an immediate old-theorem application

Garloff-Wagner Theorem 4(b,c), independently checked against its indexed
original p.800 and FZZ Theorem 2.1, applies to

\[
 (g,f)=(P(t),P(Qt)),\qquad (q,p)=(R(t),R(t)).
\]

If P is weakly Q-separated with negative roots, then P(t) alternates left
of P(Qt). If R has only negative roots, R preceq R. For nonconstant P,R
with positive coefficients, neither exception in 4(c) can hold: P(Qt) is
not proportional to P(t) because Q>1 and P_0,P_degP>0, and a t-multiple
would have zero constant. Thus P*R and (P*R)(Qt) alternate strictly. This
is strict Q-separation of P*R. Ordinary product degree is min(deg P,deg R).

The invariant is real and necessary, but the general invariant-preservation
statement itself is classical. A similar dilation-interlacing argument is
printed for weighted convolution in Martínez-Finkelshtein-Morales-Perales,
arXiv:2606.15003v1, Corollary 3.7. That result is corroborating context,
not substituted for the ordinary-product theorem.

## 5. Full sharp bridge to the candidate family

FZZ's actual proof of Theorem 1.2 already introduces precisely the unweighted
q=1 analogues of F[N,m] and G[N,m]=F[N,1]*F[N-1,m-1], inducts in m, applies
Garloff-Wagner to consecutive G's, differentiates, and identifies the result
with F[N-1,m]. With the candidate's coefficients, the only changed identity is

\[
 D_QG[N,m](t)=[N]_Q Q^m F[N-1,m](Q^m t).                 \tag{B}
\]

It follows termwise from
[k+1]_Q {N choose k+1}_Q=[N]_Q {N-1 choose k}_Q and
binom(k+2,2)=binom(k+1,2)+k+1. All terms k=0,...,N-m match;
both polynomials have degree N-m. At N=m both sides are nonzero constants.

The base F[N,1]=prod_(j=1)^N(1+Q^j t) is weakly separated and consecutive
members weakly interlace. At every m>=2 the old separation argument in
Section 4 makes every G[N,m], N>=m, strictly separated. The same old
Garloff-Wagner theorem makes G[N,m] strictly interlace G[N+1,m]. Applying
Section 3 to this pair and (B) gives strict interlacing of F[N-1,m],F[N,m].
Section 2 gives strict separation and negative simple roots individually.
Positive common argument scaling Q^m preserves the inequalities.
F[m-1,m] is a positive constant; the N=m derivative pair supplies its
comparison with the first linear polynomial. This covers the whole family,
not merely real-rootedness, finite cases, or a weakened non-strict endpoint.

MacMahon's standard product yields the literal plane-partition normalization
in review.md. Combining Q>1 with FZZ's already proved Q=1 case gives its
integer-Q Conjecture 4.1 for m=2,3, and the candidate gives all m>=2.

## 6. What this does and does not establish about novelty

Neither Lamprecht nor Leake-Ryder names this Hoggatt conjecture. Applying
their weighted convolution directly to the candidate's ordinary product,
without a symbol computation, would be invalid. The proof above avoids that
mistake and supplies the exact missing specialization.

I found no earlier explicit publication of the full Q>1 Hoggatt endpoint.
Nevertheless, after Sections 2-4, the remaining argument is the already
published FZZ induction with (B), a termwise Gaussian identity. There is no
remaining new general separation theorem, residue principle, strictness
principle, or new induction structure. Under this campaign's unusually strict
exclusion of routine adaptations/corollaries, my recommendation is NOT to
credit this as a substantive discovery and NOT to undertake the large formal
dependency development for counting purposes. This is an explicit judgment
about the campaign threshold, not a claim of documented prior publication
of the endpoint or a defect in its mathematics. A conventional short note
resolving the conjecture may still be useful; publishing is outside this task.

Primary sources: [Lamprecht v1](https://arxiv.org/html/1210.1102v1),
[FZZ v1](https://arxiv.org/html/2505.05873v1),
[Garloff-Wagner DOI](https://doi.org/10.1006/jmaa.1996.0348),
[2026 convolution paper](https://arxiv.org/html/2606.15003v1).
