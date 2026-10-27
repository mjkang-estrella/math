# Prospective all-order resolution of Zaprawa's coefficient conjecture

**Status: mathematical proposal only. Credit0, tally25/30 unchanged.**
Prior-art and substantive eligibility unresolved. No Lean endpoint, independent
review, manuscript, packet or acceptance. This is distinct from the excluded
MathDB381835 baseline bound. Do not claim novelty from an open label or the
absence of a search hit.

## Exact source

Paweł Zaprawa, *On a Coefficient Inequality for Carathéodory Functions*,
Results in Mathematics79(2024), article30, published2December2023,
DOI10.1007/s00025-023-02061-8. The actual publisher PDF pp1–3 and full HTML
were read; p3 rendered and visually inspected. Class P consists of analytic
h(z)=1+Σ_{k>=1}p_k z^k on the unit disk with Re h>0. Eq9 conjectures

    |p_(n-1) p_(n+1) - p_n^2| <= 4 - |p_1|^2, every integer n>=2.

The source proves n2 and n3 only (Theorems2 and3), explicitly says the general
case is unproved, and gives two equality families. Those known cases earn no
credit. Source PDF sources/zaprawa2023.pdf; full HTML caratheodory2023.html.

## Complete mathematical argument for all n

Use the classical Herglotz representation, with probability μ on the unit
circle T, in the convention h(z)=∫(1+ζz)/(1-ζz)dμ(ζ). Then p_k=2m_k,
m_k=∫ζ^k dμ, k>=1, and m_0=1. This precise normalization is also printed in
Efraimidis arXiv1506.07111v2 p2. All integrands below are continuous/bounded
on the compact T×T, so Fubini and products of integrals apply without a domain
or convergence qualification.

For n>=1, symmetrization yields

    m_(n-1)m_(n+1)-m_n^2
      = (1/2)∫∫(ζω)^(n-1)(ζ-ω)^2 dμ(ζ)dμ(ω).

Triangle and |ζω|=1 give

    |m_(n-1)m_(n+1)-m_n^2|
      <= (1/2)∫∫|ζ-ω|^2
       = 1-|m_1|^2.

Multiplying by4 proves exactly Eq9 for all n>=2. The final identity follows
from |ζ-ω|²=2-ζ conjugate(ω)-conjugate(ζ)ω and ∫1=1. This is not a finite-check
argument. It also proves the offset form

    |m_(n-r)m_(n+r)-m_n^2| <= 1-|m_r|^2, 1<=r<=n,

by replacing (ζ-ω)^2 with (ζ^r-ω^r)^2. No separate helper credit.

## Additional equality classification (unreviewed)

For each fixed n>=2, equality in Eq9 holds iff either
(a) μ is supported on at most two points, or
(b) μ is supported on a rotated set of nth roots of unity.

Proof: on T×T,

    (ζω)^(n-1)(ζ-ω)^2 = -(ζω)^n |ζ-ω|^2.

If support has one point, both sides of the inequality are0. Otherwise
∫∫|ζ-ω|²>0. Equality in the integral triangle inequality implies a common
phase for -(ζω)^n wherever ζ≠ω in suppμ×suppμ. First this holds almost
everywhere against the weighted product measure. The integrand is continuous;
any distinct support pair has neighborhoods of positive μ-product mass and
positive |ζ-ω|², so the phase condition holds at EVERY distinct support pair.
If there are only two support points, this condition holds automatically.
If a,b,c are three distinct support points, equality of (ab)^n,(ac)^n,(bc)^n
forces a^n=b^n=c^n. For any other support point d, comparison with two of a,b,c
forces d^n=a^n. Thus the support lies in one rotated root set. Conversely,
both alternatives make the off-diagonal phase constant and give equality.

This includes arbitrary two-point measures, beyond the two displayed source
families. It is supplementary mathematical content, not accepted credit.

## Eligibility and subsumption risks — expressly unresolved

The inequality proof is very short after the classical Herglotz representation.
A general classical covariance/Grüss/determinant bound could subsume it.
The campaign excludes immediate known-corollary resolutions, so a literal
open conjecture alone is insufficient. An independent reviewer must decide
whether the moment symmetrization is substantive new source resolution or
falls under that exclusion. Do not rescue it by counting the equality case or
offset helpers separately.

Efraimidis2015 actual Theorems1/2/3 and their Herglotz formula were read.
Their determinants A_(k,n) involve a different coefficient combination; none
of the inspected statements is Eq9. This is a bounded screen, not proof that
all consequences or earlier Livingston/Delsarte/Grüss results are irrelevant.
Zaprawa's eight OpenAlex-indexed citing works have only been identified by
title at this checkpoint, NOT cleared by body reads. No worldwide priority
claim. Required next: exact independent proof/subsumption/eligibility review,
then (only if qualified) literal analytic-object Lean bridge, paper and replay.


## Second derivation and strongest immediate-corollary objection

In L²(μ), set x=(1,ζ) and y=(ζ^n,ζ^(n+1)). With inner product
<f,g>=∫conjugate(f)g, the cross Gram determinant is
m_n²-m_(n-1)m_(n+1). Both self-Gram determinants equal1-|m_1|², since |ζ|=1.
The classical determinant Cauchy–Schwarz inequality therefore gives the same
bound immediately. Equivalently use Cauchy–Schwarz on exterior-square vectors.
This is an explicit plausible exclusion under the campaign's rule against
immediate classical corollaries; it must be presented to an eligibility reviewer,
not hidden by the shorter integral proof. Full equality classification is extra
content of this same prospective outcome, never separate countable credit.

## Current bounded source checks

Four of eight indexed citers have now been obtained as genuine primary PDFs.
Parent read the actual relevant theorem/lemma statements and citation contexts:
Allu–Shaji DOI10.1017/S0004972724000947, Lemma2.5 only uses the known n3 case;
FourLeaf2024 DOI10.3390/math12121875, Lemma2 lists low-order Schwarz bounds,
Theorems1–10 concern finite-order coefficients/Hankel/log coefficients;
qSecant2025 DOI10.3390/fractalfract9060346, Theorems1–4 concern q-starlike/
q-convex third-Hankel expressions; Symmetric2026 DOI10.3390/sym18081307,
Theorem1 is a different H3,1 near-sharp bound, not its conjectured1/16.
These inspected statements do not resolve Eq9. The qSecant multi-line constants
were scoped as different expressions, not independently rederived. This is not
an exhaustive line-by-line proof review of all four papers. Four other indexed
citers remain body-unread. Publisher MDPI PDF routes403; the publisher's own
public mdpi-res CDN PDFs200; failure/success records saved. CambridgePDF200.

Cached trureturing text search at exact revisionf8ffe9ed02e01601ed0b43a400ebc1c09cdc6ada
found no matching named-source/identifier paths. Numeric identifiers were
bounded to avoid random matches in giant certificates; a first unbounded
search was noisy and is not evidence. See zaprawa-registry-screen.json.
