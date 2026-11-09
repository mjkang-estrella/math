# Dorward 345816 focused follow-up — 5 November 2026 (Pacific)

**PARK. No all-parameter proof or counterexample. Credit 0. No Lean implementation recommended.** A precise central cancellation condition is derived below, but no uniform bound for its actual multiplicities or recoverable replacement injection was obtained. No public resolution was established either: the bounded source audit has an explicit inaccessible-body hold.

All writes are confined to this directory. No children, git operations, shared edits, browser tabs, external messages, uploads or posting. No coefficient-range sweep was run. The only arithmetic diagnostic is one literal m=4 control, under 20 CPU seconds / 512 MiB. Downloads have 20–35 second timeouts and were limited to named sources. Existing source/evidence trees are referenced, not copied. Other accepted/in-review targets remain excluded; this lane investigates only 345816.

## Source fidelity and current checks

Read ancestor instructions, campaign ledger/context, sibling discrete-r2 REPORT.md, MATH-NOTES.md, exact 345816 results entry, primary text and exclusion/registry evidence. `references.json` hashes the principal immutable references, including the original PDF and complete registry listings. The original paper was read in the sibling text at Proposition 3.5, Conjecture 4.1 and surrounding Section 4, rather than relying on its abstract. The live arXiv abstract https://arxiv.org/abs/2003.05073 still exposes v1, submitted 11 March 2020. Primary PDF: https://arxiv.org/pdf/2003.05073v1 . This is Dorward's thesis/preprint work (as identified in the sibling source audit); a refereed publication of this exact target has not been established.

Proposition 3.5 states, for the relevant integers n>=3,

    LS_(n,1)(112) = sum_(lambda in D_(n-2)) q^|lambda| [length(lambda)]_q
                  = q[n-2]_q product_(i=2..n-2)(1+q^i).

Conjecture 4.1 asks that this entire polynomial be unimodal. The source reports checks through n=800. This is the ls statistic on restricted growth words containing exactly one 112 occurrence; no other avoidance class, statistic or Sperner property is silently substituted. Definitions and the generating-function bridge are detailed by reference in sibling MATH-NOTES.md. Section 4's separate Conjecture 4.2 asks the stronger Sperner assertion. The source has a confusing index in Proposition 4.6; this report uses the explicit Proposition 3.5 identity and does not obtain a result by correcting that index.

Before new proof investment, inspected the author's actual 2026 successor body, https://arxiv.org/html/2606.15891v1 (16 June 2026; saved in successor.html). Its Question 1.1 still asks whether L(a,b) and M(r) admit SCDs. Theorem 1.1 recalls Peckness for these original lattices; Theorem 2.1 counts SCDs of L(2,n). The later tableau/involution results concern these lattices, not the marked M^1(r) object or Q_m here. No resolution of the 2020 target was located in this body. In particular, an algebraic decomposition into symmetric character intervals is not an actual SCD of M(r); the latter remains an open question in the successor. Its general SCD existence must not be imported as a theorem.

Inspected Hughes's actual 1977 chapter text, pp.135–155, in the publicly displayed OCR of *Number Theory and Algebra*, https://www.scribd.com/document/958427676/Zassenhaus-NumberTheoryAndAlgebra-djvu (chapter around displayed lines 8380–9340, especially printed pp.146–147, Theorem 2). That theorem establishes symmetry and weak unimodality for partitions into distinct parts at most r. The chapter also treats fundamental-representation layer sums, not arbitrary marked copies of each partition. OCR corrupts some signs and fractions: no new quantitative chain bound is inferred from it. No exact Q_m character identification was established.

Read Proctor's scanned primary pp.721–722,724,727,730,733, including its rank-matching lemma and discussion of the linear operators; proctor.pdf and rendered pages are local. https://sites.math.rutgers.edu/~zeilberg/akherim/proctor.pdf . The rank-unimodality/Sperner conclusions apply to L(a,b) and M(r). Its general representation criterion would apply only after constructing the required operators on the new graded space, which this lane cannot do. The original distinct-parts result alone does not imply the target smoothing operation.

**Unclosed source-body audit:** Odlyzko–Richmond, *On the unimodality of some partition polynomials*, EJC 3 (1982),69–84, https://doi.org/10.1016/S0195-6698(82)80010-3 . The publisher body and PDF endpoints returned 403; the author's publication list lists the paper but supplies no body link. Directory access was forbidden and was not pursued. Thus its actual proof/theorem body was NOT audited; the abstract's almost-unimodality statement is not treated as exact clearance or an effective all-m result. Do not advertise the classical prior-body audit as complete. An eventual analytic theorem with an unspecified cutoff does not itself certify all small parameters.

An additional current primary theorem was screened: Mao–Shi–Zhu, https://arxiv.org/html/2609.23779v1 , Theorem 1.3, for product_(k=1..n)[r]_(q^k), with r even or n>=11. This is a different family; no specialization or nonnegative decomposition giving Q_m was established. This screen is not a claim to have checked all recent partition literature.

Current GitHub head requests for both openai/math and the-omega-institute/trureturing returned 403 with X-RateLimit-Remaining=0. Stopped; no alternate API identity, retry loop, clone, or rate-limit evasion. Receipts preserve exact bodies/times. The complete earlier listings pinned to OpenAI 4eaee87548250b2682affda7d05d947c05554bae and Omega 5a97247bf6ad10485d8891db5430b9e34def4933 remain immutable evidence only. Their sibling no-match path screens and selected-body checks are not current-head clearance. Current web searches for Dorward/2003.05073/Conjecture4.1, including these registries, located no exact resolution, but returned unrelated results and do not establish absence. The correct live MathDB URL returned403. An initial wrong mathdb.org URL returned404 and is explicitly not a target-status check. Fetch times fall on 6 November UTC / 5 November Pacific.

## Exact remaining mathematics

For integers m>=1 let [a]_u=sum_(r=0..a-1)u^r and

    Q_m=[m]_(q^2) product_(i=1..m-1)(1+q^i).

Proposition 3.5 gives LS_(m+2,1)(112)=q Q_m. For m>=2, also

    Q_m=[2m]_q product_(i=2..m-1)(1+q^i).

The alternate expression is NOT asserted at m=1: Q_1=1. These identities follow respectively from (1+q^m)[m]_q=[2m]_q and (1+q)[m]_(q^2)=[2m]_q. Multiplication by q merely shifts all coefficients. For n<3 there are no such words.

For m>=2 put d=m(m-1)/2, D=d-1, and let b_m(t) count subsets of {2,...,m-1} of sum t, with b_m(t)=0 outside [0,D]. The exact full target is

    for every m>=2 and every integer 1<=k<=floor((D+2m-1)/2),
    b_m(k)>=b_m(k-2m).

Proof: complement symmetry gives b_m(t)=b_m(D-t). Multiplication by [2m] gives a(k)-a(k-1)=b_m(k)-b_m(k-2m). Q_m is palindromic of degree D+2m-1, so precisely these first differences must be nonnegative. This includes m=2 (B=1,D=0). Q_1 is already handled.

Here is a sharper exact formulation for the unpaid cases, using the actual multiplicities rather than unspecified symmetric unimodality. Fix any m>=4 with m congruent to0 or1 modulo4. Then d=2h is even. Write

    P(q)=product_(i=1..m-1)(1+q^i)=sum_(j=0..2h) p_j q^j,
    c_j=p_j-p_(j-1) for 0<=j<=h, p_(-1)=0,
    C_t=c_(h-t) for 0<=t<=h, and C_t=0 for all other integers t.

Hughes's theorem gives c_j>=0. Telescoping coefficients, followed by symmetry above the middle, proves exactly

    P=sum_(j=0..h) c_j q^j [2h-2j+1]_q.

Let Delta(k)=[q^k](1-q)Q_m. For every integer s with 1<=s<=m-1,

    Delta(h+s)
      = sum_(0<=t<=2m-2-s, t congruent s mod2) C_t
        - sum_(0<=t<=s-1, t congruent s-1 mod2) C_t.             (*)

There is no omitted assumption that h exceeds the displayed bounds: zero-extension of C handles all small m. To prove (*), multiply each interval summand by (1-q)[m]_(q^2). Its positive monomials occur at k=j+2r, and negative monomials at k=2h-j+1+2r, with 0<=r<=m-1. Substitute j=h-t and k=h+s. Positive occurrences require t+s even and 0<=t+s<=2m-2. Negative occurrences require s-t-1 even and 0<=s-t-1<=2m-2. For 1<=s<=m-1 and t>=0 these are exactly the two displayed index sets. Multiplicities are c_j, giving (*).

For 1<=k<=h no negative monomial is possible since 2h-j+1>=h+1. Hence all those differences are nonnegative. Q_m has degree 2h+2m-2 and center h+m-1. It follows that, for each of these m, unimodality is equivalent to nonnegativity of the m-1 expressions (*) — no other coefficient inequalities remain. This is an uncredited exact reformulation, not a uniform proof.

One sufficient pairing would compare each negative C_t with positive C_(t+1): t+1 has the required parity and t+1<=s<=2m-2-s. It would suffice to have C_(t+1)>=C_t for every integer 0<=t<=m-2. That stronger claim is false without small exceptions already at m=4: P_3 has coefficients (1,1,1,2,1,1,1), h=3, and (C_0,C_1,C_2,C_3)=(1,0,0,1). In particular C_1<C_0. Actual nonlocal cancellation in (*) works here: the differences for s=1,2,3 are 0,1,0. This single check demonstrates failure of this proposed pairing; it does not imply that (*) fails. An eventual local concavity estimate for sufficiently large m would require an explicit cutoff and a complete small-case proof. None is provided.

The m congruent2 or3 cases follow by the already documented even-length character-interval argument (sibling notes); these are known-theorem consequences with no credit. The m=1 constant, m=2 interval, m=3 product [3]_(q^2)(1+q)(1+q^2) are covered by the stated arguments. No restricted-residue or helper result is advanced as a discovery.

For a replacement injection the exact required domain for each m>=2 and 2m<=k<=floor((D+2m-1)/2) is subsets S of {2,...,m-1} with sum k-2m; codomain consists of subsets with sum k. The map may delete parts, but must increase sum exactly2m and admit a uniquely recoverable source for every image. Inclusion-only extension is ruled out by the sibling m=13 witness S={3,4,5,6,7}. The unused parts {2,8,9,10,11,12} cannot sum26: two large parts and2 total at most25, whereas three large parts total at least27. Here k=51 is the central permitted endpoint. No replacement algorithm with recoverable state was found, and no arbitrary matching is claimed to fail.

## Decision and formal endpoint

No exact public theorem found here is certified to subsume Conjecture4.1, but source-body and current-registry clearance are incomplete. No full ordinary proof survives. The exact unpaid task is nonnegativity of (*) for all m congruent0 or1 modulo4 and all 1<=s<=m-1, or an equivalent uniform replacement injection. Nonnegativity of individual c_j does not imply this. A generic preservation claim is false (the sibling [3]_q[3]_(q^2) example). Neither more coefficient sweeps nor a longer restricted-case formalization would repair the gap.

Recommend parking. Resume only with a concrete new multiplicity inequality, recoverable injection, or an accessible exact subsuming theorem. Do not spend on Lean now. A faithful eventual endpoint would quantify over all n>=3 and assert unimodality of the literal ls generating polynomial over RGFs with exactly one112 occurrence. It would require formalizing the RGF/statistic bijection in Proposition3.5 AND the all-m inequality, with all small cases; formalizing Q_m alone is not that endpoint. Standard finite-sum/polynomial tools suffice for the reductions, but there is no residual-bridge-free source theorem ready for Lean. Novelty, significance and journal-source limits remain unresolved. No new significant mathematical result or priority claim is made.
