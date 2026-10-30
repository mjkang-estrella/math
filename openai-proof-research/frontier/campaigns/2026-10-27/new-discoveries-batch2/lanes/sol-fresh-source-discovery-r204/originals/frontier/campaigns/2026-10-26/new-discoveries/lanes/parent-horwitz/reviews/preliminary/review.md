# Preliminary adversarial review — Horwitz osculating mean / MathDB 327618

Reviewer: pi-horwitz-preliminary-review (solo, no children, standard speed).
Candidate: `lanes/parent-horwitz` frozen at git 345d4819d3e6b336623c3ee41aceede51a3394b0.
Verdict: **HOLD** (mathematics PASS, source PASS, novelty HOLD with one material unread
source, substantive eligibility conditionally PASS). Credit 0; accepted tally 24/30 unchanged.
No Lean certificate or paper exists; **no formal PASS is claimed or implied**.

## 0. Integrity of the frozen candidate

All 17 files of `preliminary-review-hashes.json` (plain map, 17 entries) were SHA-256
verified against the frozen parent lane **before** review and re-verified on a byte copy in
`own-copy/` **after** the review completed: 17/17 match at both times. No shared or candidate
file was edited; no staging, commits, counts, or external contact.

## 1. Source gate — PASS

- arXiv:1404.1489v2 (stored pdf/txt, hash-verified): Conjecture 1, p.19, states for
  x_1(t)=t, x_2(t)=t^2, …, x_{n−1}(t)=t^{n−1}, x_n(t)=log t that
  M_n(a_1,…,a_n)=I_Z(a_1,…,a_n), with I_Z displayed exactly as
  exp[(1/V)Σ_i(−1)^{n+i} a_i^{n−1} V_i(a) ln a_i − m], V=∏_{1≤j<i≤n}(a_i−a_j), V_i the
  (n−1)×(n−1) Vandermonde (rows 1,a,…,a^{n−2}) of the remaining columns in increasing
  index order, m=H_{n−1}.
- Published JCA 4(1) (2014) 41–61, DOI 10.7153/jca-04-02 (stored `osculating-published.pdf`
  / `.txt`): same conjecture, **unnumbered, retained on the last page p.61**; the paper defines
  M_k(a_1,…,a_n)=x_k^{-1}(i_k) for the intersection point P=(i_1,…,i_n), so M_n=exp(last
  coordinate). The n=3 case M_z(a,b,c)=IZ(a,b,c)=U_2(a,b,c) is explicitly credited (Stolarsky
  [6]).
- MathDB 327618 refetched live (HTTP 200): byte-identical to the stored `327618-live.json`
  (sha256 7e028734…d1d474). Status `open`, `solutions: 0`, no human solves, no model attempts.
- Exact hypotheses: n≥2, 0<a_1<…<a_n (the identity is symmetric, so pairwise distinct positive
  nodes is the equivalent unordered form; a formal endpoint should state the ordered form or
  prove symmetry).

## 2. Mathematics gate — PASS (independently re-derived)

I re-derived every step from scratch and built an independent checker `review_check.py`
(fresh code, not derived from `check_proposal.py`; output `review_checks.json`):

1. **Taylor identity.** log a − H_m + Σ_{j=1}^m C_j (t/a)^j with C_j=(−1)^{j−1}binom(m,j)/j
   equals the degree-m Taylor polynomial of log at a; contact of order m at t=a. Verified
   symbolically n=2..14. The coefficient identity Σ_{k=j}^m binom(k,j)/k = binom(m,j)/j
   (via binom(k,j)/k=binom(k−1,j−1)/j + hockey stick) verified m=1..14. The key normal is
   (−C_1/a,…,−C_m/a^m,1) — **with minus signs on the C_j components**; during my own
   derivation I initially wrote the sign wrong and the checker caught it; the parent's PROOF.md
   has it right.
2. **Literal Wronskian normals.** With the source's own convention
   n̂(t)=(W_{1,n},−W_{2,n},…,(−1)^{n+1}W_{n,n}), W_{j,n}=W(x′_1,…,x′_{j−1},x′_{j+1},…,x′_n),
   verified n̂(t) = (−1)^{n+1}∏_{j=1}^{m} j! · (−C_1/t,…,−C_m/t^m,1) for n=2..9, so the
   source's osculating hyperplane (x̂·n̂(a)=α̂(a)·n̂(a)) **is exactly** the plane
   z=log a−H_m+Σ C_j y_j/a^j, not merely tangent to some order. The first m coordinates of
   α′(a),…,α^{(m)}(a) are triangular with diagonal 1!,…,m!, so the annihilator is 1-dimensional
   and the last cofactor (−1)^{n+1}∏j! is nonzero. This is a complete bridge, no ECC hypothesis.
3. **Intersection = interpolation.** The linear map (z,y_1,…,y_m) ↦ Q(t)=(z+H_m)t^m −
   Σ_j C_j y_j t^{m−j} is a bijection onto polynomials of degree ≤ m because every C_j≠0.
   Membership of P in all n hyperplanes ⟺ Q(a_i)=a_i^m log a_i for all i. Ordinary Lagrange
   interpolation at distinct nodes gives existence and uniqueness of the actual intersection
   point; the leading coefficient gives z+H_m=Σ_i a_i^m log a_i/∏_{k≠i}(a_i−a_k). Verified
   numerically-symbolically by solving the **literal source plane equations** at generic random
   positive rational nodes (not the special nodes 1..n), exact arithmetic, n=2..9.
4. **Sign identity against the source display.** (−1)^{n+i} V_i/V = 1/∏_{k≠i}(a_i−a_k) with the
   source's own V_i column convention, verified as a symbolic rational identity n=3..6 and
   exactly at random rational nodes n=7..10. Hence the proposed expression equals the literal
   I_Z display of both the arXiv and published source and of the MathDB statement. (Sign
   conventions here are the most error-prone point; checked twice.)
5. **Mean property.** d^m/dt^m(t^m log t)=m!(log t+H_m) verified m=1..12; Rolle on f−Q with
   n=m+1 nodes gives z=log ξ, min(a_i)<exp(z)<max(a_i). This part is classical-in-spirit
   (the divided-difference mean value theorem; Mustonen 2002 uses precisely this mechanism for
   the logarithmic mean) and receives **no credit**; it is a sanity proof, not the candidate.
6. No hidden hypothesis, no circularity, no use of an unverified Chebyshev-system condition.
   The proof is complete and universal for all n≥2 and all pairwise distinct positive nodes.
   Finite symbolic checks are evidence only and are not part of the argument.

## 3. Novelty gate — HOLD (one material unread source; bounded screen otherwise clean)

What I read (all OA/legitimate routes):
- **Horwitz 1996 (JMAA 200, 126–148, DOI 10.1006/jmaa.1996.0195): body UNREAD.** Re-confirmed
  the parent's access failures: ScienceDirect PDF 403; Elsevier api metadata only / view FULL
  401; Semantic Scholar shows bronze OA but the PDF is the same blocked SD URL. Read instead:
  the zbMATH review summary via MaRDI (Q1915593): general mean-value theorem for functional
  determinants of ECC systems + intersection result defining n means — no mention of the
  identric curve; and the 2014 author's own account of [1]: the logarithmic example proved in
  1996 is the **Pittenger curve** (t^k, k=1..n−2; log t; 1/t) → M_n=Pittenger, a different
  curve. This makes the risk lower but does not close it.
- **All 7 OpenAlex-indexed citers of Horwitz 1996 enumerated and assessed:** Ait-Haddou–Mazure
  2016 FoCM (full intro read: blossoming in *polynomial Müntz spaces* — power functions only;
  log t is outside; no IZ identity), Horwitz 2000/2002 "Invariant means" (arXiv math/0007095
  abstract read; invariance topic, 2014 paper still states the conjecture after it),
  Ivan–Neagos 2021 Numer. Algorithms (full intro read: generalized interpolation machinery,
  cites 1996 as background), Ilyuta 2004 (mathnet, title/abstract-level: intertwined zeros and
  divided differences), and the 2014 source twice. The 2014 paper has **0 indexed citations**
  (OpenAlex, both records).
- **Horwitz 2008 "Means and Hermite interpolation" (JMI 2(1) 75–95): full body read (OA).**
  Two-variable means from intersections of Hermite interpolants of x^p-type functions; no
  n-variable identric curve. Not a subsumer.
- **Mustonen 2002 (survo.fi): full body read (OA).** Neuman's logarithmic mean via divided
  differences of exp; appendix documents Xiao–Zhang's (24) as equal to Neuman's L. No
  identric/osculating content. Not a subsumer.
- **Xiao–Zhang 2003 (JIPAM 4(2) Art. 39): body NOT obtained** (EMIS mirrors 403/404/dead;
  wayback temporarily offline). Minor: its content is the G≤L≤I≤A inequalities (cannot subsume
  an exact identity) and the IZ definition itself, which is fully displayed in the read 2014
  source with the V_i convention I verified. Recorded, not decisive.
- **trureturing clone** (read-only, `pi-euler-turan-final-review/fresh`): no entry for 327618,
  1404.1489, or the identric/osculating pair; the StolarskyMean blueprint is the unrelated
  two-variable matrix Stolarsky problem. Confirms the parent's screen.
- Additional targeted web searches (exa): only the original sources surface; no resolution,
  no author follow-up, no public proof registry entry.

**Material objection (decisive for novelty):** the closest possible subsumer, Horwitz 1996,
is unread. Its title includes "Generalized Divided Differences"; if it contains a general
closed-form for intersection coordinates of an ECC curve (e.g., a Mühlbach-type generalized
divided difference formula) plus an example or remark on the curve (t, t², …, t^{n−1}, log t),
the proposed result could be an immediate specialization. The 2014 paper's own account and the
zbMATH summary argue against this, but neither is a substitute for the theorem bodies. Per the
counting standard and the user's exclusion of "reassuring known results", no prior PASS can be
recorded on this evidence alone. Note also the adjacent unread blossoming line
(Ait-Haddou–Yusuke–Nomura 2013; Mazure 1998 Vandermonde-type determinants) — bounded risk
since the 2016 paper shows that line restricts to power functions.

## 4. Substantive eligibility — conditionally PASS

- The result is **not** an immediate corollary of anything I could read. Horwitz's Theorem 1
  (even if its ECC hypothesis were verified for this curve) yields only existence, uniqueness
  and internality — no closed form for any coordinate. The exact IZ identification needs the
  specific contact computation and the Vandermonde sign matching, and none of the read sources
  contains either. The blossoming literature read restricts to power-function spaces.
- The proof is short, but shortness is not an exclusion category in the ledger; the excluded
  categories (already-published/posted proofs, re-formalizations, special-case counts,
  equivalent corollaries, wording/normalization fixes) do not apply **provided** the novelty
  gate closes. Eligibility is therefore conditional on novelty: if the 1996 body (or any other
  source) is found to contain the computation, the result becomes an excluded corollary and
  FAILs.
- One outcome only: the all-dimensional exact identification. Internality, the n=2 tangent-line
  identric fact, the known n=3 case, Lagrange interpolation, and Rolle are standard/credited
  and receive no separate credit.

## 5. Formal bridge requirements (for any future Lean endpoint)

1. Literal curve α(t)=(t,t²,…,t^{n−1},log t) and the literal source osculating hyperplane via
   the cofactor/Wronskian convention n̂_j=(−1)^{j+1}W_{j,n}; define O_a as x̂·n̂(a)=α̂(a)·n̂(a).
2. Prove n̂(a)=((−1)^{n+1}∏_{j=1}^{n−1}j!)·(−C_1/a,…,−C_m/a^m,1) with
   C_j=(−1)^{j−1}binom(n−1,j)/j, hence O_a is the plane z=log a−H_{n−1}+Σ_j C_j y_j/a^j
   (contact through order n−1; do not assume it).
3. Prove existence and uniqueness of the intersection of O_{a_1},…,O_{a_n} directly (coefficient
   bijection / interpolation); no ECC hypothesis and no citation of Theorem 1.
4. Identify exp(last coordinate) with the **literal** source expression
   exp[Σ_i(−1)^{n+i}a_i^{n−1}V_i(a)log a_i/V(a) − H_{n−1}] with V(a)=∏_{1≤j<i≤n}(a_i−a_j) and
   V_i the (n−1)×(n−1) Vandermonde of the remaining columns in increasing index order — the
   V_i/V sign identity must be proved, not assumed.
5. State nodes as 0<a_1<…<a_n (literal source) or prove symmetry for the unordered statement.
6. Standard Lagrange/Rolle steps may be cited as classical tools; no new axioms; the internality
   lemma is optional and uncredited.

## 6. Decision

- Mathematics: PASS. Source fidelity: PASS. Independent re-derivation: PASS (incl. one sign
  trap caught and resolved).
- Novelty: **HOLD** — the Horwitz 1996 body must be read (library/alternate route) or the
  parent must explicitly accept the documented limit as in precedent outcomes; the Xiao–Zhang
  and blossoming unread items are minor and recorded.
- Substantive eligibility: conditionally PASS (short but not a known corollary of anything
  read; flips to FAIL if a subsumer surfaces).
- Overall preliminary verdict: **HOLD.** No discovery credit; accepted 24/30 unchanged. No
  Lean/paper exists; no formal PASS is claimed.
