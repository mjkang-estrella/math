# Independent preliminary review: real Mathieu kernel

Recommendation: **EXCLUDE as a routine classical corollary; STOP formal/paper investment.** Ordinary real mathematics passes. The real source goal is explicit enough to be considered independently of the false complex conjecture, but the full positive-real theorem and its Mathieu starlikeness consequence are subsumed by the complex-parameter Bernardi preservation result in Lewandowski–Miller–Złotkiewicz (1976), p.115. This is a complete bridge, not an inference from missing search hits. Root alone decides acceptance. Credit remains 0; observed counts remain 6 additional / 36 total.

SOLO; no children, git commands, shared/parent/other-lane edits, Lean work, paper production, browser actions, messages, uploads, accounts or publication. All new artifacts are in this lane. Read applicable ancestor and batch AGENTS.md, ledger/prior-campaign context, full frozen discovery.md and its objections. No existing review.md specifically matching Mathieu was located in the batch review-file screen. The candidate's objections, not its disposition, were independently reassessed.

## 1. Frozen input and source fidelity — PASS with exact scope distinction

`freeze-before.json` verifies all 33 manifest-bound files against root's review-freeze.json and copies them into `frozen/`. The supplied binding commit is 5ef31e68f5c765aa3c28b9e403415736fed6a47e. Because git operations are prohibited, this review verifies the root manifest's byte/hash binding, not an independent git-object checkout. `freeze-after.json` rechecks both the original paths and own copies against the same manifest. No source edits.

Bansal–Sokół, JMI 13(4) (2019), 911–918, DOI 10.7153/jmi-2019-13-64, actual publisher PDF:
https://files.ele-math.com/articles/jmi-13-64.pdf
SHA256 d152d109ca1f7f0466907d36560a41f14c46aeb3e8d11776ce6c1fedf2a19dcb.
Full eight-page extracted body read; actual p.917 visually read in `source-page-7.png`. Definitions on pp.911–912 use positive real r and the literal normalized coefficients

    a_n=(1+r²)/(n²+r²),  h_r=sum a_n z^n,
    S_r=sum n a_n² z^n.

On p.917 the prose explicitly identifies the desired all-nonnegative-real starlikeness conclusion conditional on convexity of h_2. This is genuine printed source language, not a later reviewer-created domain. The following displayed Conjecture explicitly extends to complex Re r>0. The two must not be conflated. The positive-real theorem alone does not resolve that complex assertion.

Independent exact arithmetic confirms r=1+2i has a_2=(14+12i)/17 and |a_2|²=20/17; then |b_2|=40/17. Convex and starlike normalized coefficient bounds respectively exclude these values. Denominators are nonzero since Im r²=4. This routine complex-domain obstruction is excluded, receives no credit, and is not the reason to count a real result.

2022 actual publisher-version body at TUWien:
https://repositum.tuwien.at/bitstream/20.500.12708/139916/1/Tomovski-2022-Axioms-vor.pdf
SHA256 3acd57b5e72722121e64e9871aa31348c826752edc947eb4f726e0f57a3af98b.
Axioms 11 (2022) 568, published 19 October 2022. Definitions (2)–(3), Lemmas 1–3, Theorems 1–8, examples and conclusions distinguish n² from factorial coefficients. Theorem 2 gives a restricted real-r starlikeness bound for F_mu; it does not claim all r. Its discussion generalizes the 2019 paper, without separately restating an exact all-real open conjecture. No all-real open question is inferred from its general encouragement of future work.

2023 actual AIMS publisher body:
https://www.aimspress.com/aimspress-data/math/2023/12/PDF/math-08-12-1584.pdf
SHA256 4953e36a6d31219780dcb9b4c6c1312721c36b03d265b35c7cc9caaf7288026b.
AIMS Mathematics 8(12) (2023) 30963–30980, published 17 November 2023. Full extracted body read. Equations (1.4)–(1.5) define factorial kernels, and Theorems 2.1–2.24 impose restricted parameter assumptions. Neither its introduction nor its conclusion explicitly supplies a fresh all-real h_r question. Its convexity assertions concern Q_mu,beta, not h_r. These papers supply context, not an independent eligibility cure or novelty clearance.

## 2. Ordinary mathematics — PASS

I independently recomputed the signs and analytic dependencies in the frozen boundary proof. All statements here fix a real r>0; constants and neighborhood sizes may depend on r. No uniformity as r tends to infinity is needed.

(a) The sine coefficient of v(t)=(pi/2)sinh(r(pi-t))/sinh(pi r) is n/(n²+r²). Integrating the sinh factor alone against sin(nt) over (0,pi) gives n sinh(pi r)/(n²+r²); the pi/2 normalization in v cancels the 2/pi Fourier normalization. This identifies Im g with the Poisson extension of the bounded odd boundary function, despite its jump at t=0. For 0<theta,t<pi, cos(theta-t)-cos(theta+t)=2 sin(theta)sin(t)>0, so the paired Poisson kernel is strictly positive. Im g has a strict sign in each open half disk.

(b) The sine generating function gives

    g(z)=(2/pi) integral_0^pi v(t) z sin(t)/(1-2z cos(t)+z²) dt.

For real x in (-1,1), the denominator is |1-x exp(it)|²>0 and the integrand has the strict sign of x on (0,pi). Together with (a), this proves no disk zeros except the simple zero at 0; its first coefficient is 1/(1+r²)>0. Thus using Dg/g later is justified, not circular.

(c) The cos-weight representation over x in (0,1) is valid by termwise integration at every interior z. For any boundary point other than 1, a small complex neighborhood avoids the compact singular ray [1,infinity). The denominators 1-zx are uniformly bounded away from zero, while |cos(r log x)|<=1. Differentiation under the integral of any fixed order is dominated. This proves actual analytic continuation and smooth boundary values there, not just radial-limit existence.

(d) (D²+r²)g=z/(1-z)². On z=exp(it), D²=-d²/dt² and z/(1-z)²=-1/[4sin²(t/2)]. Hence

    u''-r²u=+1/[4sin²(t/2)],  v''=r²v,
    W=u v'-v u',   W'=-v/[4sin²(t/2)]<0  (0<t<pi).

The candidate's negative sign is correct. At pi,

    u(pi)=-(1/pi) integral_0^pi v(t)tan(t/2) dt<0,
    v(pi)=0,  v'(pi)=-pi r/[2sinh(pi r)]<0.

The endpoint integral converges because v(t)=O(pi-t). Dominated passage from the negative real radius is justified near pi by the bound on sin(t)/(1+2s cos(t)+s²) for s near 1 after multiplication by v(t): numerator is O((pi-t)²), denominator is bounded below by a positive multiple of (1-s)²+(pi-t)². Thus W(pi)>0 and the decreasing W is strictly positive to its left. Real-coefficient reflection gives W(2pi-t)=W(t). The imaginary part of g is nonzero except at pi, where u is negative. Finally g_t=iDg and Re(Dg conjugate(g))=u v'-v u', so there is no orientation reversal in the positivity conclusion.

(e) Uniform notch estimate. Put g=-Log(1-z)+H, with H=-r² sum z^n/[n(n²+r²)]. Both H and H' converge absolutely on the closed disk. Set c=H(1) real, M=r² sum 1/(n²+r²)<infinity. The segment from z to 1 lies in the closed disk and |H(z)-c|<=M|1-z|. Also Dg=1/w+E with |E|<=1+M, where w=1-z. For w=rho exp(i phi), |phi|<pi/2 inside the disk and ell=log(1/rho),

    Re(Dg conjugate(g))
      =[(ell+c)cos(phi)+phi sin(phi)]/rho + R,
    |R| <= M+(1+M)(ell+|c|+pi/2+M rho),  rho<1.

This makes the frozen O(ell+1) uniform in phi. Choose rho small enough that ell+c>0. For |phi|>=pi/4 the main numerator is at least pi/(4sqrt2); for |phi|<=pi/4 it is at least (ell+c)/sqrt2. In both regions it dominates the displayed remainder uniformly as rho tends to zero. Tangential approaches are covered; radial positivity alone would not suffice. This neighborhood need not be uniform in r.

(f) q=Dg/g has removable value q(0)=1 and no other disk poles. On the closed disk minus a sufficiently small open circular notch at 1, q is continuous and holomorphic locally in the interior, and Re q is strictly positive on the complete boundary (including both notch endpoints). Compactness and the harmonic minimum principle give interior positivity; the notch region is already covered by (e). Since Dh=(1+r²)g, h' has no zeros and 1+zh''/h'=q. The classical convexity criterion yields convex univalence.

The proof is sound as ordinary complex analysis. No unconditional Lean endpoint is asserted.

## 3. Classical subsumption — FAIL, explicit complete bridge

The decisive original source is Z. Lewandowski, S. Miller and E. Złotkiewicz, “Generating functions for some classes of univalent functions”, Proc. AMS 56 (April 1976), 111–117, application at the end of Section 3, p.115:
https://www.ams.org/journals/proc/1976-056-01/S0002-9939-1976-0399438-7/S0002-9939-1976-0399438-7.pdf
SHA256 a08e819dad041c61037efb3fb92021aa35da59751435ddd94b6bd9106f0496f8.
Full original body read; `lmz-page-5.png` visually confirms the essential non-strict condition Re c>=0, not c positive real. This application states that the analytic normalized solution F of

    c F+z F'=(1+c)f

is starlike whenever f is starlike and c is complex with Re c>=0. Its coefficient operator is

    T_c(sum f_n z^n)=sum [(1+c)/(n+c)] f_n z^n.

For the parameters here n+c never vanishes. The series gives a unique normalized analytic solution: its multipliers are bounded in n. Thus no existence or branch choice is hidden in the integral notation. The source p.115 contains a mistaken parenthetical restriction about analytic solvability and a theorem-number cross-reference typo; neither is used. Coefficientwise solvability is established directly above. The precise starlikeness preservation assertion is also independently reported in Campbell–Singh (1979), p.29, and Oros (2013), p.536.

For real r>=0, let A_r=T_(ir) T_(-ir). Both parameters satisfy Re c=0, and

    [(1+ir)/(n+ir)] [(1-ir)/(n-ir)]=(1+r²)/(n²+r²)=a_n.

This is an identity for every n>=1 and all real r, not a finite coefficient check. Put f0=z/(1-z) and k=Df0=z/(1-z)². The Koebe function k is normalized starlike because Dk/k=(1+z)/(1-z) has strictly positive real part in the disk. Apply the 1976 theorem twice: A_r k is starlike. D commutes with the diagonal operators, and h_r=A_r f0, so Dh_r=A_r k is starlike. Equivalently 1+zh_r''/h_r'=D(Dh_r)/(Dh_r) has positive real part; h_r is convex. All normalizations, domains, and imaginary-parameter boundary hypotheses have now been supplied.

The actual normalized Mathieu series has the equally direct identification

    S_r=A_r² k = sum n [(1+r²)/(n²+r²)]² z^n.

Four applications of exactly the same starlikeness preserver prove S_r starlike for every real r>=0. At r=0, T_0 has multiplier 1/n, so h_0=sum z^n/n² and S_0=sum z^n/n³; the same proof covers the printed nonnegative endpoint. There is no need for a limiting argument or a second credited family.

Additional read primary bodies: Georgia Irina Oros, JMI 7 (2013), 535–541, p.536 explicitly states convex and starlike preservation for complex Re gamma>=0, with the same operator normalization:
https://files.ele-math.com/articles/jmi-07-49.pdf
SHA256 6447470b385623d64321dca6059c00e45a320572c20b9db53cb48e5eb75a2e82.
Campbell–Singh, Pacific J. Math. 84(1) (1979), 29ff, p.29 explicitly records the complex-parameter LMZ extension:
https://msp.org/pjm/1979/84-1/pjm-v84-n1-p03-s.pdf
SHA256 afb564f0bd7f5c5e8f0d69816e5b5c03fdd15b07a882f79ba2b0fff549482a7c.
The local filename `barnard1979.pdf` is merely an initial retrieval label; authors are Campbell and Singh. Their p.30 contains an overbroad convolution description, which is NOT used.

The frozen caution that a positive-real Bernardi theorem cannot automatically be used at imaginary parameters is correct. What changes the decision is the actual original theorem including the closed right half-plane. This is substantially stronger evidence than a heuristic factorization. Hypergeometric rewritings and typical-real ODE literature need no further clearance to support exclusion once this exact older multiplier theorem already carries the endpoint. No worldwide priority claim.

## 4. Source eligibility and substantive calibration — FAIL overall

Strongest case for investment: p.917 explicitly asks for a mechanism giving all nonnegative-real starlikeness, the paper actually develops real r, and the candidate supplies a nontrivial correct analytic proof. Merely observing the broader complex conjecture is false would be insufficient to erase that printed real goal. I therefore disagree with treating complex-vs-real scope mismatch alone as a conclusive bar to considering the real goal.

Nevertheless the present real endpoint is an immediate composition of two instances of a published preservation theorem; its starlikeness consequence is four instances on the standard Koebe function. The only object identification is the exact quadratic factorization. This is a routine equivalent multiplier corollary under the batch's explicit exclusion rule, even if no later author has printed this precise Mathieu conclusion. The ODE proof's independent interest does not change endpoint subsumption.

Calibration uses actual criteria, not proof time. Ledger outcome31 resolves a separately printed surviving real arcsinh question and retains an unresolved possible two-point norm subsumer caveat. Outcome32's root INVESTMENT-DECISION-R2.md and PERSPECTIVE-OBJECTION.md explicitly acknowledge standard perspective convexity yet retain the Gamma-specific Euler identification and strict two-shift level-curve assembly. Those precedents show that classical tools and brevity alone do not disqualify. Here, by contrast, a read class-preservation theorem acts on the exact coefficient multiplier, includes the exact imaginary boundary parameters, and closes both target conclusions with only multiplication of two linear factors. This is closer to the ledger's explicit classical-corollary exclusions (Hoggatt, An–Djokovic, SOL-period) than to an unsupplied generic-tools objection. Root may adjudicate otherwise, but I recommend no investment and no quota stretching.

## 5. Current public screen and chronology — bounded; no novelty clearance

Live head refresh UTC 2026-10-29T15:11:06–07Z, recorded with URLs, response hashes, byte sizes and statuses in `http-review.jsonl`. Four heads unchanged from r51: Omega main d7af67136d4478875778ac6e75eb5fbb8b3693a5; OpenAI 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a; AIM 8729eab98bafe409b66c5e39253bf56569a62327; Count dbf673741a54c7dc9d88a6aec0e8148a538f4a3a. Omega dev advanced to b386687d1b21d80059f9b18b696db3503dbfa340 (15:08:15Z). Exact compare from frozen e1d4e12fbc1f1f82e5f88362e931a52c778b4374 is saved as `omega-delta.json`: two commits, one changed file, docs/develop/theory/FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_XI.md, unrelated to Mathieu; no D5/Problems changes. This is a relevant-delta statement, never whole-dev clearance.

All named complete baseline scope hashes in frozen registry-screen.json were independently verified and copied here as registry-*.json: Omega D5 12552 and Problems 1551, Omega main 69, OpenAI preprints 13578, AIM 3541, Count 183 entries. Baseline lexical screen is inherited only as a bounded filename screen, not absence of semantic counterparts. The exact older subsumer was established from an actual 1976 claim body and predates the 2019 question and both 2022/2023 followups. There is no reliance on later independent public material being a prior proof merely because it is now searchable.

Bounded fresh public searches covered complex Bernardi preservation, original 1973 convolution, original LMZ title, and Mathieu/Bansal/Sokół convexity/conjecture with 2024–2026 terms. No separate exact newer Mathieu resolution was identified in returned results. Search absence is not clearance; no exhaustive citer, specialist database or MathDB solution-body audit is claimed. Since a complete 1976 subsumer was located, such absence cannot rescue novelty.

Access gap: the E-Periodica 1973 Ruscheweyh–Sheil-Small endpoint returned HTTP200 challenge HTML, not a PDF (2682 bytes; SHA256 99db20996e773331668b73504feee8be893cf14abe485e2462b9202beaf67ca2). A web open likewise returned verification-required content. No challenge was solved, bot link followed, account used or bypass attempted. The misnamed `rss1973.pdf` preserves those exact HTML bytes. I do NOT claim to have read the original 1973 body, and search snippets do not clear that dependency. The printed classical convolution route consequently retains an original-body access gap. However, the independently complete four-Bernardi consequence above avoids that dependency entirely and suffices for this EXCLUDE decision. No eligible substantive scope is promoted requiring further RSS assembly.

## 6. Approximate formal feasibility — possible, unproved, no investment

The ordinary theorem is amenable in principle to formalization, but no Lean source/library feasibility claim has been tested. The frozen proof would require holomorphic power series, Poisson boundary recovery with a jump, positivity, analytic continuation, Wronskian calculus, branch-log estimates on a notched disk, harmonic minimum principles and the geometric convexity criterion. These are substantial analytic bridges; they cannot remain assumptions in an accepted endpoint. A formal proof of the classical Bernardi theorem plus coefficient identities would likely be the cleaner mathematical route, but would formalize an existing theorem and its routine corollary. No Lean start, no unconditional formal theorem, no paper investment recommended.

## 7. Independent diagnostics and limits

`independent_checks.py` is newly written, not a rerun of the candidate checker. Exact Q(i) arithmetic verifies the excluded complex coefficients. Rational arithmetic checks the conjugate multiplier at several inputs; the universal algebraic identity is proved in Section 3. Independent 40-digit quadrature of the cos-integral g, Dg and D²g checks the sine boundary formula, the ODE sign and Re(Dg/g) for nine (r,t) points including t=pi; all assertions passed. These are diagnostics, not proof of any universal sign or numerical certificate. The notch is justified by the explicit analytical bound in Section 2, not by probes.

`checks-guard.json`: exit0, no cap reason, sampled peak group RSS 17,702,912 bytes, wall approximately0.535s. Helpers ran via the frozen cap wrapper: AS512MiB, CPU210s, wall230s, BLAS1, process-group RSS/CPU sampling. Transients and reaped-child CPU are not exhaustively measured. `http-review.jsonl` records access times and hashes; frozen provenance records cached-source retrieval UTCs. `artifact-hashes.json` inventories new evidence.

Final recommendation remains **EXCLUDE / stop investment**, despite ordinary-math PASS and recognition of the separate explicit real source goal. The decisive issue is the complete older complex-Bernardi multiplier bridge. Credit0. No acceptance or ledger update performed.
