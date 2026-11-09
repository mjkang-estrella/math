# Focused follow-up: Sun4.4 resolved publicly; one fresh source-question pivot

Disposition: **Sun Conjecture 4.4 is already proved in full by Mao–Pan, arXiv:1801.02213v2, Theorem 1.1. No discovery nomination or count.** Pivot: Guo, arXiv:1901.07908v1, Conjecture 6.1, all positive n congruent to 4 or 7 modulo 9. A complete classical q-Pfaff–Saalschütz bridge is in pivot-proof.md. This is research-level mathematics only, with prior-art/credit HOLD: no Lean, manuscript, acceptance or worldwide priority assertion.

Root alone accepts/counts/stages. Administrative snapshot: 9 additional, 39 total, next40. No shared edits, git operations, browser, external communications, MathDB mutation, Lean or manuscript work. All output is in this lane. Other active r218/r219 scouts may overlap in q-hypergeometric sources; root should reserve this exact pivot before assigning a further solving lane. No communication to other workers was performed.

## Literal primary statement and public full-proof bridge

Sun, *On sums of Apéry polynomials and related congruences*, actual https://arxiv.org/pdf/1101.1946v4, p27, Conjecture 4.4: for EVERY odd prime p, EVERY integer n>=2, h=2n+1, EVERY x in Z_p with x=-2k mod p for SOME integer 1<=k<=floor((p+1)/h),

    sum_{r=0}^{p-1} (-1)^r binom(x,r)^h = 0 mod p^2.

The fetched explicit v4 PDF is byte-identical to the frozen scout PDF (SHA256 b1bfd6f01416354f6e6b9867434e5a3f80ca598801d6dc5238ea28715d076a20). The actual abstract history lists v1 Jan10 2011, v2 Jan11 2011, v3 Jun22 2011, v4 Apr28 2014 15:39:45 UTC. The paper is cited by Mao–Pan as J.Number Theory132(2012),2673–2690; we do not identify every arXiv revision with that published version.

Mao–Pan, *On the divisibility of some truncated hypergeometric series*, https://arxiv.org/pdf/1801.02213, actual v2, cover March5 2018, pp1–2 explicitly quotes Sun4.4 and identifies the binomial-to-Pochhammer conversion. Theorem1.1: for every odd prime p, integer R>=1, alpha in Z_p with alpha=2a mod p and 1<=a<(p+R)/(2R+1),

    sum_{j=0}^{p-1} (alpha)_j^(2R+1)/(j!)^(2R+1) =0 mod p^2.

Set R=n, alpha=-x, a=k. The range is valid because k<=(p+1)/h<(p+n)/h for n>=2. Since binom(x,j)=(-1)^j(-x)_j/j!, the two signs cancel: (-1)^j binom(x,j)^h=(-x)_j^h/(j!)^h, as h is odd. Every denominator j! is a p-unit. This retains all primes, all h, all admissible k and every p-adic x. It does not replace x by an integer. Empty k ranges are vacuous. h divisible by p is included in Mao–Pan's proof and Remark2.1. No n=1 or fixed-input result is used to claim the full theorem.

Mao–Pan's complete eight-page body was read, including the actual proof pp3–7. The classical ingredient is its Lemma2.1 (Karlsson–Minton terminating vanishing). The proof combines antisymmetry at an odd negative integer with two evaluations of a one-parameter derivative. Its parameter inequality 2p-2a>2R(2a-1) is exactly implied by a<(p+R)/(2R+1). Harmonic reflection supplies a second relation; the two equations force the derivative to vanish when p does not divide 2R+1, while that divisibility makes the full derivative vanish directly. This is a full applicable bridge, not exclusion inferred from shortness.

The primary proof contains harmless display slips: the relation between the diagonal derivative and the one-coordinate derivative is needed only at zero (the globally printed psi'(x)=h phi'(x) is not generally true); some later summation upper limits print p-2k where p-2a is intended; and the last cutoff sentence on p5 should refer to indices beyond p-2a. These do not alter the theorem specialization above. We do not nominate a correction as a new result.

Public chronology: arXiv abstract history v1 Jan7 2018 16:57:43 UTC; v2 Mar5 2018 00:59:48 UTC. The abstract explicitly warns that an incorrect first-version Theorem1.2 was removed. We rely on the surviving v2 Theorem1.1, not that removed statement. A journal publication for Mao–Pan was not verified; the full proof was publicly available in 2018.

## Independent reduction check and conceptual routes

Let N=p-2k. Since h>=5 and hk<=p+1, 0<N<p and N is odd. F(X)=sum_{r<p}(-1)^r binom(X,r)^h belongs to Z_p[X], because r! is a p-unit. Pairing r,N-r gives F(N)=0 exactly, with r>N terms zero. For every u in Z_p, Taylor expansion gives F(N+pu)=pu F'(N) mod p^2. For r>N the binomial polynomial has a root at N and its h-th power has zero derivative there. For r<=N, logarithmic differentiation yields

    F'(N)=h sum_{r=0}^N (-1)^r binom(N,r)^h (H_N-H_{N-r}).

This independently verifies the scout's entire reduction and explains why one integer test F(N)=0 cannot settle all x. The missing harmonic identity is supplied by the public Mao–Pan theorem; reconstructing it further would repeat public work.

Two conceptual mechanisms examined: (1) finite-field polynomial/Taylor and harmonic reflection, which alone leaves the derivative identity; (2) exact terminated hypergeometric vanishing plus shifted-tail comparison, the actual public Mao–Pan mechanism, which closes it. We stopped original-target proof investment once the exact public proof was found. The pivot separately has a direct root/derivative route and a successful two-deformation route; see pivot-proof.md.

## Targeted later-body coverage, limits and pivot status

Actual bodies inspected: Meng–Sun1502.06909v3 (2015, complete6pp), Wang–Pan1806.02735v2 (2018, theorem/auxiliary sections and references), Wang–Xia2002.08814v2 (2020, Theorems1.1–1.2, Karlsson–Minton Lemma2.1 and derivative mechanism), Mao–Pan1703.01215v4 (2018, introductory theorems/relevant identity discussion and references), Guo1901.07908v1 (2019, full9pp), Guo–Zudilin1803.01830 (actual concluding conjectures and surrounding microscoping identities), Guo–Schlosser1901.07962v3 (2019, main theorem statements, transformation mechanisms and concluding conjectures). Partial bodies were not represented as complete reading. Mao–Pan1801.02213 is an actual direct citer of Sun1101.1946; Guo–Schlosser is an actual direct citer of Guo1901.07908. We do not falsely label every thematic neighbor a direct citer.

Meng–Sun fixes the input p/m-q and requires m even or q odd: its theorem is not a full Sun4.4 subsumer. Wang–Xia retains a fixed input and parity condition. Wang–Pan's prime congruence and fixed parameters do not match all alpha. Guo's Theorem1.1 has gcd(r,d)=1 and n=-r mod d and proves a particular q-family; we found no literal all-x specialization and make no such claim. Guo–Schlosser explicitly proves Guo Conjecture1.3 (its Theorem3), so that neighboring question was not selected. Its classical transformation techniques, including insertion of parameters in multiple places, are credited.

Pivot6.1 is a real source question, distinct from Sun4.4 and the scout's named targets. It is fresh relative to a bounded screen of699 direct lane report files (hashes in history-screen.json); no literal identifier hit was found. This cannot clear all campaign history, aliases, evidence trees or literature. The selected question has a full symbolic proof bridge in pivot-proof.md, but that proof is a direct classical identity application and we do not recommend counting it as a substantive new discovery without root's stricter adjudication. No known published exact proof was located in the bounded searches; that is not a claim it remains open in 2026. Current GitHub proof-registry access remains denied and was not retried; no current head was obtained. Prior-art and registry gates remain HOLD.

## Evidence and checks

http.jsonl records exact URLs, UTC, response status, byte count and SHA256 for each retrieved body. Original assigned scout/source files were selectively copied and hashed before scientific reading; freeze.json binds them. Administrative ledger/NEXT are snapshots only. retrieved-freeze.json binds downloaded local bodies to working copies; downloaded bodies were initially inspected as retrieval artifacts before this second freeze (explicit limitation, not concealed). Final verification rechecks both original paths and copies. Final manifest explicitly excludes itself and verification-receipt.json; verification is a separate guarded invocation after final writes.

checks/checks.py independently verifies the original reduction for231 admissible (p,h,k) triples with p<=43 and all7527 residue lifts modulo p^2; h varies, including h=p. It also verifies pivot6.1 exactly over Q[q]/Phi_n(q)^2 at n=4,7,13,16. These finite exact checks are not universal proofs. The universal pivot proof uses the displayed classical identity and uniform index bounds, not computation.

Access/protocol failures are in FAILURES.md. No forbidden route was retried. No absolute literature priority, exhaustive citation search or unrestricted full-history clearance is asserted.

Classical-body supplement: Schilling–Warnaar math/9909044v1, actual p1 Eq(1.1), was read on a distinct allowed arXiv route after stopping NIST403. It exactly verifies the q-Pfaff–Saalschütz input and its specialization in pivot-proof.md; its URL, UTC and hash are in http.jsonl. Only its introductory formula and context were read, not its complete generalized-identity proof.

Supplemental validation: checks/pivot_deformations.py verifies both exact deformations at n=4,7,13,16 and the linear index inequalities for all l>=0 using symbolic coefficient signs. Results are in checks/pivot-results.json. This is a cross-check of the written proof, not independent novelty evidence.
