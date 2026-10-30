# r161: Ulas two-parameter irreducibility remains unresolved

Research UTC: 2026-10-30. Credit 0; no nomination, Lean, manuscript, or PROOF.md.
Counts remain 9 additional / 39 total, next 40. Solo, assigned-lane writes only.

## Selection and source fidelity

Two precise claims were screened. The ordinary reciprocal-subsum denominator
log-concavity claim (Ballantine–Beck–Feigon–Maurischat 2605.10512,
Conjecture 4) was retired immediately on reopening original discrete-r6,
denominator-dyadic-r1 and r124 reports. Their existing unresolved disposition
and mixed-curvature obstructions remain unchanged. No new denominator experiment.

Selected: Maciej Ulas, *Strong arithmetic property of certain Stern polynomials*,
arXiv:1909.10844v1, Conjecture 4.2(3), actual PDF pp15–16. This is one full
two-parameter irreducibility claim, not the same paper's real-root clauses,
Conjectures 4.3/4.4, or prime-index irreducibility.

Use the BODY definition p2 (the abstract incorrectly writes n-1):
B0=0, B1=1, B_(2m)=t B_m, B_(2m+1)=B_m+B_(m+1).
For every integer k>=2 and n>=1 define

    p_(k,n)=2^(2n+k)-3*2^(n+k-1)+2^k-3,
    V_(k,n)(t)=B_(p_(k,n))(t).

The conjecture says V_(k,n) is reducible over Q iff k>=3 and n=k-1.
On that diagonal it gives the exact factorization

    V_(k,k-1)=(1+2 sum_(i=1)^(k-2) t^i)
               (V_(2,k-2)+2 t^(k-2)(1+t)),

with both factors irreducible. All these quantifiers remain in the selected
target. Neither a finite rectangle nor only the k=2,3 cases would resolve it.

Current arXiv metadata advertises only v1 (24 September 2019) and says a
revised version will appear in Publicationes Mathematicae Debrecen.
The actual source Theorem 2.3 pp6–8, its formula and coefficient proof,
and the Section 4 Eisenstein proof and exceptions were read before testing.
The known k=2,3 polynomials have constant 1, other coefficients even and
leading coefficient 2; reversing and applying Eisenstein at 2 proves them.
The same source explicitly proves the displayed diagonal factors irreducible
by that criterion. These known cases and factors receive no credit here.

Published DOI 10.5486/PMD.2020.8683 identifies the 2020 article (96,401–422).
The current DOI redirects to an explicit no_subscription page (HTTP200),
not its proof body. Both old publisher load_doc links returned404. No
subscription/access workaround was attempted. Thus the revised published
scope remains an actual-body gap. This lane does NOT claim source clearance
or that the arXiv wording remains the exact published question.

## Historical screening and public comparisons

Before downloads/investment, the qualified original full SUMMARY/discovery/
PROOF/review/DECISION bodies were searched for exact ID/title/author/claim
aliases. The r150 baseline and r153/r155/r158 deltas were reused; a later pass
also reuses the qualified r157 original index and discovers changed/new
originals. Original r111–r113 files remain in scope. No original lane is
wholly excluded; copied/frozen/extracted evidence is excluded by role.
Full bodies, not just displayed snippets, are queried. Queries and reopened
body hashes are retained, with no global match cutoff. This is qualified
historical coverage, not all-workspace semantic absence.

The first exploratory author pattern mistakenly matched `Ulas` inside
`formulas`; its noisy output is not negative evidence. A word-boundary
correction supplies the operative screen. One inherited frozen-copy and
extracted-replay role omission was corrected. A missing r157/history-delta
path caused a failed command; the actual r157/history-receipt is used instead.

Reopened exact Altizio-related matches are original r39 and r63 reports:
they concern the full Stern half-plane conjecture and explicitly leave it
unresolved; they do not settle this V_(k,n) family. The root Mittag proof's
author match is unrelated. Prior reciprocal-subsum matches were reopened
as above. No exact prior V_(k,n) resolution was found in this bounded scope.

David Altizio, *Zeros of Stern polynomials in the complex plane*, current
2511.03847 metadata/PDF was fetched; actual statements pp2–3 and complete
factor-evaluation proof p9 were read. Its disk theorem says every Stern
root avoids |z-2|<=1. For an integral factor P, this implies |P(2)|>1.
Together with B_p(2)=p this forces irreducibility when the INDEX p is prime.
Our p_(k,n) need not be prime. The argument supplies no obstruction to
p_(k,n)=P(2)Q(2) with both factors >1 when this index is composite. Hence
it is not full subsumption; no claim about unseen thesis results is made.
The companion itself attributes its prime result to a different Ulas–Ulas
question. Its main disk theorem is used here only to assess this attempted
bridge, not assumed to resolve the chosen target.

The live observed heads at 01:03 UTC are Omega
b62773edfb6a6f7806de09b593b2e3b6834685c7 and OpenAI
4eaee87548250b2682affda7d05d947c05554bae, unchanged from r157. No repeated
HEAD chase. Reused complete cached trees, Problems records, r157 uncapped
deltas, and the older qualified deltas were screened. The two historical
300-path gaps remain; newer uncapped deltas do not fill them.
Broad lexical Ulas hits include irrelevant `formulas` paths and hash names;
they are retrieval noise, not semantic matches. The target-facing Altizio
Problems dossier and Blueprint were fetched at the actual current immutable
head and read in full. Their exact endpoint classifies geometric-sum disk
degrees {5,6,7}, a different inequality in the companion's Remark 4. Its
boundary defect/maximum-modulus argument is not an irreducibility theorem
for V_(k,n). No registry exclusion of the selected target or worldwide
novelty clearance is asserted. Registry chronology is recorded by immutable
heads and dated HTTP receipts; no prior-proof exclusion rests on an abstract.

## Sustained algebraic route

The source formula, after clearing denominators, gives the exact identity

    (t-1)^3 V = (t+1)t^(n-1)(2t^n-t-1)(t-1)^2
        +(2t^(k-1)-t-1)
           [(t^(n-1)-1)(2t^n-t-1)+t(t^n-1)(t-1)].       (H)

It is a polynomial identity including t=1; it does not exclude that point.
It follows by multiplying the source's explicit Theorem 2.3 expression
by (t-1)^3. Independent binary Stern recursion checks it in every tested
pair. My first expansion omitted the last (t-1) inside the bracket and
failed its very first exact assertion. That failure is a calculation error,
not a source counterexample. The corrected unexpanded form (H) passes.

For k>=5,n>=4,n!=k-1 put

    d=2n+k-5,    d0=max(2n-1,n+k-2).

The source parity proof gives V=1 mod2. Identity (H) gives degree d and
leading coefficient 4. The largest index with coefficient 2 mod4 is d0:
in H the top potentially surviving terms mod4 have degrees 2n+2 and
n+k+1, each coefficient 2. They are distinct exactly when n!=k-1.
All larger terms vanish mod4. Since multiplication by the monic
(t-1)^3 preserves the top degree of (V-1)/2 modulo2 (above its fixed
degree-three constant correction), the index is max(2n+2,n+k+1)-3=d0.
Furthermore 2d0>d. Thus the lower 2-adic Newton polygon has vertices
(0,0),(d0,1),(d,2): every intermediate nonconstant coefficient has
valuation>=1, and those past d0 have valuation>=2. These observations
give the whole lower hull, not just three selected points.

If V factors over Q, Gauss' lemma allows integral primitive factors with
constant 1 after signs. Reducing mod2 forces each factor to reduce to 1
(the only units in F2[t]). Every nonconstant factor therefore has even
leading coefficient. Since V has leading coefficient 4, there can be only
two such factors, each leading coefficient of absolute value 2. Each
reversed factor is Eisenstein at 2 and so irreducible. Its Newton polygon
is a single segment of vertical rise 1. The product polygon theorem then
forces their degrees to be exactly d0 and d-d0. In particular the smaller
degree is k-4 when n>k-1, and n-3 when n<k-1.

This is only a necessary-factor-degree reduction using classical Newton
polygons, not a new full source theorem or eligible outcome. It leaves a
genuine two-factor possibility for every pair in this generic range.
For example k=6,n=7 has vertices (0,0),(13,1),(15,2), yet exact Q
factorization reports irreducible. Thus a demand that the local polygon be
one segment is an invalid route to this source's full rational claim.
Local splitting is compatible with global irreducibility. The diagonal,
n<=3 and k<=4 require their own treatment; the source already supplies
some of these cases, not a full uniform resolution.

The arithmetic evaluation route would additionally need to rule out all
integral factors of these forced degrees, with constant 1, even nonconstant
coefficients and leading coefficient 2, simultaneously for all off-diagonal
k,n. No coefficient, resultant, or value-at-2 argument establishing that
was found. Separating the two Newton slopes alone does not do so. Generic
irreducibility results for sparse polynomials would need an exact bridge
through (H), including its fixed (t-1)^3 cancellation and both free exponents;
none was supplied. No routine adaptation or parameter slice is nominated.

## Runnable diagnostics, objections and falsifiers

checks.py uses binary-pair Stern recursion without enumeration up to the
exponential index. It compares (H), exact Q factorization, the source diagonal
factorization, and Newton vertices for 185 distinct pairs: k2..16,n1..9;
diagonal k3..24; and k17..28,n in {1,2,3}. No factorization disagrees with
the conjecture. All generic polygon assertions pass. This does not certify
irreducibility outside the finite list or any infinite special family.

Strongest mathematical objection: the necessary-degree condition does not
exclude the allowable rational factors, so the main assertion is unproved.
A single exact off-diagonal nonconstant factorization would refute it;
an independently verified factor with another degree would refute the
generic Newton reduction. A revised published statement or earlier exact
resolution would change source eligibility. Finite tests, the prime-index
companion, the diagonal Eisenstein proof, and an empty database solution
field cannot fill the missing step. No claim of current global openness.

Every Python/retrieval/edit helper ran under the unchanged designated guard:
AS512MiB, sampled group RSS512MiB, CPU210s, wall230s, nominal40ms, BLAS1,
PYTHONDONTWRITEBYTECODE=1. Native bounded reads/apply_patch were used.
Guard sampling can miss transients; no stronger peak guarantee is claimed.
Initial oversized tool displays were truncated; conclusions use saved full
bodies and targeted actual reads, not hidden portions of those displays.
No independent eligibility review, Lean, paper, git, shared/count edit,
public action, or browser tab. No completed discovery to advance.
