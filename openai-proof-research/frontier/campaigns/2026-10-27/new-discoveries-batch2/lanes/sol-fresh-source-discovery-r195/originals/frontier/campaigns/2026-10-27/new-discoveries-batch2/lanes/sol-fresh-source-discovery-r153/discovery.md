# Fresh source, unresolved least-prime bound

Zero nominees. This report does not claim a full ordinary source resolution.
The root's acceptance and investment gates are untouched.

## Literal source and chronology

Zhi-Wei Sun, OEIS A224416, created April 6, 2013, current COMMENTS part (i):
let C_k=binom(2k,k)/(k+1), and for each integer n>=1 let
Q_n(x)=sum(k=0..n) C_k x^(n-k). The sequence a(n) is the least prime p
such that Q_n mod p is irreducible in F_p[x]. The target is the **full
universal assertion a(n)<=n²+n+5**, including existence. Q_n is monic,
so there is no degree-drop convention to fix. Its reciprocal P_n(x)=
sum C_k x^k has constant coefficient 1 over Q; reciprocal reversal preserves
its rational splitting field and rational irreducibility. At a prime dividing
C_n, however, P_n drops degree while Q_n does not. All checks therefore use
the source's literal monic Q_n. The bound is not replaced by an asymptotic,
density assertion, single degree, helper, or Galois-group reformulation.

Primary bytes are sources/oeis.html. Seki's actual latest arXiv metadata
advertises only 2609.10526v1, September 9, 2026. The actual PDF/HTML was read:
Introduction pp1–2, root bounds, forced symmetry/resultant proof pp3–6,
especially Section4.1 equations(4.1)–(4.3). Theorem1.1 proves irreducibility
over Q for every n>=1; Introduction explicitly leaves the stronger Galois
question open. The author's current bibliography lists this work as a
preprint; no separate journal version was established. This is a bounded
bibliographic observation, not proof that no publication exists anywhere.

CURRENT actual source-facing proof lead followed before sustained mathematics:
Khai-Hoan Nguyen-Dang, *Galois groups of Taylor polynomials: prescriptions and
arithmetic families*, Valency W_mep2xkcu_v2, displayed publication October27,
2026. Actual full HTML retrieved, not an abstract-only inference. Theorem E
asserts Gal_Q(P_n)=S_n for all n>=1. Read the actual Catalan section, equations
(44)–(50), local cycles and discriminant proof, Lemma5.3 and its proof,
smaller-block exclusion, two-block trace exclusion, and all-degree group
assembly including Tables3–4. The proof uses Seki irreducibility, tame
inertia cycles, explicit primes, primitivity, and an odd permutation.
In the two-block case it forces AB=-n(n+1), A+B=-1, contradicting transitivity.
This is a public full-scope proof manuscript for the Galois question observed
before this investigation (October30 UTC / October29 Los Angeles). Its
supporting cited prime-estimate bodies and external verifier were not all
independently replayed; no independent global correctness certificate is
claimed. It suffices to retire the Galois question from fresh nomination.
Introduction and Further questions explicitly retain Sun's least-prime bound.
The exact object bridge is reciprocal reversal over Q; it does not assert
any bounded-prime consequence. No public proof of the bounded-prime claim
was identified in the bodies actually read. No worldwide absence claim.

## History and fixed registries

Before source downloads, searched IDs, exact titles, authors and claim aliases
across complete retained original SUMMARY/discovery/PROOF/review/DECISION
bodies. history-query-*.json records each pattern and full-body hit list;
history-delta.json references the qualified r150/r147 baseline by hash and
stores only changed/new original roles and excluded echo paths. The r149
exact-history context was reopened. Original r111–r113 science is retained
explicitly, including r111/PROOF.md. Generated release/extraction/context/
private/core echoes are excluded by role, not by a global size cutoff.
Some retained source-role aliases contain identical bytes; a match is not
automatically a distinct original investigation. No whole-workspace semantic
completeness is claimed. The exact Catalan/Seki/A224416/Nguyen-Dang query
has no retained-body match. This is evidence of project freshness within
that scope, not literature novelty.

Initial Stern lead matched r39 and r63. Both complete original discovery
bodies were reopened: r39 already attempts the full half-plane question;
r63 explicitly retires it. No Stern downloads or new mathematics followed.
The root r150 disposition was read; McDermott conditional stability remains
unresolved and was not revisited. r151 analysis and r152 finite remain separate.

registry-screen.json screens retained immutable Omega
490f6bccbf445ab8e111a16b0b8670a5dd7c9a9c and OpenAI
7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a path indexes and prior retained deltas.
No HEAD chase. Both aa026->a19a and a19a->490f compare lists are capped at300;
neither narrow retained walks nor lexical nonmatches clear their omitted
paths. Semantic matching across all registry bodies is not complete.
Actual plausible certificate CatalanConjectureSevenRefutation.md was fetched
at fixed Omega and read in full: Wang–Xin1811.00248v2 Hankel powers, a printed
clause correction, **not** Catalan truncation irreducibility or a least-prime
bound. Other returned names concern parity, Hankel determinants, combinatorics
or Catalan's constant. Names alone do not prove non-subsumption. No blanket
registry or classical-prior clearance is asserted.

## Sustained route 1: transport the actual local argument

Let p be odd and k=(p-1)/2. Coefficient comparison, as in Seki Section4.1,
gives in F_p[x]

    2 Q_k(x)=x^(k+1)-(x-4)^(k+1),
    Q_k(x)[x^(k+1)+(x-4)^(k+1)]=2(x^p+x-4).

Thus Q_k is squarefree and every root gamma satisfies gamma^p=4-gamma,
hence gamma^(p²)=gamma. Every irreducible factor has degree at most2.
This is an elementary consequence of the already-public local identity,
recorded as a strategy obstruction, uncredited.

For n+1<p<=2n, factorial valuations give C_j nonzero mod p for j<=k and
zero mod p for k<j<=n. Therefore

    Q_n mod p=x^(n-k) Q_k mod p.

Here 0<n-k<n, so these primes are all unusable as irreducible-reduction
witnesses. The same primes are useful for Galois inertia cycles precisely
because the reduction has a zero-root component; they cannot simply be
reused as primes certifying Sun's bound. If p=2n+1 is prime and n>=3,
Q_n itself has all factor degrees <=2, so that boundary prime is also unusable.
This closes the proposed local transport route rather than the source question.
It does not rule out primes <=n+1, or primes >2n+1 up to n²+n+5, or other methods.

The Frobenius identity does not extend to arbitrary p>2n+1: the truncated
binomial identity singles out k=(p-1)/2. Treating a general truncation as
that special Q_k changes its degree and loses the source polynomial. I found
no preserved identity controlling the full range of candidate primes.

## Sustained route 2: quantitative versus qualitative Galois information

The public S_n conclusion permits an n-cycle Frobenius class; its usual
qualitative prime-existence consequence supplies no explicit prime below
n²+n+5. No effective inequality with this exact bound occurs in the read
proof bodies. Repeating their primitivity argument would resolve an already
public question and still leave the quantitative step untouched.

There cannot be a bound depending only on degree and the assertion G=S_n
valid for arbitrary integer polynomials. Concrete diagnostic: x²-18481 is
irreducible over Q (135²<18481<136²), with Galois group S_2. Since
18481=1+8*(2*3*5*7*11), its reduction is reducible at every prime <=11,
including characteristic2. Thus the degree-two threshold 2²+2+5=11 fails
for this generic S_2 polynomial. This is **not a counterexample to Sun**:
the Catalan Q_2 is x²+x+2, whose least prime is3. It proves only that the
source's coefficient structure must enter a bounded-prime proof.
No classical subsumption exclusion of Sun's conjecture is claimed.

## Exact diagnostics, objection and gap

Runnable: bash run-checks.sh. A custom exact finite-field Rabin criterion
uses x^(p^n)=x mod Q_n and gcd checks at n/q for prime q|n. It tests primes
in increasing order and reproduces the OEIS least-prime entries for n=1..40.
SymPy independently checks all40 successful reductions and all preceding
primes for n<=12 using the original integer coefficients. Local factorization
identities are checked for n<=100, and Frobenius-square identities for odd
primes<=199. These finite diagnostics do not prove a universal source statement.

An initial independent-check implementation accidentally reused coefficients
already reduced modulo the witness prime when checking smaller primes; it
failed an assertion. checks.log preserves the failure. The correction rebuilds
each reduction from the original integer Catalan coefficients. Corrected and
final runs pass; no failed run is represented as successful. PDF conversion
emitted a font warning but produced readable text. One author-page request
failed on unescaped Unicode; a percent-encoded URL succeeded. Web-reader
opening of Valency v1 returned an access error; the actual v2 public HTTP
retrieval succeeded. No403/429/challenge or bypass occurred.

Strongest objection: every completed deduction above is a known-identity
consequence, strategy obstruction, or finite diagnostic. There is no new
full-scope arithmetic result. Strongest source falsifier: one integer n with
exact reducibility certificates for Q_n modulo **every** prime p<=n²+n+5.
It must use the original Q_n and include all primes, not just the unusable
local interval. A positive resolution instead needs an all-n witness-prime
construction or a quantitative existence theorem at exactly that threshold.
This is the precise remaining mathematical gap. Source, companion, and
registry access limits cannot be traded for a proof. No Lean or manuscript
investment is requested; no PROOF.md is appropriate.
