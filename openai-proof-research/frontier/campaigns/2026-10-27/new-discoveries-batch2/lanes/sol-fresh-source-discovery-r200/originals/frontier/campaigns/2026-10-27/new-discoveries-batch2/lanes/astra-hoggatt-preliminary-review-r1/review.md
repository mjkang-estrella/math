# Independent preliminary review: q-Hoggatt strict interlacing

Reviewed 2026-10-28 UTC (2026-10-27 America/Los_Angeles). Assigned lane:
`astra-hoggatt-preliminary-review-r1`. Work was solo, with no children,
git operations, shared edits, posting, accounts, or external messages.
This report makes no acceptance or counting decision.

The reviewed object is `root-hoggatt-r1`, user-supplied freeze label
`0aadc15c28`. All 64 entries of `preliminary-review-hashes.json` matched on
initial verification. The manifest SHA256 is
`ae01bcd0e0e959016bf5d5d2eef9bc18def8a141338c06130050280680093b25`.
The git label itself was not independently verified, because git operations
were prohibited. See the initial/final hash reports for byte-level identity.

## Verdict and investment recommendation

The written mathematics is sound on the stated classical dependencies.
I found no counterexample, orientation error, missing residue sign, indexing
failure, or normalization gap. It proves the claimed Q>1, all-m>=2 theorem
and, with the known Q=1 result, the literal arXiv Conjecture 4.1.

The strongest adverse finding is a precise classical reduction: the entire
q-Markov lemma is a direct specialization of Lamprecht Theorem 30, using
the symbol `t D_Q R_d(1/Q;t)`. The strict separation invariant is an immediate
application of Garloff-Wagner 4(b,c) to a polynomial and its dilation. After
those substitutions, the proof is FZZ's existing m-induction and a routine
Gaussian coefficient identity. Full details, including every strictness
hypothesis, are in [classical-subsumption.md](classical-subsumption.md).

Under the campaign's explicit exclusion of routine adaptations/corollaries,
I recommend **no substantive-discovery credit and no large formalization
investment for counting purposes**. This is a threshold judgment supported
by a full bridge, not a claim that I located an earlier printed solution of
the Hoggatt conjecture. No such explicit prior solution was located in the
bounded investigation. The proof could still be useful as a short conjecture
resolution in a setting that credits such applications.

| Gate | Independent finding |
|---|---|
| SOURCE | PASS for the exact latest available arXiv target; full journal-body comparison remains incomplete. |
| MATH | PASS for the complete ordinary proof, conditional on the correctly stated established GW/MacMahon/q-binomial inputs. |
| NOVELTY | No earlier explicit full endpoint found; absolute priority unproved. Exact classical reduction of the claimed new analytic mechanism established. |
| SUBSTANTIVE | NOT CLEARED; recommend exclusion under the campaign's routine-adaptation rule. |
| FORMAL | INCOMPLETE. Only three elementary helpers replayed. No full FORMAL PASS. |

There is no manuscript gate in this preliminary review. Root alone decides
whether the eligibility judgment warrants stopping, holding, or further work.

## Source target and exact normalization

Fang-Zhang-Zhao, *Analytic properties arising from the Baxter numbers*,
[arXiv:2505.05873v1](https://arxiv.org/html/2505.05873v1), defines

\[
 H_n^{[m]}(Q,t)=\sum_{k+l=n-1}Q^{m\binom{k+1}{2}}
           \sum_{\pi\in PP(k,l,m)}Q^{|\pi|}\,t^k.
\]

Conjecture 4.1 is for every positive INTEGER Q and m=2,3; it asks that the
sequence indexed by n>=1 be Sturm. Theorem 1.2 already establishes Q=1
for all m>=2. The current arXiv abstract/history displayed v1 only. This
review does not silently replace the integer conjecture by a different
one: the all-real Q>1 result is an extension, with Q=1 a credited input.

The source has a published version: JMAA 561(1), article 130615, 1 September
2026, DOI [10.1016/j.jmaa.2026.130615](https://doi.org/10.1016/j.jmaa.2026.130615).
Indexed publisher introduction and conclusion snippets were read. The
conclusion still introduces three conjectures and discusses the same
q-extension, but its displayed text is truncated before the full first
conjecture. Direct article access returned 403. Thus the exact journal
Conjecture 4.1 body was NOT independently compared; the frozen discovery
file's stronger wording about the published conclusion should be qualified.
The complete arXiv definition/conjecture/proof were read, not inferred from
an abstract or a registry label.

Set N=k+l+m-1=n+m-2. With Q-factorials A_j=[j]_Q! and A_0=1, the proposed
Gaussian quotient is

\[
 \frac{\prod_{j=0}^{m-1}{N\brack k+j}_Q}
      {\prod_{j=1}^{m-1}{N\brack j}_Q}
 =\prod_{j=0}^{m-1}\frac{A_j A_{N-j}}{A_{k+j} A_{N-k-j}}
 =\prod_{j=0}^{m-1}\frac{A_j A_{k+l+j}}{A_{k+j} A_{l+j}}
 =\prod_{j=1}^{m}\prod_{i=1}^{k}
       \frac{[l+i+j-1]_Q}{[i+j-1]_Q}.
\]

In the middle equality, reindex the N-dependent product j -> m-1-j.
The last expression is MacMahon's product for the box, after interchanging
box dimensions if necessary. There is no extra Q-power. Since every
positive-index Q-integer is positive for real Q>1, all denominators are
strictly positive, including the boundary n=1. It follows literally that

\[
 H_n^{[m]}(Q,t)=\frac{F[n+m-2,m](t)}
                    {\prod_{j=1}^{m-1}{n+m-2\brack j}_Q}.
\]

Thus zeros, multiplicities, and directed interlacing are unchanged. The
source enumerates actual boxed plane partitions; a future Lean theorem
only about F would not yet be the source endpoint.

## Garloff-Wagner conditions and orientation

The original Theorem 4's indexed p.800 and FZZ's full Theorem 2.1 agree:
inputs have positive leading coefficients and only nonpositive zeros;
nonzero ordinary Hadamard products have simple nonzero zeros; the directed
order is preserved; common nonzero zeros are excluded unless both pairs
are proportional, or both upper polynomials are positive constants times
t times their lower polynomials. The simultaneous nature of the two
exceptions matters and is stated correctly in the candidate.

For successive G's, both factor pairs have adjacent degrees. Proportionality
is impossible; positive constant terms forbid the simultaneous t-multiple
exception. The product degrees differ by one and products have positive
constant terms. Hence weak interlacing becomes strict negative interlacing.

For separation, with roots r_1<...<r_d<0, weak separation gives

\[
 r_1<r_1/Q\le r_2<r_2/Q\le\cdots\le r_d<r_d/Q.
\]

So P(t) alternates LEFT of P(Qt), as required, not the reverse. Pair this
with R preceq R. For nonconstant P the first pair cannot be proportional:
the constant terms force a proportionality constant of 1 while the leading
terms would force Q^d=1. Nonzero constants exclude t-multiples. Consequently
the output roots s satisfy s_i<s_i/Q<s_(i+1), which is precisely strict
Q-separation. Products of unequal degree pose no problem; their common
degree is the minimum input degree. All displayed input coefficients are
positive, so there are no leading cancellations.

The original PDF full proof could not be downloaded (timeout). Reliance
on this established theorem is transparent, supported by the original
indexed statement and a complete primary restatement. It is not a Lean axiom.

## Independent rederivation of q-Rolle and q-Markov

For squarefree f of degree d with leading coefficient a>0 and strict
Q-separated negative roots r_1<...<r_d, put a_i=r_i/Q, b_i=r_(i+1).
Both a_i and Q b_i lie strictly in (r_i,r_(i+1)). The denominator
(Q-1)t is negative at both endpoints. Thus

\[
 \operatorname{sign}D_Qf(a_i)=(-1)^{d-i},\qquad
 \operatorname{sign}D_Qf(b_i)=(-1)^{d-i+1}.
\]

The signs are nonzero and opposite. There are d-1 disjoint brackets, and
D_Qf has degree exactly d-1 with leading coefficient [d]_Q a>0. Therefore
each bracket contains exactly one root, all are simple, and there are no
other roots, real or complex. With these roots y_i,
y_i<r_(i+1) gives y_i/Q<r_(i+1)/Q<y_(i+1), proving strict separation.
For d=1 there are no brackets and D_Qf is a positive constant.

For a degree d-1, positive-leading g weakly interlacing f,

\[
 \frac{g(t)}{f(t)}=\sum_j\frac{c_j}{t-r_j},\qquad
 c_j=\frac{g(r_j)}{f'(r_j)}\ge0,\qquad
 \sum_j c_j=\frac{\operatorname{lc}(g)}{\operatorname{lc}(f)}>0.
\]

This follows by Lagrange interpolation (so no unmentioned polynomial part
or limit is needed). At a shared root the residue is zero; otherwise g(r_j)
and f'(r_j) both have sign (-1)^(d-j). The leading coefficient comparison
gives the sum. Weak interlacing, even with repeated roots of g, suffices.

At a root y_i of D_Qf, both Qy_i and y_i lie strictly in the SAME gap
(r_i,r_(i+1)), and f(Qy_i)=f(y_i)!=0. Subtracting the two partial fractions
and dividing by (Q-1)y_i gives exactly

\[
 D_Qg(y_i)=-f(y_i)\sum_j\frac{c_j}{(Qy_i-r_j)(y_i-r_j)}.
\]

Each denominator product is positive, and at least one c_j is positive.
The resulting signs are (-1)^(d-i+1), in particular positive at y_(d-1).
The d-2 intervening sign changes exhaust the degree of D_Qg. They prove
simple negative roots and strict interlacing with D_Qf. For d=2 this is
exactly a positive constant versus a negative-rooted linear polynomial;
there is no nonexistent root index to consider.

This direct proof is valid, but does not establish novelty. The separate
subsumption note derives this same full lemma from Lamprecht Theorem 30.

## Coefficients, induction, and small boundaries

The coefficient of t^k in D_QG[N,m], for 0<=k<=N-m, is

\[
 [k+1]_Q Q^{m(k+1)(k+2)/2}{N\brack k+1}_Q
       \prod_{j=0}^{m-2}{N-1\brack k+1+j}_Q.
\]

The Gaussian step replaces its first and third factors by
[N]_Q {N-1 choose k}_Q. Combining that factor with the product gives
exactly the m factors for F[N-1,m]. The power is
m k(k+1)/2+mk+m, proving

\[
 D_QG[N,m](t)=[N]_Q Q^m F[N-1,m](Q^m t).
\]

At N=m the degree on both sides is zero. Above the displayed range every
coefficient is zero. There is no reliance on a negative-index Gaussian or
an incorrectly extended finite sum.

The base F[N,1]=prod_(j=1)^N(1+Q^j t) has the ordered roots
-Q^-1,...,-Q^-N. They meet the weak separation condition at equality;
successive products weakly interlace by adding the rightmost root.
For N>=m, F[N-1,m-1] has degree N-m+1>=1, so both G factors are nonconstant.
The separation and interlacing consequences of GW therefore apply.
Apply q-Markov with f=G[N+1,m] and g=G[N,m]; its larger degree is always
at least 2. The identity gives precisely F[N-1,m] versus F[N,m] with the
same positive argument scaling. These cover every consecutive pair starting
with N=m. Individual q-Rolle gives the individual strict root conclusions.

F[m-1,m] is a positive constant. F[m,m] is a positive constant times
1+Q^m t, so the first source polynomials are H_1=1 and H_2=1+Q^m t,
and the first nonempty root is -Q^-m. All n>=1 and m>=2 are covered.

## Independent checks and formal scope

The assigned absolute Lean 4.34.1 binary replayed the unmodified frozen
`formal/ResidueBridge.lean` directly. Exit status was 0; the only warning
was a tactic-style linter. Each of the three declarations reports exactly
`propext`, `Classical.choice`, `Quot.sound`. See `bridge-replay.json` and
`bridge-replay.log`. The frozen replay.py was NOT executed, because it
writes its own lane. No imported theorem of Hoggatt, GW, MacMahon, or
polynomial interlacing is established by those three helper declarations.

The independently written `independent_checks.py` uses rational arithmetic
and a Pascal recurrence for Gaussian coefficients. It checked 120 coefficient
identities, 108 literal small plane-partition enumerations, 32 Lamprecht-symbol
identities, and 20 first-linear cases, including Q=101/100. These are finite
corroboration only, not the proof and not a novelty argument.

The formal obligations in BRIDGES.md are substantial and correctly identified.
In particular, a checked GW/stability theorem, root/order and q-difference
infrastructure, and a literal finite plane-partition MacMahon bridge remain.
The Q=1 contribution must also be checked for a full source-conjecture
certificate. A bounded search of the pinned mathlib analysis, combinatorics,
and polynomial trees found no ready GW/interlacing/MacMahon theorem matching
this need. This is not a proof of absence throughout all possible libraries.
Existing external real-rootedness developments cannot be treated as already
ported or already replayed under the pinned dependencies.

Given the precise routine-adaptation objection, the cost of a full literal
certificate is not justified merely to turn these three helpers into an
accepted discovery. If root overrides that eligibility judgment, formalize
the direct residue proof rather than all of Lamprecht's stronger theory,
but still prove every GW and plane-partition dependency. There is no honest
shortcut through a new axiom or an endpoint that assumes the missing facts.

## Bounded literature conclusion

See [source-notes.md](source-notes.md) and `provenance.json` for exact bodies,
versions, access limitations, and evidence locations. The nearby 2026 works
prove coefficient log-concavity, polynomial log-convexity, or other generating
function positivity; those conclusions are not strict row-root interlacing.
The public RealRooted comment read in full treats the Q=1 Hoggatt rows via
ordinary reciprocal-Pochhammer multiplier sequences. The live MathDB record
had no solutions, but that is not evidence of novelty. Its additional source
matches were checked and do not state this Hoggatt conjecture.

The report therefore separates two facts: no earlier explicit full endpoint
was found, and the candidate's analytic contribution reduces completely to
old theorems plus FZZ's already published induction. The latter is the basis
for the adverse substantive recommendation. It is not a fabricated claim
of known publication priority and not a rejection just because the final
proof is short.
