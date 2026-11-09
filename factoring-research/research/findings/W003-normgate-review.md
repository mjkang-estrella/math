# W003 norm gate — independent review

2026-10-08. **Scoped verdict: PASS the elementary construction and paid finite
Norm2 reference, with a correction to its one-field target limitation;
retain the source and common mixed-target gates as UNRESOLVED.**
No displayed algebraic identity needs correction. The qualifications below
govern reuse: sequential storage is exponential in input length; modular
division requires a unit; the norm certificate supplies no prescribed root;
and neither checked primary source supplies the claimed *possible* fast,
unconditional all-input replacement. **Best supported new COMPLETE classical
factoring improvement: NONE.** No finite test is selected. This is a review
recommendation, not coordinator acceptance. All additional deductions here
remain **UNACCEPTED pending coordinator disposition**.

The sentence denying a rational-row product certificate is too pessimistic:
the construction explicitly gives Q(alpha)=alpha*z^2 with two allowed rows,
Q(T)=(t^2-u^2 T)(v^2-T) and z=v^2-alpha (section 6). This corrects only
the **one-field** limitation; a common mixed target remains unconstructed.
Using the two conjugates of this one polynomial cannot fill that gap.

## 1. Frozen scope and identities

I read all **190 lines** of [the assessed note](W003-normgate.md), the five
required project instructions, the W003 brief and accepted Lens A disposition.
The current instruction overrides stale lifecycle text in STATE. Lens B's
live review was not read, and none of its proposed deductions is used.
There are no earlier reviews or author responses for this parent note.

The [full frozen review brief](W003-normgate-review-evidence/frozen-review-brief.txt)
assembles the exact supplied instructions/background/response status with
byte-preserved copies of the assessed note and disposition. The
[18-input identity ledger](W003-normgate-review-evidence/input-identities.json)
records originals, frozen paths, byte counts and SHA-256 values. Key identities:

- Assessed note: `dae0f013bac05b31ce3b3f6373fcd8e2a2d0e3b0ff35086574a27cea6f26af5f`.
- Lens A disposition: `6658032dbcf973721d9a771071ea44659fe842daa55cac15d54adaeedf2403a5`.
- Original W003 brief: `fc8f5cf42a34b020833832a56994421c183e22a8fd2e951a6cb9c6cee14ab629`.
- Assembled review brief: `85b291d0fc09b4374e9cdaf1638cdcfe8d0ab248ff431f601ce2ab5173952c49`.

Only directly relevant primary PDFs, their existing extraction/access records,
instructions and assessed inputs were copied; no historical evidence tree was
recursively duplicated. The original 16-entry delivery manifest verified on
intake and again at delivery. All 18 frozen snapshots verify. The mutable
STATE original changed after intake; its frozen bytes remain intact and its
new content was not consumed. The other 17 originals still match intake;
this reviewer did not edit any of them. This review's separate
[delivery manifest](W003-normgate-review-delivery.sha256) covers its own report
and supporting files. File operations, source searches and PDF extraction/
rendering were the only execution: no mathematical computation or example
search, implementation, numerical test, Lean action or recursive delegation.

## 2. Existence and fully paid Norm2 reference

Let n=bit_length(N), N>1 odd, gcd(N,15)=1, and R a unit in [1,N-1]. This
subproblem does **not** need R to be a square, although the outer W003 trial
supplies one. Removing factors 3 and 5 and handling primes/perfect powers
belongs to paid preprocessing; the following existence proof also covers
arbitrary odd prime powers and unequal multiplicities directly.

For each p|N, the square set and 5R minus that set each have (p+1)/2 members,
so intersect. A resulting pair (a,b) cannot have both coordinates zero modulo
p. Suppose a is nonzero. Given a lift modulo p^j, replace a by a+c p^j;
the error changes by 2ac p^j modulo p^(j+1). Since 2a is invertible modulo
p, one choice of c removes it. Keep b fixed. If b is nonzero instead, swap
roles. Induction and CRT over the distinct prime-power factors prove existence.
These factors are used only in the proof, never supplied to the program.

The two lists in the note are consequently guaranteed to intersect in their
first coordinate. Store both the residue and its witness; duplicate residues
cause no problem. A fixed tie rule, such as increasing witness, makes the
reference deterministic and independent of any hidden x. Verify the resulting
pair and reduce both coordinates to [0,N-1]. No randomness, restart, failure
probability or factorization oracle is required for this reference on its domain.

Here is a concrete sequential bit-cost realization of the stated envelope.
With schoolbook arithmetic, constructing all 2N records costs O(N n^2) bit
steps. Each fixed-width record takes O(n) bits. Bottom-up merge sorting on a
fixed number of sequential tapes has O(n) passes, each copying and comparing
O(N) records in O(N n) bit steps; tape rewinds have that same bound. Final
merge and verification cost O(N n)+poly(n). Thus **O(N n^2) time and O(N n)
working bits** suffice in this model, including construction and access.
The weaker O(N poly(n)) envelopes in the note are valid. Materializing these
lists already costs Omega(N n) bits/work in this representation: this is not
polynomial space or polynomial time in n. No single-tape simulation bound is
being silently identified with the fixed-multitape bound.

For a replacement, charge its actual T_Norm2, S_Norm2, random-bit law, failed
attempts and restarts. The subsequent transform is poly(n) overhead after a
verified, reduced pair. It cannot be advertised as a poly(n) construction
without paying T_Norm2. Nor is a Norm2 completion a factoring completion.

## 3. Height, irreducibility, positivity and simple reduction

The ranges 4N<=u<5N and 0<=v<N give 16N^2<=s<26N^2. Also 0<t=2R<2N,
and 16R^2<16N^2<32N^2-1<=2s-1. Consequently

    0 < (s-1)^2 < Delta=s^2-16R^2 < s^2.

These are consecutive integer squares. Delta is therefore positive and not
an integer square; an integer which is a rational square is an integer
square. The monic quadratic is irreducible over Q. Its two roots have
positive product and positive sum, and hence are both positive. Coefficients,
Delta and the rational coordinates used below have O(n)-bit descriptions.
No discriminant factorization, integral-basis or class-group computation is
hidden in this degree-two construction.

Modulo N the stronger factorization is

    f(T)=(T-R)(T-4R),    f'(R)=-3R,    s=5R.

Both s and f'(R) are units; the two roots are separated by the unit 3R.
The discarded t=R, s=2R law gives (T-R)^2 and zero derivative. It cannot
justify inversion of that derivative. This is a precise correction to that
discarded variant, not evidence that every repeated-root construction fails.

For clarity, derivative clearing really has an integral-root hypothesis.
If w is integral in this quadratic K, write m=Tr(w), l=Tr(alpha w), both
integers. Direct coordinate expansion gives

    (2alpha-s)w = l-sm+m alpha in Z[alpha].

Thus the unit derivative permits reduction of such w through the localization
of Z[alpha] at 2alpha-s. It does not permit reducing arbitrary field elements
with arbitrary denominators. Neither this identity nor the note constructs
two distinct fields. For two monic polynomials sharing R modulo N their
resultant is 0 modulo N, so the warning against inverting it is correct.

## 4. Exact square test and the two root branches

If w in K satisfies w^2=alpha, then w is integral (also directly a root of
X^4-sX^2+t^2). Norm(w)^2=t^2, so Norm(w)=±t, and

    Tr(w)^2=s+2Norm(w) in {s+2t,s-2t}.

Conversely, (alpha±t)^2=(s±2t)alpha. Since s>2t>0, either positive integer
square s±2t=k^2 supplies w=(alpha±t)/k, and k is nonzero. This proves both
directions of the asserted criterion, including nonintegral-coordinate roots
in a nonmaximal presentation of K. Exact integer-square testing, inverses
and output verification have polynomial bit cost here.

With t=2R, s-4R is R modulo N and s+4R is 9R modulo N. Hence the two
outputs k and k*3^(-1) modulo N are correct. Their k denominators, if used
for the field formulas, are automatically units modulo N since k^2 is a
unit. The continuing branch has alpha nonsquare and [L:K]=2, as required
for the two-term relative norm formula. No positive frequency of either
integer-square event follows from the criterion.

## 5. Norm certificate and exact localization boundary

Expanding the numerators cancels the cross terms and gives

    (u alpha+v t)^2+(v alpha-u t)^2
       =(u^2+v^2)(alpha^2+t^2)=s^2 alpha.

This proves A^2+B^2=alpha. Since u,t,s are positive, v=0 gives B=-ut/s!=0;
if v!=0, B=0 would imply alpha=ut/v rational. Thus B is nonzero in K.
In the genuine extension L/K, beta maps to -beta, so

    Norm((A+beta)/B)=(A^2-alpha)/B^2=-1,
    Norm(beta*(A+beta)/B)=(-alpha)(-1)=alpha.

These field identities remove the two advertised necessary barriers:
negative real conjugates and exclusion of alpha from Norm(L^*). They do not
by themselves characterize the subgroup generated by rational-pair rows.
A is not rational because u!=0, but this does not rule out a different
certificate using rational pairs. Section 6 provides one for this same law.

Let C=Z[alpha,1/s]. Because s mod N=5R is a unit, evaluation alpha->R
defines C->Z/NZ and gives the displayed Abar,Bbar. In particular

    ((u+2v)^2+(v-2u)^2)/25=s/5=R modulo N.

Use modular inverses for these divisions. For d=gcd(Bbar,N), 1<d<N yields
a verified factor; d=N means Bbar=0 and Abar is a verified root. Only d=1
allows extending the map to C[1/B]. Nonzero B in a field does not imply
unit Bbar in a residue ring. All these gcd checks are polynomial overhead.

Even when Bbar is a unit, reducing the norm identity merely supplies an
identity in (Z/NZ)[Z]/(Z^2-R). To send beta to a residue y would require
already knowing y^2=R. This is the elementary obstruction to treating the
norm certificate as a root-selection algorithm. Norm2 and the certificate
exist even for nonsquare unit R; a purported implication to a root for all
such inputs is therefore impossible. On W003's square inputs this observation
proves neither impossibility nor a useful completion probability.

## 6. Material completion and a further elementary obstruction

The defining equation and s=u^2+v^2 immediately give

    t^2-u^2 alpha = alpha*(v^2-alpha),
    (t^2-u^2 alpha)(v^2-alpha)=alpha*(v^2-alpha)^2.

Thus rows (a,b)=(t,u),(v,1) realize the one-field target, with explicit
root z=v^2-alpha. Irreducibility makes z and both rows nonzero, including
v=0. The coefficients and z have O(n)-bit coordinates; forming and checking
this witness takes poly(n) work **after the paid Norm2 construction**.
Equivalently Norm((t+u beta)/(v+beta))=alpha. This is an explicit product
of two rational-pair rows times a square, correcting the note's sentence
claiming that its law does not show such a product. It does not make alpha
a square: Q(alpha) has the nonsquare class [alpha] on the continuing branch.

For reduction set g=v^2-R modulo N. The two row images are R*g and g,
so Q(R)=R*g^2, and zbar=g. If gcd(g,N) is proper, it yields a factor.
If g=0 modulo N, v is already a root of R. If g is a unit, the displayed
identity is merely a valid twisted relation; no root of R follows. These
checks cost poly(n), but no frequency or complete factoring bound follows.
A second field making this same Q an ordinary square is still missing.
Nor does forming these rows establish useful norm sizes or smoothness:
Norm(z)=t^2-u^2 v^2 and Norm(t^2-u^2 alpha)=t^2 Norm(z), giving only
O(N^4) and O(N^6) magnitude upper bounds. They are cheap to describe and
evaluate, but no smooth-relation supply theorem accompanies them.

Taking the two conjugates of this one polynomial cannot realize the mixed
target on the continuing branch. Indeed, let tau(alpha)=alpha'=s-alpha.
For Q in Q[T], Q(alpha)=alpha*z^2 implies
Q(alpha')=alpha'*tau(z)^2. If Q(alpha') were also a nonzero square, alpha'
and hence alpha would be squares in K, contradicting the continuing test.
The opposite orientation is equally impossible. This excludes only this
conjugate reuse; it does not exclude two independently selected laws/fields.

Another exact consequence is

    [alpha]=[s+2t]=[s-2t] in K^*/K^{*2},

because (alpha±t)^2=(s±2t)alpha. Thus the one-field target is also a rational
class, represented by s+4R, reducing to 9R. In particular a separating
character excluding [alpha] from the subgroup of *all* rational-pair rows
cannot exist: the explicit two-row witness disproves that exclusion.
No common mixed-target theorem follows from either one-field description.

## 7. Hidden-root boundary and cost/probability scope

Every operation in the note can depend only on N,R and fresh internal
randomness; deterministic sorting tie rules and the direct square tests
respect that restriction. Factor outputs must be verified separately. For
N=product p_i^e_i odd and r distinct primes, a unit square R has exactly
2^r roots, including unequal repeated exponents: two local signs at each
prime power, then CRT. Conditional on R, the retained uniform outer x is
uniform on that fiber. Any internal transcript/stopping event determined by
N,R and independent randomness preserves that uniformity.

Consequently, conditional on an actual verified inner root y, gcd(x-y,N)
is proper with probability 1-2/2^r. Only x=y and x=-y give respectively N
and 1. For r=1 the probability is zero; prime/power preprocessing matters.
Raw words x>=N and x=0 remain charged failures, and nonunit words need their
earlier gcd branch. This conditional law does not bound the probability that
the inner routine ever returns a root. A finite Norm2 solver alone supplies
no such root event, no mixed-target search and no restart/completion theorem.
No NFS relation-supply result, smoothness model or complete factoring bound
has been established or transferred by this note.

## 8. Independent primary-source scope

**Shallit.** I checked sections I–IV and VI, the later explanatory sections
and bibliography in the archived [author report](https://cs.uwaterloo.ca/~shallit/Papers/pols.pdf);
the source's numerical illustration was only read, never executed. Its norm
composition and coefficient descent are explicit. Page 9's speed estimate
assumes a least-prime conjecture; page 7 separates an unproved fast sequential
prime search for sums of two squares from a different algorithm referenced
to [Sha]. The latter theorem/algorithm is not given in this report and was
not retrieved here. For Norm2 the specialization is D=-1, k=5R, which goes
directly to that sum-of-two-squares base case, not the generic recursive
prime-search estimate. The note's refusal to import an unconditional fast
routine is therefore appropriate; the citation is not evidence that none
exists. Norm inverses and role interchange require units. Section VI's
factor-and-CRT shorthand alone does not settle noncoprime split recombination
for arbitrary repeated prime powers; the reviewed finite reference avoids it.

**BGH.** I checked section 5 through Lemma 5.2 and Appendix C/C.1 in the
archived [author PDF](https://theory.stanford.edu/~dabo/papers/bgh.pdf).
Section 5 assumes unequal unit coefficients and N odd. Lemma 5.2 charges
generation of two suitable primes; it does not bound a sequential progression
scan by poly(log N). Appendix C starts with coprime integer lifts, specified
parities and verified mutual modular square roots; its lattice reduction
does not construct those inputs for free. C.1 describes a heuristic screening
method with exact square-root checks, not an all-input running-time proof.

To match Norm2's coefficients, put c=(5R)^(-1) modulo N and solve
c X^2+4c Y^2=1, then take (u_0,v_0)=(X,2Y) modulo N. The coefficients
are distinct units since 2 and 3 are units. Directly using c,c would ignore
section 5's stated unequal-coefficient assumption. Reducing an integer conic
point requires a unit z; merely z!=0 is insufficient. Likewise the product
formula's denominator must be a unit. Proper gcds can produce factors, but
full gcds and retries need explicit accounting. The checked text does not
provide that complete Norm2 contract. Its attribution of a GRH qualification
to Pollard–Schnorr is verified as an attribution, not an independent review of
the latter article's precise hypothesis. That full article was not obtained.

**AEM.** Exactly six focused search queries, no extra direct opens, were used;
see the [search ledger](W003-normgate-review-evidence/aem-search-ledger.json).
No full AEM manuscript or pertinent proof was obtained. Previously failed
endpoints were not retried. The abstract/metadata at
[DOI 10.1090/S0025-5718-1987-0866095-8](https://doi.org/10.1090/S0025-5718-1987-0866095-8)
remain leads, not verification of the input domain, success law, randomness
or all-input expected polynomial cost. This unresolved source gate does not
invalidate the elementary construction and is not a lower bound.

The frozen primary PDFs have SHA-256 `91f9ab651a8697c05505fb32a092f78340ed182e285e4760dc0ecdb40400ba67`
(Shallit) and `3352454da2736e823ca5433bfff3da35ae4b98edfc0094489dd6c010b26bd7e6`
(BGH). Independent pdftotext extractions are archived. I visually checked
new renders of Shallit p.9 and BGH pp.9–10. Shallit's legacy text encoding
loses glyphs and its renderer emitted Type-3 bounding-box warnings; the PDF
and inspected image govern the source claim. These are independently read
existing archives, not newly downloaded versions. No ECCC or Lens B theorem
was used to strengthen their scope.

## 9. Coordinator disposition requested

Accept the reviewed elementary identities, all-prime-power Norm2 existence,
the explicit paid reference and the localized/root-fiber qualifications;
independently disposition the new one-field completion and conjugate-use
obstruction in section 6. Keep fast Norm2, two-field selection, common
mixed-target attainment, norm supply, useful probability and complete
factoring cost open. Preserve the original
note and its source/delivery ledger unchanged.

One warranted next proof question is whether the explicit Q from section 6
can be an ordinary square in an independently selected second field of this
law, with unit reduction, under an N,R-only selection rule with proved cost
and completion probability. A square-class test or a bare existence claim
cannot substitute for that selection rule. The conjugate reuse is closed.
No experiment, larger row cap, implementation or Lean work is selected.
