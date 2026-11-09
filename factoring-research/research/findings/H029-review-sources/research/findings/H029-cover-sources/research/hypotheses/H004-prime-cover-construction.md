# H004 construction attempt — powers-of-two shifted progressions

Status: **rejected as an all-parameter cover; no asymptotic impossibility claim**.
Date: 2026-10-08 UTC. The preregistered version is frozen in the evidence below.
Verified factoring improvement: **NONE**. This is an exclusive child report;
H004.md, shared harness, Lean, and STATE are outside its write scope.

## Family and question

For integer m >= 2 put R=m^3, L=m^2, and B=2^e. The nominal rule is e=2m;
the single family investigated allows m <= e <= 4m. Define

S={B+jm+1 : 1 <= j <= m}, T={1,...,m}.

Then S-T={B+1,...,B+m^2}, exactly, with no zero differences. The question is
whether this explicit, cheaply generated shifted progression covers every
prime <= R. For general R take m=ceil(cuberoot(R)); no input factor is used.
The nominal rule has |S|=|T|=m and height B+m^2+1 of exactly 2m+1 bits.
These are the desired cube-root height/cardinality exponents, not a coverage
theorem. A binary exponent description does not pre-factor the differences.

## Preregistration (freeze before any search; retain verbatim)

Recorded at 2026-10-08 06:31 UTC. No finite coverage computation has run.

- Primary parameters: m in [2,3,4,5,6,8,12,16,24,32,48,64,96,128], R=m^3,
  L=m^2, e=2m, step c=1. No RNG and no hidden factors.
- Predeclared bounded revision within the same family: for
  m in [2,3,4,5,6,8,12,16,24,32], test every integer e in [m,4m], inclusive.
  Keep all results. Rank by covered-prime count, breaking ties toward smaller e.
  Do not extend either grid after looking at results.
- Generate primes by a fresh standard-library sieve through 128^3. Charge
  sieve time, memory, modular powers, scanning, validation and evidence writes.
  Never form a primorial or consult a factor database.
- Exact coverage criterion for p>L: r=(-pow(2,e,p)) mod p is in [1,L]. Every
  prime p<=L is covered by any L consecutive integers. Store the complete list
  of missed primes, covered counts, 10 largest misses, smallest miss, and all
  complete-cover cases. Count modular tests. Do not infer equidistribution.
- Rejection: a single missed prime rejects that (m,e) as a complete cover.
  One failing nominal m rejects the nominal rule as an all-parameter cover.
  No exponent succeeding at a scanned m rejects the whole bounded exponent
  subfamily at that m. Finite failure alone does NOT prove eventual or
  infinite-subsequence impossibility; finite success does NOT prove a family.
- Independently check nominal m<=16 using explicit positive differences and
  trial remainders for every prime. For each nominal m, use the two largest
  misses in ((m-1)^3,m^3], if present, to construct a nonsquare semiprime whose
  own rounded cube-root parameter is m. Verify gcd(product mod N,N)=1 directly.
  This is a coverage counterexample, not a factoring performance benchmark.
- Retain nominal large-prime leaf collisions (two primes >L hitting one index)
  when present. Verify the product divides that difference. This illustrates
  the leaf obligation without asserting computational hardness.
- Capped script: standard-library Python, internal wall deadline 50 seconds,
  external hard timeout 60 seconds. On internal timeout retain completed work
  and mark remaining cases unstarted. No rerun with larger limits. No harness
  or Lean changes. Evidence names must begin H004-cover- in this directory.
- Save a frozen copy of this preregistration and the script/report SHA-256
  values in evidence before results are appended. Record runtime and peak
  process RSS; RSS is descriptive, not a certified bit-machine memory model.

## Result

The nominal rule failed all 14 registered parameters. Exhaustive tuning within
the registered exponent ranges found complete prime covers only at m=2, with
e=2,5,8. All 339 exponents tested at the other nine revision parameters failed.
At m=128 the nominal progression has two sets of 128 elements, maximum element
of 257 bits, and 16,384 differences, but misses 146,904 of 155,611 required
primes. Its largest missed prime is 2,097,143.

There are three distinct outcomes: a cheap uniform formula with the desired
sizes but invalid coverage; exact finite counterexamples including nonsquare
semiprimes; and a proof of systematic failure on a finite block of parameters.
This rejects the stated construction, not the existence of prime-only covers,
the paper's conjectures, or a possible eventually successful subsequence.
No efficient leaf factorization routine was obtained.

## What the primary source actually says

Checked directly against the supplied HTML, not inferred from the baseline
ledger. In the following source summary, its size parameter n is our R.

- Section 6 explicitly leaves shifted progressions with c=1 open. Lemma 6.2
  characterizes prime coverage using a partition of the prime product and a
  CRT congruence; it does not construct suitably small coefficients.
- Proposition 3.4 converts a progression into two smaller difference sets.
  The sets above give our own exact indexing for this particular family.
- Theorem 5.2 assumes every integer <=R divides the product of the A_i,
  efficient interval products, and efficient prime-factor output for each leaf.
  Its proof already uses coverage of the small prime divisors of N.
- Conjecture 5.1 adds the prefactoring requirement. Theorem 5.5 is conditional
  on that conjecture and states exponent max(alpha,beta)/2+o(1); 1/6 is the
  alpha=beta=1/3 aspiration, not an established algorithm here.

[Umans–Wang, Proposition 3.4, Theorem 5.2, Conjecture 5.1, Theorem 5.5, Section 6](https://arxiv.org/html/2511.10851).
The analysis below concerns integers only; prime coverage is not coverage of
all possible irreducible polynomial degrees.

## Exact coverage and obstructions for this family

Write A_i=2^e+i for 1<=i<=L=m^2. The displayed S,T produce every one of these
differences exactly once: the j-th block is B+(j-1)m+1 through B+jm.

For p<=L, an interval of L consecutive integers contains a multiple of p.
For p>L, at most one index works, and it exists exactly when

    1 <= (-2^e mod p) <= L, using the least nonnegative residue.

In particular, residue zero does not count: index zero is absent. This is a
complete deterministic coverage test, not a heuristic distribution model.

**A systematic missed-prime lemma.** If an odd prime p satisfies
p<=m^3, p>m^2+1, and 2^e=1 mod p, then p is missed. Indeed the first positive
index with 2^e+i=0 mod p is p-1>L. For the nominal e=2m and p=65,537,
2^16=-1 mod p and ord_p(2)=32. Therefore every multiple of 16 in

    m = 48,64,80,96,112,128,144,160,176,192,208,224,240

misses 65,537. The inequalities follow from 40^3<65,537<=41^3 and
255^2+1<65,537=256^2+1. Primality of 65,537 is covered by the exact sieve;
the order computation follows directly from 2^16=-1 and the divisors of 32.
The m=48,64,96,128 failures independently occur in the registered data.
This proves the entire stated block fails, including its untested parameters,
but the block is finite. Another small exact certificate is m=5:
2^10=1 mod 31, while the first successful index 30 exceeds L=25.

**An asymptotic height restriction on the same exponent family.** Put
theta(x)=sum_{p<=x} log p. If a member is a full prime cover, then

    theta(m^3) <= sum_{i=1}^{m^2} log(2^e+i)
                <= m^2 [e log 2 + log(1+m^2/2^e)].

This is a divisibility argument only; the prime product is never constructed.
Since theta(x)~x and e>=m, any sequence of successful members tending to
infinity must satisfy liminf(e/m)>=1/log 2. Thus any rule
e<=(1/log 2-epsilon)m, for a fixed epsilon>0, eventually fails rigorously.
This excludes, for example, e=m. The nominal e=2m has adequate aggregate
capacity and is NOT ruled out asymptotically by this bound. Prime divisibility
mass is necessary, not sufficient, and does not supply the required residues.

**Why an arbitrary small step is not a free repair.** If B=2^e and an odd prime
p<=R divides a proposed step c, then B+ic is never zero mod p. In particular
every c<=R having an odd prime factor fails. For c=2^u with u<=e, removing
the common factor 2^u reduces odd-prime coverage to the same consecutive
power-shift family with exponent e-u. This elementary obstruction does not
exclude large steps with no small odd factors or completely different shifts.

## Registered finite evidence

The single run completed all 360 cases (14 nominal plus 346 revision cases),
with no errors, censored cases, or unstarted cases. No parameters were added
after the run. Complete missed-prime lists are retained for every case in JSON.
The table uses R=m^3 and e=2m; the maximum-element bit length is 2m+1.

| m=each set size | L=differences | R | Covered / all primes | Missed | Largest miss |
|---:|---:|---:|---:|---:|---:|
| 2 | 4 | 8 | 3 / 4 | 1 | 7 |
| 3 | 9 | 27 | 8 / 9 | 1 | 19 |
| 4 | 16 | 64 | 12 / 18 | 6 | 61 |
| 5 | 25 | 125 | 17 / 30 | 13 | 113 |
| 6 | 36 | 216 | 20 / 47 | 27 | 211 |
| 8 | 64 | 512 | 37 / 97 | 60 | 509 |
| 12 | 144 | 1,728 | 87 / 269 | 182 | 1,723 |
| 16 | 256 | 4,096 | 166 / 564 | 398 | 4,093 |
| 24 | 576 | 13,824 | 351 / 1,633 | 1,282 | 13,807 |
| 32 | 1,024 | 32,768 | 607 / 3,512 | 2,905 | 32,749 |
| 48 | 2,304 | 110,592 | 1,254 / 10,499 | 9,245 | 110,587 |
| 64 | 4,096 | 262,144 | 2,203 / 23,000 | 20,797 | 262,139 |
| 96 | 9,216 | 884,736 | 4,801 / 70,169 | 65,368 | 884,717 |
| 128 | 16,384 | 2,097,152 | 8,707 / 155,611 | 146,904 | 2,097,143 |

At m=128 only 1,900 primes are covered automatically by p<=L, and 6,807
additional primes are covered by the shift. The ten largest misses, descending,
are 2,097,143; 2,097,133; 2,097,131; 2,097,097; 2,097,091; 2,097,083;
2,097,047; 2,097,041; 2,097,031; 2,097,023. The smallest miss is 16,993.

For the predeclared exponent revision, the best e and residual miss count were:

| m | Best e | Covered / all | Misses | Largest miss for that best e |
|---:|---:|---:|---:|---:|
| 2 | 2 | 4 / 4 | 0 | — |
| 3 | 4 | 8 / 9 | 1 | 13 |
| 4 | 10 | 14 / 18 | 4 | 59 |
| 5 | 9 | 21 / 30 | 9 | 113 |
| 6 | 21 | 29 / 47 | 18 | 211 |
| 8 | 25 | 48 / 97 | 49 | 509 |
| 12 | 42 | 100 / 269 | 169 | 1,723 |
| 16 | 51 | 169 / 564 | 395 | 4,093 |
| 24 | 29 | 372 / 1,633 | 1,261 | 13,799 |
| 32 | 97 | 624 / 3,512 | 2,888 | 32,749 |

All other exponents and failures remain in the evidence. The m=2 successes are
explicit small covers, not an infinite family or an asymptotic gain. A finite
table giving the best exponent is not usable as uncharged size-dependent advice.

The modular coverage rule was independently checked by direct remainder tests
on the actual differences for every nominal m<=16. Twelve nonsquare semiprime
counterexamples also passed an independent full-product gcd check. Two examples:

- N=3,599=59*61 gives floor(sqrt(N))=59 and ceil(cuberoot(59))=4.
  The nominal differences are 257,...,272. Their product is 3,337 modulo N,
  with gcd 1. Thus failure persists with the parameter computed from N itself.
- N=4,397,987,791,019=2,097,133*2,097,143 gives floor(sqrt(N))=2,097,137
  and m=128. The product is 3,825,934,302,822 modulo N, again with gcd 1.

The displayed prime witnesses were independently checked by trial division in
the diagnostic; they were not supplied to the construction. These are failures
of this coverage primitive, not assertions that other factoring algorithms
fail on these N. In particular, easy close factors do not weaken a coverage
counterexample, nor make this a representative factoring timing benchmark.

## Height, description, and complete cost accounting

Let n=bit_length(N), R=floor(sqrt(N)), m=ceil(cuberoot(R)), and M(w) denote
the bit cost of multiplying w-bit integers. Costs below distinguish a formula
from expanded output and from a verified cover.

- **Uniform parameters and height.** The nominal rule e=2m is one fixed finite
  program. Computing R,m,e costs poly(n); writing B=2^e in binary costs O(m).
  H=max(S union T)=2^(2m)+m^2+1 and bit_length(H)=2m+1 for m>=2.
  Thus log H=Theta(R^(1/3)), with no primorial or factor information.
- **Set size and description.** |S|=|T|=m, |S-T|=m^2. An AP description
  with B as a literal binary coefficient uses O(m) bits; an executable
  description allowing the power 2^e uses O(log R) parameter bits plus fixed
  code. Expanding S as full integers takes Theta(m^2) bits, and expanding T
  takes Theta(m log m). Explicit lists therefore already cost
  Theta(R^(2/3))=Theta(N^(1/3)), above the N^(1/5) benchmark. The compact
  description must actually be used, not merely mentioned after expansion.
- **Modular generation.** B mod d can instead be computed by O(log e)
  modular multiplications. Generating the two progressions modulo d then
  takes O(m) additions on at most n bits. There is no need to build B in full
  during this primitive. Its cost is O(M(n)log m+mn), up to reduction costs.
- **Interval products.** Order pairs in columns by t, with s varying within a
  column. An interval has two partial columns and a consecutive block of full
  columns. For the full columns form the monic polynomial product(X-t),
  evaluate it on all s, and multiply the evaluations. Monic product/remainder
  trees require no inversion of arbitrary nonunits modulo composite d.
  Fast arithmetic gives a standard soft-O(m M(n)) bit bound, plus modular
  generation. A direct O(m^2) modular loop is also executable but slower.
  The experiment did not implement or time fast polynomial arithmetic and
  does not independently certify that implementation bound.
- **Coverage construction/certification.** The cheap formula has failed the
  contract. The actual finite screen first sieves R, taking Omega(R) storage
  initialization, and then performs pi(R)-pi(L) modular-power tests per case.
  Its classical upper bound is soft-O(R) bit work for a nominal screen,
  including sieve and prime output. The exhaustive exponent-selector used
  here performs (3m+1)(pi(R)-pi(L)) tests, hence Omega(mR/log R) such tests
  asymptotically and soft-O(mR) bit work. These exceed R^(2/5)=N^(1/5).
  This is an obstruction to the implemented search/certificate method, not
  a lower bound on every possible analytic construction or verification.
- **Leaf cost.** Even perfect coverage would not make gcd(d,B+i) prime or
  reveal its factors. For m=8,i=18, the evidence gives
  65,554=2*73*449 and d=32,777=73*449, so gcd(d,A_i)=d is composite and
  d<=R^2. General d<=N can likewise be unsplit at a leaf. No all-leaf cheap
  routine is supplied. Factoring it by trial division costs at most
  soft-O(sqrt(d)) divisions' bit work, potentially soft-O(R), and calling a
  known general factorer must charge its own full cost. Building a complete
  prime-to-index allocation by the above sieve already spends R-scale work.
  The small exhibited collision proves only the missing obligation, not a
  lower bound on leaf factoring.

The promising size parameters would make the interval primitive about
N^(1/6) times logarithmic factors. Coverage, construction of a valid cover,
and leaf extraction have not been supplied at that cost. In particular, this
is not a deterministic exponent improvement over the W001 N^(1/5) baseline,
and no practical or heuristic GNFS comparison is made.

## How the prime-only reduction applies, and where it stops

For completeness, the relevant correctness argument needs only prime coverage.
Suppose every prime <=R divides some nonzero A_i, all interval products can be
computed, and a leaf procedure actually factors gcd(d,A_i). Put
N0=gcd(N,product A_i). Every prime <=R dividing N divides N0, although N0
may have smaller multiplicity. Recursive splitting maintains
d | product_{i=a}^b A_i. If P,Q are the two half-products and
g=gcd(d,P), then g|P and d/g|Q, by comparing each prime valuation; coprimality
of the half-products is unnecessary. The nonunit leaves multiply to N0,
so there are at most n of them. Factor these leaves, collect their primes,
and trial-divide each repeatedly from the original N. The remaining cofactor
is 1 or one prime greater than R, since two such factors would exceed N.

A conservative explicit cost envelope is

    T_generation + O(n log(k+1))*(T_interval + T_gcd)
                 + O(n)*T_leaf + poly(n),    k=m^2,

where all subroutine bounds include bit widths, generation of their inputs,
and prime certification as needed. This argument does not create any of those
subroutines. In our family coverage already fails, and the leaf cost is also
unresolved. The prime-only observation is closely visible in the source proof;
no novelty is claimed for this reduction, and this child report is not an
independent review accepting H004.

## Run accounting and evidence integrity

Invocation (once, from the project root):

    timeout --signal=KILL 60s python3 -B research/hypotheses/H004-cover-power-shifts.py

The internal limit was 50 seconds. Recorded time including result serialization
was 0.264790 seconds, with a final process print at 0.264949 seconds. The sieve
accounted for 0.044288 seconds. Peak process RSS was 51,644 KiB. These are
machine-local diagnostics, not bit-complexity evidence or matched benchmarks.
The one fresh sieve through 128^3 was shared across the registered cases and
charged once to this diagnostic; per-case times are not cold solver timings.
The final tiny manifest write and print occur after the stored timing sample;
the external 60-second kill covers the complete process. Counts were 733,523
modular powers, 158,962 direct remainders, and 34,141 negative-product modular
multiplications. These counters intentionally do not pretend to price the
sieve, Python control flow, primality checks, or serialization as unit events;
wall time and RSS include that work. Human reasoning and report writing are
not part of a claimed solver runtime.

Evidence, all in this directory:

- [Frozen preregistration](H004-cover-preregistration.md).
- [Executed standard-library source](H004-cover-power-shifts.py).
- [Complete results, including every missed prime](H004-cover-results.json).
- [Manifest, environment, timing, and hashes](H004-cover-manifest.json).

SHA-256 of the frozen preregistration:
`f9bfd5106073d597b764d35c134dd085ef055c9c6dbd78d5146c3e8e29310c5e`.
SHA-256 of the executed script:
`75169e59555bbd84e910eca024188a0a9d12a5bd7d21e941a5c874b2e22d9dd0`.
SHA-256 of the complete results:
`a5aaeb040cdae929d627b1228746016b975488dc146099d725bd6dcd978aadff`.

No shared code or Lean was changed, so shared build/check scripts that would
write outside the owned files were not run. Scratch assertions checked the
registered direct enumeration, negative semiprimes, and leaf collisions.
No nested agents, dependency installation, commits, publication, or scheduler
were used.

## Disposition and next revision

**Reject the nominal power-shift rule; reject the scanned exponent-tuning
repair at all tested m>=3. Verified improvement: NONE.** The evidence does not
establish a large-m density law, infinitely many failures of e=2m, or an
impossibility theorem for shifted progressions. Repairing finitely many m by
special cases would not solve coverage or leaf extraction for unbounded m.

One concrete next revision within the same progression approach is to allow
both bands B-L,...,B-1 and B+1,...,B+L, with B=4^m. Use the existing T and
S_plus above together with S_minus={B-jm : 0<=j<m}. The union has
|S|=2m, |T|=m and the same asymptotic height, and contains no zero differences.
It covers the systematic residue-one misses via B-1 without enumerating primes.
The exact remaining condition for p>L is that -B mod p lies within L of
either end of the residue interval; this is still not automatically satisfied.
This revision was NOT run or counted as a success. A subsequent authorized
wave should preregister that single change, retain the largest misses, and
either prove uniform coverage and costed leaf extraction or reject it. Simply
enlarging the exponent grid or buying a prime-allocation table is not progress.
