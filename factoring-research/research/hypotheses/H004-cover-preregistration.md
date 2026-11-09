# H004 construction attempt — powers-of-two shifted progressions

Status: preregistered, before computation. Date: 2026-10-08 UTC.
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

## Results and analysis

Pending the registered capped run. Primary source checked directly:
[Umans–Wang, Sections 5–6](https://arxiv.org/html/2511.10851#S6).
