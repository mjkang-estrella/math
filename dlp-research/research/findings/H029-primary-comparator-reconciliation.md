# H029 primary comparators: accepted evidence and corrections

2026-10-08. Opus's raw report/task ID is in H029-primary-comparator-opus-raw.md.
Independent native Sol reread primary texts; root checked Bos Table1/Table3 and
§§4.6–4.7 from the downloaded primary extraction and Rotem–Segev online. EPFL
failed in root/Sol's web tool; original primary bk.pdf/bk.txt downloaded by Opus
were accessible in /tmp/h029lit.4NEx. No local experiment or new Lean theorem.

## Executed historical comparator

[Bos et al., prime-field ECDLP record](https://infoscience.epfl.ch/record/164550/files/164550.pdf)
supports the one solved112-bit instance at approximately8.5e16 additions and
slightly over5e9 distinguished points. Final regular-iteration accounting is456
cycles with400 walks/SPU and a special modulus; the actual campaign also used
earlier slower software. Roughly580 cycles is a generic-modulus estimate, not
a second executed record. It does not calibrate contemporary GPU hardware.
Table1's16-adding ratios1.036/1.033 without negation and1.016/1.016 with negation
are measured/predicted collision-step ratios on32-bit curves; costly cycle
detection is not erased by those ratios. They are not complete-work speedups.
Jump tables/starts/arithmetic support require setup; "no preprocessing" must not
be read literally as zero setup. This historical comparator establishes neither
our current baseline's optimality nor any new algorithmic gain.

Reject raw transfer of its fixed r-adding same-partition correction into the
fresh-iid landing model. The latter already has its own exact probability law.
Actual new walks need their own law, not a convenient multiplier from another map.

## Constructive preprocessing tradeoff

[Rotem–Segev, ITC2022](https://drops.dagstuhl.de/storage/00lipics/lipics-vol230-itc2022/LIPIcs.ITC.2022.12/LIPIcs.ITC.2022.12.pdf),
Theorem6, gives success >=s*l²/(8N)-O((3l)^(-c)) when s*l²<=N/64,
state O((s+l)logN), online O(l*t_exp). Algorithm A0 performs s*l group
exponentiations; hash generation and endpoint construction also cost work.
The achievable success lower bound is NOT a necessary resource lower bound.
The separately cited generic upper bound has different quantifiers and hidden
log factors. Withdraw raw literal ST+T>=2sqrtN conclusion.
Choosing s*l²=Theta(N) yields the explanatory exponentiation envelope
(N/l+l)*t_exp, plus other construction costs. Balancing is square-root scale;
this is neither a universal lower bound nor a measured comparison to rho.
Replacing full exponentiations by finite-list r-adding steps needs a new proof.

## Additional fixed-point checks

[Neamah, primary preprint](https://arxiv.org/pdf/1607.05901), pp7–8, retains
ordinary and reverse collisions as well as testing O,+/-P,+/-Q. Raw "only five
points" description is therefore incorrect. Marked set size is at most5, possibly
smaller; q/5 waiting needs an independent-uniform or other justified hitting
model, not merely this set cardinality. Recovery also needs invertible label
denominators. Informative labels on an example start R0=P already encode a
relation; obtaining them is not free. Trivial labels(1,0) do not recover the
target. No fivefold complete-work gain follows from the examples.

## Decision

Retain the historical measurement, constructive theorem and counterexamples to
overbroad interpretations. No new survivor or numerical experiment is supplied.
Current verified improvement NONE; generic exponent reference1/2 unchanged.
Literature search non-discovery is not novelty or an exhaustive absence claim.
