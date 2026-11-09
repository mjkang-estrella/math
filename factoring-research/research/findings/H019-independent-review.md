# H019 — Independent implementation and evidence review

2026-10-08. **ACCEPT the frozen finite implementation and the degree-52 primitive-irreducible upper-count certificate. ACCEPT the three other count outcomes as UNKNOWN. The registered screen remains INCONCLUSIVE. Verified full factoring complexity improvement: NONE.**

No defect requiring revision of these finite claims was found. This review independently checked the mathematical links to the accepted H017 theorem, read every original implementation source, and performed exactly one newly frozen arithmetic replay of the archived witnesses. All nine review cases were verified, with zero verification failures, errors, timeouts or unstarted cases. This does not convert the three original unknowns into count certificates or change the continuation rule.

The complete AGENTS.md, README.md, docs/SPECIFICATION.md, RESEARCH_LOOP.md, RESEARCH_TEAM.md and research/STATE.md were read, followed by the full H019 hypothesis, expanded protocol, 144-line finding, candidate, reference and runner; the full H017 derivation, independent review and disposition; and the original manifests, outcomes, control witnesses and worker records. Frozen counterparts match the reviewed originals except the legitimately changed live STATE. The user's narrower review ownership controlled this task. Only this report and adjacent H019-review-* artifacts were written.

**1. ACCEPT — protocol compliance and evidence correspondence.**

The controlling [H019 hypothesis](../hypotheses/H019.md) and [expanded protocol](H019-certificate-protocol.json) agree on the four cases, public degree map, parameters, root proposals, sufficient predicates, timing and continuation condition. The runner has one persistent `random.Random(1919)` and exactly four ordered `getrandbits(n-1)` calls. The review reproduced these exact archived draws, including the leading-bit and odd-bit OR operations, all hexadecimal payloads and N-only object schemas. There was no factor input or case-family label at the worker boundary. These integers have no semiprime, composite or hard-factor promise.

The source uses integer Newton iteration and exact corrections for m, ordinary base-m digits, and exact height/cutoff arithmetic. It leaves degree/monicity failures unknown. The review independently enclosed each archived m between consecutive dth powers, rebuilt every digit by divmod, checked f(m)=N, and verified H=2^ceil(67473*n/(20000*d²)) and (h_*-1)^5<H^4<=h_*^5. The four H exponents are exactly 62, 115, 192 and 328.

Static review confirms the prescribed degree-(d-2) truncation is used only for proposals. Coefficients are divided by their maximum before floating conversion. The Cauchy radius, half-phase start, simultaneous old-vector Aberth corrections, 500-sweep maximum, 2^-42 correction cutoff, denominator 2^40 and radius 2^-24 match the protocol. There is no alternative start, adaptive precision/radius or retry. Collisions, failed convergence, nonfinite values and caught arithmetic errors yield unknown. Recorded sweep counts are 50, 22, 18 and 51. The review checked the recorded correction cutoff and independently rounded the archived binary64 centers using exact fractions; it did **not** rerun Aberth or independently reproduce its trajectory.

The original runner freezes sources and inputs before importing the arithmetic modules, charges input generation and freezing to setup, runs the five controls first under a shared 3-second cap, and gives each research worker min(12 seconds, remaining budget less its reserve). Fresh process groups are killable; worker timeouts retain partial logs and a fixed denominator. Exclusive creation refuses overwriting original evidence. The source and stage logs show one recorded original trial with no fallback. All five worker groups exited normally, all logs have empty stderr/stdout, and every recorded worker wall time is within its cap. The archived completion time through sealing is 5.830190 seconds; the finding reports 5.834619 seconds through final output. Neither this timing nor an event counter is a bit-machine cost theorem.

The [integrity record](H019-review-integrity.json) independently confirms all 57 sealed files and byte lengths, all 13 frozen source/document hashes, all six frozen input-file hashes, and the seal/completion link. All current original source/document hashes match except mutable STATE. The original freeze hash is `c60a9c190308e9ab20c642496ea43ca8f12db2b46de186b907e27b4d504a87af`; seal hash is `4f71fce92f6412014d6b154e7d1a2344c75420c32bf3c1bbd95443588b6b164f`.

Hashes establish byte correspondence. They cannot independently attest that no unlogged pre-freeze exploratory execution ever occurred. The available source, retained logs and report are consistent with the authorized single-trial protocol; this review makes no stronger historical claim. Timeout/unstarted branches were inspected, not fault-injected or dynamically tested.

**2. ACCEPT — square-freeness and complete root accounting.**

The fixed modulus 65537 was independently trial-divided by every integer 2 through 256; all 255 archived remainders match and are nonzero. For each research polynomial, independent convolution verifies s*f+t*f'=1 modulo this prime, coefficient by coefficient. Monicity preserves degree under reduction. A repeated monic rational factor would give a nonconstant common factor of f and f' after reduction, contradicting that identity. Thus the sufficient modular certificates prove square-freeness over Q; they do not prove irreducibility of f. No second modulus or square-free-part substitution occurs.

For nonnegative ordinary digits, the strict inequality

    f[d-2] R^(d-2) > sum_(j != d-2) f[j] R^j,   R=2H+2,

makes f[d-2] X^(d-2) dominate the remainder everywhere on |X|=R. Rouché gives exactly d-2 roots inside, none on the circle, and exactly two outside. Their modulus is therefore strictly greater than the H017 large-root threshold. All four archived dominance products, widths, hashes and strict decisions were independently checked.

There are exactly d-2 disks in each research witness. Every disk is strictly inside R, every pair is disjoint, and every disk passes the full-f one-root test below. They account for all d-2 interior roots. Together with the global count this covers **all d complex roots**, including conjugates, without locating the two exterior roots. This is precisely the combination already allowed by H017 equations (18)–(19) and its accepted disposition, not a new population theorem or an assumption about omitted roots.

**3. ACCEPT — exact full-polynomial Taylor predicates.**

Put Q=2^40, S=2^24, z=(x+iy)/Q, and A_j=Q^d f^(j)(z)/j!. At each Horner extension the candidate multiplies its current polynomial by x+iy+QY and adds f_i Q^level. Induction gives the claimed shared-denominator Taylor array. The original reference instead reconstructs

    A_j = sum_(i=j)^d f_i binom(i,j) (x+iy)^(i-j) Q^(d-i+j).

It imports no candidate Taylor or predicate functions. The independent review also uses this binomial identity, with monomial-first accumulation and a binomial-coefficient recurrence; it imports or executes neither original module. Sharing an algebraic identity with the reference is disclosed. Arithmetic agreement alone would not prove the theorem, so the normalization and inequality were checked directly here.

Coordinate maximum is a lower bound on complex modulus; coordinate sum is an upper bound. Multiplying H017's strict linear-term dominance inequality by the positive Q^d*S^d gives exactly

    max(|Re A_1|,|Im A_1|) S^(d-1)
      > sum_(j != 1) (|Re A_j|+|Im A_j|) S^(d-j).

Thus the linear Taylor term dominates on |Y|=1/S, proving exactly one full-f root, counted with multiplicity, in the disk. The exponent d-j on each right term and d-1 on the left are correct. Strictness is essential. Truncation coefficients are never substituted into this proof.

With TQ=Q/S=2^16, the exact squared checks are distance²>(2*TQ)² and x²+y²<(R*Q-TQ)², with R*Q>TQ. They are sufficient for strict disjointness and containment. The replay matched every archived Taylor-array hash, every exact cleared lhs/rhs, associated bit lengths/hashes and acceptance decision: all 115 research disks passed.

**4. ACCEPT — positive geometry and H017 equation (11).**

For every certified interior root alpha_i, the disk gives

    U_i=max(1,|Re z_i|+|Im z_i|+1/S) >= max(1,|alpha_i|),
    L_ij=max(0,max-coordinate-distance(z_i,z_j)-2/S) <= |alpha_i-alpha_j|.

Therefore L_ij/(U_i U_j) bounds each normalized pair separation below. The review recomputed every pair as a reduced rational and multiplied these pair bounds for **every** distinct triple, divided by six. This yields the same positive kappa as the archived L-product formula with U_i² U_j² U_l² in the denominator. Each root occurs in two pair denominators, explaining the squares. No real-root restriction or conjugate deduplication is permissible or used. The first minimizing triple and reduced numerator/denominator match in all four cases.

The H017 proof was checked independently of the code. The three normalized evaluation rows have entries of modulus at most one and determinant equal in modulus to the triple separation product. Cofactor row sums are at most six divided by that determinant. Hence at least k-2 evaluations have normalized magnitude >=kappa*h. The other two contribute at least the square of the smallest evaluation e. The two exterior roots each contribute >1/2 for every allowed quadratic. Combining the resultant product with A<=2^d M(f) gives

    e² <= 2^r 12^d(d+1) H^d N^(-9/(5d)) / (kappa*h)^(k-2).

At h>=h_*, the cleared equation (11) forces e<=1/(144H³). H017's accepted H008 uniqueness argument then bounds the integer resultant between two height-H quadratics at the same witnessing root by 72/144=1/2<1. Primitive irreducibility and positive leading normalization force them to coincide. There are at most k high-height exceptions; all lower-height quadratics fit in exactly (h_*-1)(2h_*-1)² triples. These are the already accepted H017 implications, not new substantive lemmas.

For k=d-2, r=2, kappa=x/y>0, the implemented comparison is exactly

    (x*h_*)^E N^9 >= y^E [20736*2^2*12^d*(d+1)*H^(d+6)]^(5d),
    E=5*d*(k-2)=5*d*(d-4).

All bases are positive; taking powers and clearing denominators preserves order. Equality is safe for this comparison because the later uniqueness gap is still 1/2<1. Equality is not safe for either Rouché predicate. The review matched every factor base/exponent and independently recomputed all four huge products using powers and a product accumulation, including an actual H power instead of the candidate's binary-shift shortcut. Product hashes and widths all match.

**5. ACCEPT — exact individual outcomes; preserve the registered criterion.**

All four cases have verified base, square-free, global-count, disk-coverage and positive-geometry certificates. Their count outcomes are:

- **4096 bits, d=15: UNKNOWN.** k=13, H=2^62, E=825. Equation (11) fails: left 262,653 bits, right 294,544 bits. The exactly evaluated trial expression is `0x6f6e336b6f846858fe6c7d65b9c9896712c388` (151 bits). It is **not a certified population bound**. [Replay result](H019-review-evidence/n4096-d15-result.json).
- **16384 bits, d=22: UNKNOWN.** k=20, H=2^115, E=1980. Equation (11) fails: left 782,415 bits, right 839,088 bits. The trial expression is `0x3ffffffffffffffffffffff80000000000000000000000500000000000000000000013` (278 bits), **not a certified population bound**. [Replay result](H019-review-evidence/n16384-d22-result.json).
- **65536 bits, d=34: UNKNOWN.** k=32, H=2^192, E=5100. Equation (11) fails: left 2,515,137 bits, right 2,538,571 bits. The trial expression is `0x6f6e336b6f8480853d874c2c9fea59ff43f038c87b34c6459e195cb9e1164f9ff5f3111004100fe97ccb9806b08d4bb8870113e198221ae3350e` (463 bits), **not a certified population bound**. [Replay result](H019-review-evidence/n65536-d34-result.json).
- **262144 bits, d=52: PASS.** k=50, H=2^328, E=12480. Equation (11) holds: left 8,425,749 bits, right 7,972,362 bits. Its exact certified upper bound C has 790 bits. [Replay result](H019-review-evidence/n262144-d52-result.json).

For the passing case the verified values are:

```text
h_* = 0x5472d14ee54db115a4ea11db2e5ade00b464328b6706d4b0455447ad0de103ad96
kappa numerator = 0xcf18c3e20cc4183a7d759f4282800000000000000000000000000000
kappa denominator = 0x463d75406ab7838b2061a3f6354919c065e3b0730b7606e1fcf926aaf061
minimizing triple = [3,4,5]
C = 0x24c2230d75cce92d4a43c840ec1c3eb99817b92b236d471a569f595302dd051c78ff0d2f9b972e0d41c6189a1719d78708f6cfac7ae65df0a7834a10adf3ae2f102fa85182ce6bdeba2ea43b1c4485e6aa2d5886c51ba90e973f6c3fe3467deb34b35f
left SHA-256 = b9dbac1d9a7b0d7176a5c9215b9ca8a31d6c56a2fa8b1ed0a5016d973dcc38b4
right SHA-256 = c68fbd0cf1f6bfd844da1e797aec1e05fbce070b1b19f5f83b27ffac0c81ccac
```

For this archived N and its verified degree-52 f, with A=max_i f_i, C bounds the number of genuine primitive quadratics irreducible over Q with 1<=a<=H, |b|,|c|<=H satisfying

    |Res(f,aX²+bX+c)|^(5d) N^9 <= [(3H)^d(d+1)A²]^(5d).

It is an exact integer **upper bound**, not an exact population cardinality. No quadratic was enumerated. The three failed sufficient comparisons neither prove these smaller trial expressions valid bounds nor provide positive supply, lower counts or a counterexample to H017.

The original denominator remains four research cases: **1 pass, 3 unknown, 0 verification failures, 0 errors, 0 timeouts, 0 unstarted**. All controls are correct, but the 65536-bit required case did not pass. Consequently the controlling requirement for **both** largest cases remains unmet. **ACCEPT the INCONCLUSIVE disposition; reject any reinterpretation as a continuation pass.**

**6. ACCEPT — control coverage and the independent replay evidence.**

The five controls were independently verified at their specified gates: accept both disks for X²-2; accept both for X²+1; reject the zero-centered X²-2 disk at Taylor–Rouché; reject duplicate disks at disjointness; reject (X-1)² at square-freeness. For the last control this review directly verified its common root with its nonzero linear derivative, rather than rerunning either modular gcd implementation. The duplicate/repeated controls are not claimed to have reached Taylor verification. No additional controls or geometry inputs were introduced after freeze.

The [review protocol](H019-review-protocol.json) and [review source](H019-review-audit.py) were written and syntax-parsed before any arithmetic execution. The [review freeze](H019-review-freeze.json) hashes 76 fixed files, including all 59 original archive files, the reviewer source/protocol and reviewed immutable sources. Live STATE is recorded separately as mutable provenance. The sole invocation was:

```bash
timeout --signal=KILL 60s .venv/bin/python -B research/findings/H019-review-audit.py
```

It used a 55-second internal cap, a 53-second attempts deadline reserving time for evidence, 3 seconds for all controls, and up to 12 seconds per research worker. Review runtime was **3.500754 seconds through final output**, 3.496181 seconds through sealing. All nine cases were verified, with no failures, errors, timeouts or unstarted cases; every review worker exited zero. Approximate original proposals were read only, never recomputed. The frozen review source was not changed or rerun.

Observed arithmetic coverage was four base reconstructions; four global dominance checks; eight unit modular Bezout identities plus the repeated-root rejection; 115 research containment checks; 1,989 research disjointness comparisons plus four control comparisons; 120 Taylor predicates (115 research accepts, four control accepts, one control rejection); 99,028 direct binomial terms; 1,989 normalized research pair bounds; **25,986 research triple bounds**; and all four cleared count comparisons, factors, hashes, widths and trial-count expressions. These counters state what was checked, not its certified bit cost.

[All review outcomes](H019-review-evidence/outcomes.json), individual results, stage logs, [preflight](H019-review-evidence/preflight.json), [seal](H019-review-evidence/seal.json) and [completion](H019-review-evidence/completion.json) retain the evidence. Review status `verified` means the archived outcome was independently checked; it is deliberately distinct from the original count status `pass` or `unknown`. The 30 sealed review files and completion link were checked after the replay.

```text
review source SHA-256 = e49529b3d479f2de67e89f85a9e6e3448b61237a5463c66e66838b51b6775ee1
review protocol SHA-256 = dce220e88710390287de59bcc40703d6d6cec65f6a526388f4d5ed612b0dc1f5
review freeze SHA-256 = 8d5e1621830052c706db3fdbc68d6919db749c40fb23fee9d93ab9891f54b5be
review seal SHA-256 = a6f8dc6837a96224950ff78f81995feefe7ab504aac580c585717b353e46d5a2
```

[Final review provenance](H019-review-provenance.json) captures reviewed/owned file hashes and post-review correspondence. No project checks, original runner, original reference or original candidate were executed in this review. The parent's reported 12 Python tests, source screen, Lean build and axiom audit remain separate from research-certificate verification.

**7. ACCEPT the restricted finite scope; REJECT stronger interpretations.**

Irreducibility in the population claim concerns g. Square-free reducible f is allowed by H017; this review establishes no number field or field admissibility. A zero resultant is included where applicable in the population count and its exceptional-root argument, but it is not a smooth nonzero norm. Primitive irreducible quadratic zero-resultant members must be quadratic factors of f. Reducible quadratics and positive contents retain their separate H017 qualifications; no finite numeric all-output bound is inferred from O(H² log H). Reducibles can supply distinct linear factors, and the square-class relation R=V+c*1^T, even-cardinality restriction and odd dependency cosets remain relevant. No rank-at-most-d shortcut is accepted for that population.

H016's processing result and H018's corrected degree model remain separate. The heuristic smoothness comparison supplies no useful-relation lower bound, rank, algebraic square roots or proper splitting. One valid finite upper-count certificate establishes no all-input geometry, asymptotic gain, field-selection escape probability or population/pass frequency. These four public odd inputs are not a factorization benchmark; no factors were found.

The accepted result is reviewed informal mathematics backed by exact Python integer witnesses, not Lean refinement of the verifier or an all-input runtime theorem for binary64 root proposals. The original and review failures/timeout paths were not exhaustively tested; sufficient-test failure must remain unknown and a timeout remains a censored implementation result. No new substantive theorem beyond the accepted H017 chain is promoted here.

No revision is required for the finite claims or the recorded INCONCLUSIVE disposition. Any changed geometry method, parameters, sample or continuation criterion would be a separately authorized and preregistered round; none was started. No packages, recursive delegation, commits, publication, scheduler, prior-evidence changes, shared solver/Lean edits, STATE updates or registry changes occurred. **Verified full factoring complexity improvement remains NONE.**
