# Arithmetic discovery r1: the uniform quartic paired-Jacobsthal problem

Author: **Myeongjin Kang**. No affiliation. Research date: 2026-10-15.

**Disposition: UNRESOLVED; no substantial theorem nominated.** The selected full-scope statement C4 below is neither proved nor refuted. The complete new-to-this-note deductions are the cutoff-to-cardinality transfer in §4, the exact two-label tree and arithmetic shortcut checks in §5, and the routine squarefree-argument screening theorem in §6. These do not meet the requested substantial-contribution gate. No manuscript or formal package has been prepared. Campaign count remains **4/10**; this author has not conducted an independent review of this work.

All mathematical results used from `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are assumed true, as instructed. The issue is the new interface, not upstream truth. All retained upstream files were obtained from immutable raw URLs and matched against the complete pinned preprint tree. Exact byte hashes, Git blob identities, reading extents, external retrieval receipts, inputs and outputs accompany this note.

## 1. Exact selected problem and the bounded selection

For an integer k ≥ 1 let G₂(k) be the least positive integer H such that, for **every** set P of at most k distinct rational primes, every choice of sets

    R_p ⊂ Z/pZ,   |R_p| ≤ 2,   |R_p| < p    (p ∈ P),

and **every integer** a, the interval {a+1,…,a+H} contains n satisfying

    n mod p ∉ R_p for every p ∈ P.

Empty R_p are permitted. The properness condition forces |R₂| ≤ 1 and is essential. Prime sizes, residue choices and interval positions have no bounds. Multiplicities of prime divisors are irrelevant.

**C4 (selected original target).** There is an absolute constant C such that

    G₂(k) ≤ C k⁴  for every integer k ≥ 1.                         (C4)

This is a two-class, arbitrary-prime-set Jacobsthal theorem, not just a statement about the first k primes or the fixed pair of classes {0,−2}. No effectivity of C is required. Proving C4 by a genuinely new dimension-two comparison would be a substantive arithmetic contribution; this note does not establish that comparison or assert worldwide priority.

Exactly three serious options were screened, before developing C4:

1. **Power saving for polynomial differences at squarefree arguments.** A complete local characterization and fixed-dilation deduction are given in §6. It is a routine consequence of the pinned prime-argument theorem, including its zero convention, after a bounded partition. It is excluded from nomination despite its superficially different argument set.
2. **Finite mixed sums of products beyond FS ∪ FP.** The actual Hindman manuscript already includes arbitrary prescribed separation and distinct-expression conclusions. Its Prediction Principle counts specified additive forms against a product-color mask; it does not automatically count arbitrary alternating sum/product expressions. No new alignment principle was proved. This option was screened and stopped, rather than promoted by changing the configuration.
3. **C4.** Selected for detailed work because it has a precise full uniform scope, a genuine sieve-dimension change, a clear primary predecessor, and an identifiable unpaid bridge.

The project context was consulted before selection. In particular R006/R008/R010's prime-factor laws, I73/I75's polynomial-twist gaps, I99's synchronized polynomial-pattern gap, I204's denominator-cap gap, I282's mesoscopic factor-law gap, and the two recent Liouville reports were excluded. The Liouville supporting processes are not arithmetic counterexamples. C4 does not use or duplicate the active geometry/Borsuk or operator/quantum work. No active directory was edited or incorporated as an input.

## 2. Actual source contracts

All paths in this subsection are under `preprints/` at the stated pin. Their retained copies live only in this assigned folder. `sources/manifest.json` gives full paths, immutable raw URLs, full Git blob hashes and SHA-256 hashes; `reading.json` distinguishes complete reads, selected passages and unread retained files.

**J — `A-quadratic-bound-for-Jacobsthals-function-September-25-2026`.**

* `build/sections/introduction.tex`, `thm:main`: for the **one-class** function h(k),

      h(k) ≤ C k² / (log log(3k))².

  This is stronger than the catalogue's summary. It covers arbitrary prime sets and interval translations. The simultaneous conditions are still one residue per prime.
* Same file, `thm:survivors`: for L=log z, Y=floor(z²/L²), w=L/(log L)², B=L/log w and V₀=∏_{p≤w}(1−1/p), **one** forbidden residue at each p≤z leaves at least cYV₀/B² points of [1,Y], uniformly in the residues. This is of order Y log log z/(log z)², not a dimension-two estimate.
* `build/sections/inputs.tex`, `lem:fundamental`: intersection densities g are multiplicative, 0≤g(p)≤2/p, g(p)<1, g(2)≤1/2, and at a sufficiently large sieve parameter s the count is

      X ∏(1−g(p)) (1+O(e^(−cs)))
      + O(∑_{d≤v^s} τ(d)^C |r_d|).

  Constants are absolute. This stipulated classical input **does** allow two local classes. It does not assert positivity at parameter four. `lem:small-sieve` itself is stated for one class; §4 proves the two-class progression upper bound directly from `lem:fundamental`, rather than citing the one-class lemma with changed hypotheses.
* `build/sections/tree.tex`, `eq:tree-identity`, `eq:reference-tree`, `eq:total-prefix-mass`: exact least-bad-prime partition, one-class transition weight 1/p, total unrestricted prefix mass ∏(1+1/p) ≪ B. Read through the stopped comparison identity.
* `build/sections/reference.tex`, `prop:reference-margin`: its positive B⁻² margin is for the displayed **one-class** reference tree at r₀=2B−a★+o(1).
* `build/sections/inverse.tex`, `prop:inverse`: after fixing its candidate-box ranges, discrepancy threshold and exception fraction, there is a bounded rational list for **one prescribed a_p at each prime**, with alignment Da_p≡A (mod p). The whole-box measure, fixed-width order and denominator/intercept restrictions are part of the statement.
* `build/sections/stops.tex`, `prop:stopped-comparison` and `prop:hard-stopping`: comparison at its defined rational-owned stops and coverage in its original harmonic measure. These have not been extended to two classes here.
* `build/sections/assembly.tex`: the complete final proof was read. Its large-prime deletion step inspires §4, with the changed sieve dimension explicitly paid there.

The complete preprint tree and catalogue locate one J manuscript, not a separate two-class companion. Retention of its full TeX source is not a claim to have read all its technical proofs.

**P — `A-Power-Saving-for-Polynomial-Differences-at-Prime-Arguments-October-5-2026`.** `build/sections/introduction.tex`, `thm:main`: if fixed h∈Z[t] has degree ≥2, positive leading coefficient, and for every q a root r modulo q with gcd(r,q)=1, then constants c_h>0,C_h≥1 give

    (A−A) ∩ {h(p): p prime} ⊆ {0}  ⇒  |A| ≤ C_h N^(1−c_h)

for all N≥1 and A⊆[N]. Constants depend on the **whole fixed polynomial**. The zero exception is explicit. This supplies only §6, not C4.

**I — `A-power-saving-for-intersective-polynomial-differences-with-an-exponent-depending-only-on-the-degree-October-5-2026`.** Its introduction's `thm:main` concerns unrestricted positive integer arguments and a degree-only exponent, with polynomial-dependent constants. This companion does not justify a degree-only prime exponent or a growing-coefficient family. **S**, the September 24 square-difference companion, is checked at its introduction: it is the scalar square case, not a uniform sieve statement. Neither I nor S is needed to prove §4.

**H — `Monochromatic-finite-sums-and-products-in-the-positive-integers-September-23-2026`.** Introduction `thm:main`, `cor:distinct-expressions`, and framework through `pr:prediction` were inspected for option 2. The source already permits fixed R,D separation. Its specified FS/FP scope, block-chain ordering and product mask were not broadened by assertion.

## 3. Primary literature comparison and the exact arithmetic object

[Ziller–Morack, arXiv:1706.00317v1](https://arxiv.org/pdf/1706.00317v1), Definition 2.1, defines j₂(Q) using paired progressions (a+i,b+i) with even b−a; Definition 2.2 defines h₂(k)=j₂(p_k#). Definition 2.1 and its parity exception were also inspected on the rendered page. The object and its paired formulation are therefore credited, not claimed new.

Here is the precise CRT equivalence. Choose labels a_p,b_p for a nonempty R_p, repeating a label for a singleton. CRT gives a,h with

    a≡a_p (mod p),    h≡b_p−a_p (mod p).

Then n avoids all R_p exactly when

    gcd((n−a)(n−a−h), Q)=1,   Q=∏_{p∈P}p.                 (3.1)

When 2∣Q, h is automatically even. When Q is odd its representative can be made even by adding Q. Empty local sets may be filled with one residue; this only makes avoidance harder. Conversely (3.1) gives a proper at-most-two-class system when h is even. Thus C4 is equivalent to an absolute quartic bound for the supremum of this paired function over **all** Q with ω(Q)≤k. CRT and translation preserve maximum gaps. They do not restrict h to a small integer or turn the problem into the fixed twin-slot problem.

Ziller–Morack's Conjecture 6 asks the much stronger primorial estimate h₂(k)<p_k²−p_k. Their propositions connect **that specific stronger bound** to prime-pair/Goldbach assertions. C4 would not establish their conjecture or those prime assertions. The companion [arXiv:1706.03668v1](https://arxiv.org/pdf/1706.03668v1), Definitions 2–4 and Table 1, gives computational values; our exact checks reproduce its first four values 2,6,18,30. These finite values do not prove C4 or primorial extremality.

[Franze, arXiv:1012.3809v1](https://arxiv.org/pdf/1012.3809v1), Introduction (1)–(4), Theorem 1 and Table 1, states the distribution/remainder hypotheses and gives its dimension-two Selberg lower bound at exponent 4.516. Table 1 reports the DHR dimension-two threshold as approximately 4.266. This is a primary paper's comparison table; the complete DHR Theorem 9.1 was **not** obtained/read here, so its full hypotheses or the digits 4.26645028 are not certified by this note. The Cambridge primary excerpt was inspected for local densities, properness and the exact remainder decomposition, not for an absent chapter. These classical scales explain why replacing a 2 by a 4 is a real new step; they are not a claim that no other method can reach four.

[Kalmynin–Konyagin, arXiv:2302.00459v1](https://arxiv.org/pdf/2302.00459v1), introduction, definition of j_f, Theorem 1: their translated **polynomial sequence** x+f(i) is a different restriction from arbitrary paired classes at each prime. The title alone is not evidence that their result covers C4.

The publisher attempt for Iwaniec (1978) returned HTTP 202 with zero bytes; its PDF could not be read. The historical one-class attribution is supplied by J's read introduction, not represented as a fresh reading of Iwaniec. All failures remain in the receipts. The exact external versions have hashed local copies. No exhaustive literature survey or worldwide-priority claim is made; no successful theorem is being nominated on the basis of an absent search hit.

## 4. A fully proved transfer and the unpaid cutoff estimate

For real z large set

    L=log z,   M=log log z,   H(z)=floor(z⁴/L⁴),

and saturate the local restrictions: one forbidden residue at 2 and **two distinct** residues at each odd prime ≤z. Let S₂(z;R) count survivors in [1,H(z)]. Saturation is legitimate for lower bounds because filling missing restrictions only deletes points.

The following would suffice, but is **not proved**:

    ∃ c₀>0,z₀ ∀ z≥z₀ ∀ saturated R:
       S₂(z;R) ≥ c₀ H(z) M / L³.                         (BG4 — OPEN)

BG4 is a specified sufficient route, not a necessary condition or an equivalent restatement of C4. It is not inserted as a new axiom and then advertised as a solved conditional frontier theorem.

### 4.1 Two-class upper bound on a large-prime progression

Put X=H(z)/z. For every prime q>z, every residue b mod q, and every saturated small-prime system R, the points of [1,H(z)] in that q-class which survive R number at most

    C X/(log X)²                                                (4.1)

for all sufficiently large z, with an absolute C, independent of q,b,R. This also covers q>H(z).

**Proof.** Their q-progression coordinate interval has length at most X+1; enclose it in a consecutive interval of integer coordinates of length J=ceil X+2. Choose a fixed small θ>0 and sieve these coordinates at primes ≤u=z^θ. The step q is invertible at all these primes, so there is one bad coordinate at 2 and two distinct bad coordinates at each odd sieve prime. An intersection indexed by squarefree d has count

    J ν(d)/d + r_d,   |r_d| ≤ ν(d),   ν(d)≤2^ω(d).

Use J's `lem:fundamental` at level D=J^(1/2). Since log J∼3 log z, its parameter s=log D/log u tends to 3/(2θ); θ can be fixed small enough for the stated upper estimate. For an absolute integer m large enough, its weighted remainder sum is at most

    ∑_{d≤D, squarefree} τ(d)^C 2^ω(d)
      ≤ ∑_{d≤D} τ_m(d) ≤ D(1+log D)^(m−1).

The last inequality follows by counting ordered factorizations and successively using the harmonic sum. The remainder is o(J/(log u)²). The local product is

    V₂(u)=(1/2)∏_{3≤p≤u}(1−2/p) ≍ 1/(log u)²,

because (1−2/p)=(1−1/p)²(1−1/(p−1)²), and the last product converges to a positive constant. Thus the upper count is O(J/(log u)²)=O(X/(log X)²). All endpoint errors are uniform. Enclosing a progression remains valid even when its original intersection has at most one point. ∎

### 4.2 Transfer theorem

**Proposition (complete, technical).** BG4 would imply the stronger estimate

    G₂(k) ≪ k⁴/(log log(3k))⁴,                           (4.2)

and hence C4, with absolute constants.

**Proof.** For k large write ℓ=log k and m=log log k. Fix a large absolute A, subsequently chosen, and set z=A kℓ/m. Translate an arbitrary interval of H(z) integers to [1,H(z)]. Include its actual restrictions at primes p≤z and fill each to a saturated system; impose arbitrary saturated restrictions at missing small primes. BG4 leaves at least c₀HM/L³ points. Each actual prime q>z removes at most two classes, each costing (4.1). Thus all remaining restrictions delete at most 2CkX/(log X)² points. Their ratio to the lower count is

    ≤ (2C/c₀) k L³ / (z M (log X)²)
       = (2C/(9c₀A)) + o(1),

since L∼ℓ, M∼m, log X∼3ℓ. Choose A sufficiently large once and for all. The ratio is then <1 for all sufficiently large k, uniformly in all actual prime sets, classes and translations. A survivor remains. Moreover H(z)∼A⁴k⁴/m⁴, proving (4.2) for large k.

For completeness the finite k range has a uniform bound independent of prime sizes. Inclusion–exclusion and CRT give, for r≤k primes and any interval of length T,

    |S−T∏_{p∈P}(1−|R_p|/p)| ≤ ∏_{p∈P}(1+|R_p|) ≤ 3^k.

The product is at least 1/((k+1)(k+2)): if 2 is present, order the other primes and use p_j≥j+1 to obtain at least 1/(r(r+1)); if 2 is absent use p_j≥j+2 to obtain at least 2/((r+1)(r+2)). Empty restrictions only increase the product; r=0 is immediate. Consequently T=(k+1)(k+2)(3^k+1) always suffices. This absorbs every bounded k into the constant in (4.2), since log log(3k)>0. ∎

This proof pays the large-prime tail, the entire residue/translation uniformity and the finite range. **It does not pay BG4.** The outer transfer is a dimension-two version of a classical sieve assembly, not a new substantial result.

As an additional check, the stipulated dimension-two fundamental lemma proves S₂(z;R)≳H/(log z)² at H=floor(z^B) for some sufficiently large absolute B: take level H^(1/2), fix B so that the relative fundamental-lemma error is <1/4, and use the displayed divisor remainder. The same tail argument at z=Ak proves G₂(k)≪k^B. This is a routine polynomial bound. Neither optimizing an unspecified B nor reporting that baseline as a new result would solve C4.

## 5. Attack on the new step: exact tree, failed tensoring, and limits

### 5.1 What survives from the one-class tree

Fix w<z. For a squarefree d supported on primes in (w,z], let N_d count n∈[1,H] which hit the local forbidden **set** at every p∣d and avoid it at every p≤w. Let S_d(b) additionally avoid all available primes w<p≤w^b smaller than the last prime in d. Partition the discarded integers by their least bad available prime. Exactly as an integer identity,

    S_d(b)=N_d−∑_{p available} S_{dp}(log_w p).            (5.1)

The local alternatives at the least bad prime are disjoint, so no missing multiplicity occurs in (5.1). Even/odd truncation and prefix-free stopping still give the same signed lower/upper inequalities. This part requires no conjectural randomness.

However, the correct reference mass is now

    μ_d=(H/d)V₂(w) 2^ω(d),   μ_{dp}/μ_d=2/p,

and not the source's (H/d)V₀ and 1/p. Summing unrestricted prefix weights gives exactly

    ∑_{d|∏_{w<p≤z}p} 2^ω(d)/d = ∏_{w<p≤z}(1+2/p) ≍ (log z/log w)².     (5.2)

J's corresponding one-class mass has order log z/log w. Thus its original reference function, rational-list exceptions, harmonic occupation measure and hard-stopping coverage do not apply unchanged. One can split N_d into 2^ω(d) CRT branches and apply a progression bound to each branch; summing their individual absolute errors does **not** restore the one-class total path measure. The source's reference margin is only proved for its 1/p recursion at ratio two. At H=z⁴/(log z)⁴ its original state definition starts near ratio four, and doubling each transition changes the recursion anyway.

An exploratory floating-point evaluation of the *unchanged admission rule* with doubled transition weights, fixed w=2 and H=z⁴, remained positive through z=397. Those finite computations have no asymptotic implication and do not establish BG4. Their code/values are isolated in `diagnostics/reference_probe.py` and `diagnostics/reference-probe.json`; they were not used in any proof. In particular this note makes no unsupported assertion that the doubled reference is negative, or that its positivity would suffice without an actual/reference comparison.

### 5.2 Two arithmetic obstructions to proposed bridges

First, one-class survivor counts cannot simply be intersected. In the actual interval [1,4], the classes {0 mod 2, 0 mod 3} leave {1}, and {0 mod 2, 1 mod 3} leave {3}. Each scalar system has a survivor but the proper two-class system {0 mod 2, {0,1} mod 3} has none in that interval. This refutes that intersection inference; it is **not** a counterexample to C4 for an unspecified absolute C.

More generally, label the two distinct forbidden roots at each odd prime by 0,1. After conditioning on the allowed parity, averaging scalar survivor counts over independent choices of a single label gives

    2^(−r) ∑_{σ∈{0,1}^r} S_σ = ∑_n 2^(−m(n)),         (5.3)

where m(n) is the number of these primes at which n hits either root. The desired joint survivor count is #{m(n)=0}. The positive contributions with m(n)>0 remain in (5.3). The example above realizes this failure arithmetically; replacing it by an abstract stationary process is unnecessary.

Second, signed pointwise sieve lower bounds do not multiply. Let p=(3,5,7,11), first labels (0,0,1,1), second labels (1,1,0,0), and n=0. For layer i the first Bonferroni lower function L_i=1−number of hits is always ≤ its survivor indicator. Here both L_i=−1, so L₁L₂=1 while the joint survivor indicator is zero. This is a genuine residue-system counterexample to the proposed algebraic inequality, not to the quartic target. It explains the need for a new joint comparison rather than multiplying two scalar signed constructions.

### 5.3 Precise remaining gap

I have not proved a positive two-class reference margin with a valid comparison of actual short-progressions to that reference at H=z⁴/(log z)⁴. Nor have I supplied an alternative bound directly implying C4. In a tree route one must prove both:

* a suitable dimension-two reference lower contribution on the BG4 scale;
* a rational/list/stopping comparison controlling **two-label** discrepancies in the changed path measure, with all constants uniform in the arbitrary local pairs.

The source's allowance g(p)≤2/p in the fundamental lemma pays long progression estimates, not these critical-scale operations. Its one-class inverse/stopping theorem and its B⁻² margin cannot be relabelled to pay them. BG4 packages these unpaid operations in a single explicit sufficient analytic assertion. It might be possible to prove C4 by a different route without BG4. No arithmetic counterexample to either C4 or BG4 has been found.

## 6. A proved screening theorem, excluded as routine

Let fixed h∈Z[t] have degree ≥2 and positive leading coefficient. Define condition SF(h): for every rational prime p there is α_p∈Z_p with

    h(α_p)=0,    v_p(α_p)≤1.

The valuation condition excludes α_p=0. Then, using pinned P,

    SF(h) ⇒ ∃ c_h,C_h>0 ∀N ∀A⊆[N]:
    (A−A)∩{h(n): n≥1 squarefree}⊆{0}
       ⇒ |A|≤C_h N^(1−c_h).                             (6.1)

If SF(h) fails, there is a fixed positive-density arithmetic progression avoiding all these nonzero values. Thus SF(h) is also necessary for qualitative density decay.

**Complete proof.** Write h(t)=t^e g(t), g(0)≠0. A root α_p allowed by SF is nonzero and therefore a root of g. For p∤g(0), every integral root of g is a p-adic unit. Among the finitely many p∣g(0), prefer a unit root if one exists; otherwise SF provides a root of valuation exactly one. Let D be the squarefree product of those latter primes. For every p a chosen root α_p divided by D is a unit in Z_p, and h(D(α_p/D))=0. Hence F(t)=h(Dt) has a unit p-adic root at every prime. Compactness/CRT makes this equivalent to the unit root modulo every integer required by P. F has the same degree and positive leading coefficient.

If p∤D, Dp is squarefree, so an A as in (6.1) avoids every nonzero F(p) with p∤D. The exceptional primes p∣D are finite. Choose a positive integer Q larger than the absolute values of their nonzero F(p). Each set A∩(r+QZ) then avoids those exceptional values as differences too, and therefore avoids **all** nonzero F(p). Apply P to each of the Q subsets of [N] and sum. This yields (6.1), with constants depending only on h. Zero exceptional values impose no condition, exactly as in P.

Conversely suppose SF fails at p. The compact sets

    K_j={x∈Z_p : x∉p²Z_p, h(x)∈p^j Z_p}

are nested and closed. If all were nonempty, compactness would give an allowed p-adic root. Thus some K_j is empty. For every squarefree positive n, h(n) is not divisible by p^j. The set p^j Z∩[N] consequently avoids all such values as differences, and has limiting density 1/p^j. This proves necessity. ∎

For h(t)=t(t−2) the dilation is D=2; for h(t)=(t−2)² it is again 2. For h(t)=t² condition SF fails: already modulo 16 its roots are all divisible by 4, so 16Z avoids squares of squarefree arguments. These are actual arithmetic examples. The proof handles h(0)=0, finite exceptional prime arguments, zero values and all N; no limiting prime-distribution claim was smuggled in.

[Rice, arXiv:1111.6559v1](https://arxiv.org/pdf/1111.6559v1), Definition 1 and Theorem 1, already gives the unit-root characterization at prime arguments with its stated weaker logarithmic-iterated bound; its §2.1 develops the compatible p-adic auxiliary family. The retained v1 is not silently substituted for the stronger bound in the final 2013 version cited by P. Here the power saving is entirely the stipulated newer P input. Finite dilation, compactness and a bounded partition are routine, so (6.1) is not offered as the missing substantial result or as a second finding.

## 7. Reproduction, manifests, rights, and handoff

Run from this assigned folder:

    python3 -B diagnostics/check.py
    python3 -B diagnostics/verify.py

The first script performs exact CRT, endpoint, cyclic-gap, tree-partition, label-average and signed-lower checks, plus finite root/dilation checks. `diagnostics/results.json` is its retained output. The second script is offline and read-only: it authenticates the input/source/output manifests, verifies every upstream Git object against the frozen complete tree, and reruns the exact finite checks. It does not claim to certify BG4, C4, asymptotic mathematics, novelty or independent review. The floating-point reference exploration is explicitly separate.

`inputs/context-manifest.json` freezes the required context and relevant selected historical records. `sources/manifest.json` authenticates pinned source copies. `literature/retrieval*.json` preserve versions, bytes, statuses and failures; `reading.json` records actual selected reading extents and visual checks. `input-manifest.json` lists all retained inputs, including external versions and failed zero-byte response. `output-manifest.json` lists authored deliverables. `seal.json` binds all owned files except itself; its detached digest is in the handoff. A seal is an integrity receipt, not an independent mathematical review.

Original prose is CC BY 4.0; original code is MIT, copyright 2026 Myeongjin Kang. See `RIGHTS.md`. All copied upstream and external sources, extracted text, and rendered source pages retain their respective authors' rights. They are private reading/provenance caches, not relicensed or proposed publication payloads. The primary papers' authorship is not attributed to this note's author.

No shared edits, stages, commits, public uploads/messages, nested agents or count changes were made. The parent can retain the exact BG4 gap and the technical lemmas, or commission a new proof attack. There is **no valid substantial candidate here to send to manuscript or formal gates**.
