# H039 exact arithmetic report — raw testimony

Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h039-arithmetic-operators-opus-20261008-r1`

Provider/model: claudeAgent/claude-opus-5-5. COMPLETED, no pending children.
No new primary source was read. Root qualifications remain separate; this
report does not establish its proposed universal exclusions or concrete costs.

I found no mechanism in this lens that survives as a card for credible full-range exponent or material complete-work gain. I checked six genuinely different mechanisms; each fails a paper falsifier or reduces to an existing record. Nothing new is admitted for experiment. Best supported exponent stays 1/2, and verified improvement is NONE.

Scope: read-only. I read RESEARCH_LOOP.md, RESEARCH_TEAM.md, research/STATE.md and the dispositions for H003, H006, H019, H021, H022, H026, H036 and H038. I read no other H039 proposals. No runs, imports, edits, files, children or web fetches, so **no new primary source was read in this task**. Prior-art pointers below are to sources already opened in earlier dispositions, or are marked as recalled.

## M1. Polynomial-valued symmetric translation operator (exact identity, no gain)

- **Operator (public input):** Take F(Y)=∏(Y−y_i) with y_i=x(P_i), and c=x(C). Define T_c(F)(X)=Res_Y(F(Y), S3(X,Y,c)), which equals ∏_i (y_i−c)²(X−x(P_i+C))(X−x(P_i−C)).
  - When y_i=c, S3(X,c,c)=−4(c³+ac+b)(X−x(2C)) and the other root is O; these cases need explicit handling.
  - S3 has degree 2 in Y, so T_c can be computed by reducing F modulo S3 over F_p[X] using divide and conquer. My upper estimate is Õ(deg F) field operations; no reviewer has checked it.
  - Composing T_{x(2^{k-1}H)}∘…∘T_{x(2H)} on (X−x(H)) gives the polynomial whose roots are x(jH) for odd |j|<2^k. That is an interval root polynomial built from k field elements, with no point enumeration.
- **Why there is no gain:** The dense result still costs Õ(N), the same as a product tree. Evaluating the composition at a target expands into 2^k leaves. This is the same expansion objection as H003 D3 ("short recursive notation is not cheap evaluation") and gives the H019/H026 Õ(√q) route.
- **Prior art:** It reproduces the H019 resultant and the H025 dyadic identity in polynomial-valued form. It is not a new primitive.
- **Cheapest falsifier:** The paper argument above: evaluating the depth-k composition at one point needs 2^{k−1} norm factors unless a separate identity collapses them. None is known.

## M2. CM endomorphisms as cheap orbit maps (scoped negative, extends H003/H036)

- **Idea:** Find α∈End(E) with α≡ζ (mod 𝔮), where 𝔮=(q,π−1) and ζ has small order m. Then α acts on E(F_p) as an automorphism of order m. Rho over α-classes would gain √m.
- **Why it fails:**
  - Every element of Z[π] acts on E(F_p) as the integer a+b. Elements outside Z[π] act as (a+b)/f, where f divides the conductor index.
  - The H036 norm lemma gives deg α ≥ |D_O|/4 for non-integers. For a generic curve that is about p, and my coset-count heuristic suggests about q√p for the required residue class.
  - Evaluating α as a smooth isogeny chain needs at least log_B(|D_O|/4) steps.
  - With orbit canonicalization the work ratio is (1+(m−1)C_α/C_A)/√m. Gain needs C_α < C_A/(√m+1), which is under ~3M for m≥4. A 256-bit chain with B≈2^8 has ≥32 steps, so it cannot meet this.
- **Scope:** This rejects isogeny-chain evaluation only. A compact non-chain straight-line program for a degree-≥|D_O|/4 map that beats scalar multiplication would reopen it; none is known.
- **Prior art:** Duursma–Gaudry–Morain and Wiener–Zuccherato (recalled); H003 already states that a giant multiplier costs a scalar multiplication unless a cheap map is supplied.

## M3. Multiplicative-coset abscissa sets (rejected)

- **Idea:** V_n={P : x(P)^n=d}. It has about n points, can be enumerated from n-th roots, and membership costs one O(log n) exponentiation with no table.
- **Why it fails:** It is a distinguished-point set with a structured definition. The multiplicative structure of x gives no relation between the logs of V_n elements: neither the Weierstrass nor the Montgomery x(P±R) identity preserves the coset. Matching both sides needs about √n hits at q/n tests each, so q/√n ≥ √q. This agrees with H038's bounded-recovery lemma (B·n=Ω(q)).
- **Montgomery note:** Translation by the 2-torsion point T₀ inverts x, but it only moves between cosets and does not exist on prime-order curves.

## M4. Ring-extension, lift and auxiliary-pairing bridges (rejected; one line)

Several possible bridges all reduce to a homomorphism from Z/q into a group of coprime order, which must be trivial (consistent with H022): F_p[ε], Z/p² (Smart-type), Teichmüller or canonical lifts (the torsion lift has zero log), mod-ℓ Tate pairings and ℓ-adic data. The non-trivial versions are the ray-class/Galois action (H021: target conversion missing) and pairings with huge embedding degree (H003 D2).

## M5. Polynomial-method batch evaluation of the 3-list S3 predicate (rejected)

- **Idea:** Williams/Razborov–Smolensky-style batching of "is some S3(a_i,b_j,c_k)=0" over A×B×C with |A|=|B|=|C|=n≈q^{1/3}.
- **Why it fails:**
  - Each bit of a product mod p has degree close to the full bit-length as a polynomial over F_2, so no low-degree probabilistic polynomial exists.
  - Even the best analogous results for integer 3SUM save only polylog factors, which cannot close n² versus the n^{1.5}≈√q target.
  - Exact zero-counting via Σ S3^{p−1} needs a p×p×p coefficient tensor.

## M6. Folded elliptic AG codes / Riemann–Roch decoding (duplicate)

This is already covered by H006 (Cheng's equivalence, translation-folding objection). One sharpening: the needed agreement equals k exactly, which is the Singleton threshold itself. Guruswami–Sudan needs at least about √(n(m+1)), and capacity decoders need (R+ε)n. Nothing reopens.

## What would actually reopen this lens

A new evaluation identity that collapses composed translation norms. Concretely: evaluate T_{c_k}∘…∘T_{c_1}(F₀) at a single point using fewer than 2^{k/2} norm factors, with explicit zero/O handling and position recovery, and with those identities proved rather than assumed. Or a compact non-chain straight-line program for a CM endomorphism that costs less than C_A/(√m+1). I have neither, and stating them as wishes would just repeat the missing interval-product primitive.
