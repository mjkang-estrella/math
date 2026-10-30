# discovery.md — pi-bbk-full-refinement-r3

## Mathematical discoveries (in order of certainty)

### 1. COMPLETE PROOFS: G_{4,n} ⪰ 0 and G_{5,n} ⪰ 0 for all n ≥ 0 (2026-10-29)

The k = 4 and k = 5 rows of BBK Conjecture 5.1 are fully proved for all n; by Lemma 5.3 symmetry this covers {k ≤ 5} ∪ {n ≤ 4}. Method: exact quasi-polynomial certificate machines (full details, proofs of every lemma: `PROOF-K4-K5.md`). Highlights:

- **Prop 2.2 (proved):** h₁₃₅(15Q+r) = (15/2)Q² + ((2r+9)/2)Q + h₁₃₅(r), via two counting lemmas: r_{3,5}(v) − r_{3,5}(v−15) = 1 (v ≥ 15) and h(x+15) − h(x) = Σ_{v=x+1}^{x+15} r_{3,5}(v).
- **Cubic analogue for h₁,₃,₅,₇** with period 105 (Prop 2.3), exact for all Q.
- **Newton certificates:** forward-difference data ≥ 0 on each residue class ⇒ nonnegativity on the whole ray/quadrant/wedge (exact expansions).
- Certificate counts: k=4: 15 classes (regime A3) + 225 (A4). k=5: 11025 (tail quadrant) + 2·11025 (wedges B4/B7) + 4×11025 (slabs). **All pass; minimum data value 0 (attained, never negative).**
- Cross-validation: cubic/quadratic data vs series (all residues, Q ≤ 9 / Q ≤ 20); T₅ vs directly computed G_{5,n} series: 27 009/27 009.

**Significance:** first proofs of any infinite sub-family of Conjecture 5.1 beyond the trivial rows; the source's own §5 stops at computation. Also proves the row/column n = 3, 4 and the previously only-numerical h-superadditivity lemma.

### 2. RIGOROUS NEGATIVE: sub-object positivity is false

(1−q⁷)/((1−q³)(1−q⁵)) has coefficient −1 at q⁷ (`checks/run2_subobjects.py`). Consequences: no monotone induction through sub-objects; Conjecture 5.4-type decompositions cannot hold sub-objectwise (they may still hold for the full G). Note G_{4,2} itself (min coeff −5640 up to deg 400… wait — corrected: G_{4,2} is a k=4 object and is **now proved ⪰ 0**; the earlier −5640 was a bug from reading product tails beyond the truncated inverse, fixed in `run3`).

### 3. Divisor matching: characterized, partial

Injective a ↦ b with b | a exists for most (M, m) but fails for 229 pairs with M < 4m+2 (list in `run2` log). Where it exists it gives a proof; it is strictly weaker than the certificate machine.

### 4. k = 6 reconnaissance

Same machine, tail quadrant, 225-class sample (`run9`): 0 failures. Full k = 6 needs ≈10¹⁰ exact ops (compiled code); no mathematical obstruction observed.

### 5. Stronger-form status (inherited + confirmed framing)

The stronger pre-division form H is false (H_{3,5} negative; inherited from pi-discrete-discovery-r7). Conjecture 5.2 (differences) remains open and stronger.

## Open gap (precise)

Conjecture 5.1 for **k ≥ 6 ∧ n ≥ 5**. The certificate machine applies formally; obstacles are computational scale only, as far as current evidence goes.
