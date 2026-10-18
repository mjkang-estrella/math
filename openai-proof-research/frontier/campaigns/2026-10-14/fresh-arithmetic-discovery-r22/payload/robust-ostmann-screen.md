# Robust Ostmann screen: unchanged full target unresolved

Original analysis: Myeongjin Kang, no affiliation. Original prose CC BY 4.0.
Source manuscripts are private third-party material. No upload or nomination.

## Target and chronology

Selected after reading family013's actual introduction/conclusion and checking I99's bounded screen. For every A,B⊆N₀ with |A|,|B|≥2, rule out

    E(x)=|((A+B) △ P)∩[0,x]| = o(π(x)).                 (T013R)

Equivalently, each such pair should have limsup E(x)/π(x)>0. No uniform positive constant, bound on representation counts, finiteness of either summand, prime-only sumset inclusion, or quantitative rate in the little-o is assumed. This is a proposed full target, not a theorem freeze or claim that the target is true. No counterexample to T013R was obtained. Source013 proves finite symmetric difference impossible, which is stipulated true. Its proof is not being audited.

The actual target was communicated to the parent before extensive operative-body reading. Subsequent finite-factor and contamination lemmas are technical support only; neither replaces the target.

## A complete finite-factor check, including zero

Let A be a finite subset of N₀ of size at least two and let B be arbitrary. Put D=max A−min A≥1. Then

    |((A+B) △ P)∩[0,x]| ≥ π(x)−O_D(x/log²x)−O_D(1).   (1)

Here and below the implied constants may depend on fixed shifts. This proves liminf E(x)/π(x)≥1 for finite A, including A={0,h}. The symmetric assertion holds for finite B.

Proof. Call a prime p≤x−D isolated if there is no distinct prime p′ with |p−p′|≤2D. The fixed-two-shift upper-bound sieve gives O_D(x/log²x) nonisolated primes (sum over the finitely many nonzero shifts of magnitude ≤2D). Hence the number I(x) of isolated primes is at least π(x)−O_D(x/log²x)−O_D(1).

Partition these primes into those missing from A+B and those covered. Each missing prime is an error. For each covered isolated prime choose a representation p=a+b. Choose a′∈A with a′≠a. Then q=a′+b belongs to A+B, satisfies 0≤q≤x and 0<|q−p|≤D, and is not prime by isolation. If the q chosen from p and p′ were equal, then |p−p′|≤2D, contrary to isolation. Thus the covered isolated primes inject into the nonprime errors. Missing-prime errors and nonprime errors are disjoint, so E(x)≥I(x). This also handles q=0 or 1: they are nonprime errors, without calling them composite. ∎

This is a routine fixed-shift sieve consequence, not a substantial new nominee. The finite injection has a useful elementary formal interface: for any marked subset P of N₀, isolated marked points covered by a sumset with bounded-diameter nontrivial A inject into unmarked sumset points. Number theory is needed only to show almost all primes are isolated at a fixed radius.

## Necessary bounds for a hypothetical full-scope counterexample

Write C(x)=|((A+B)\P)∩[0,x]| for nonprime errors and M(x)=|(P\(A+B))∩[0,x]| for missing primes. Suppose E=o(π). Fix two distinct a₀,a₁∈A. Every b≤x either makes both b+aᵢ prime or makes at least one b+aᵢ a nonprime error. For a fixed i, translation injects these b into the errors at x+max(a₀,a₁). Consequently

    B(x) ≤ O_{a₀,a₁}(x/log²x)+2 C(x+max(a₀,a₁)) = o(π(x)).   (2)

The same argument gives A(x)=o(π(x)). This argument permits 0 in either summand. Together with (1), any counterexample must have both summands infinite, and removing any fixed finite subset from either summand loses only o(π(x)) represented primes. It does NOT give the source square-root bounds. In particular it does not justify removing initial segments of length √x or applying source collision stability with point masses O(log^b x/√x).

## Sparse contamination gives a precise boundary for literal support arguments

The following conditional lemma is an obstruction to importing the source's literal support conclusion, not a counterexample to T013R.

If a pair A,B satisfies E=o(π), there is an infinite C⊆N₀ such that A′=A∪C and B′=B∪C still satisfy E′=o(π), while C (and hence A′ and B′) meets every residue class modulo every prime infinitely often. Thus both tail supports are full modulo every prime.

Proof. Enumerate pairs (p,r), p prime and 0≤r<p, so that each occurs infinitely often. By (2), for each j≥1 choose a threshold T_j such that

    j(A(x)+B(x))+j² ≤ π(x)/j       for every real x≥T_j.

This is possible because A+B=o(π) at the counting-function level and π(x)→∞. Choose integers c_j strictly increasing, with c_j≥T_j and c_j congruent to the jth prescribed residue. Set C={c_j}. If c_j≤x<c_{j+1}, nonnegativity implies the number of new sums at most x is at most

    |(C+A)∩[0,x]|+|(C+B)∩[0,x]|+|(C+C)∩[0,x]|
    ≤ j(A(x)+B(x))+j² ≤ π(x)/j.

Since j→∞ as x→∞, these new sums are o(π). Enlarging the sumset cannot create new missing primes; it creates at most the stated number of new nonprime errors. Therefore E′=o(π). Each prescribed residue recurs arbitrarily far out. ∎

One may additionally make j=o(A(c_j)),o(B(c_j)) by enlarging thresholds, since both sets are infinite. Thus this lemma does not rule out removing a negligibly small contaminating set. A cleaning theorem could still work. It DOES show why a proof that simply asserts disjoint literal tail supports from the robust hypothesis has not addressed the necessary change of objects.

## First failed source interface: exact avoidance and pair mass

In source013 §02, eventual exclusion of all composite sums yields a partition S_p⊔S_p^c=F_p containing the A-tail and −B-tail supports. This is used in lem:size to get square-root summand bounds and in lem:collision to write the exact identities

    ||μ_p−U_{S_p}||² = ||μ_p||²−1/|S_p|,
    ||ν_p−U_{S_p^c}||² = ||ν_p||²−1/|S_p^c|.

The sum of these plus the reciprocal-support deficit is nonnegative, with an O(log log X) budget. Under T013R's contrary hypothesis, only cardinality of the nonprime sum set is controlled. If r_X(n) counts representations by A∩[0,X], B∩[0,X], the bad-pair mass is

    Σ_{n≤2X, n∉P} r_X(n),

not C(2X). The elementary bound is at most C(2X) min(A(X),B(X)); normalized by A(X)B(X), this only gives C(2X)/max(A(X),B(X)). Both denominator counts are o(π(X)) by (2), so C=o(π) does not make that bound small. No estimate in the read source operations fixes this scale mismatch.

Even replacing pair counts by a graph cannot delete all bad edges at a cost bounded just by the number of distinct sums: each fixed sum labels a matching, and different bad sums can together support a dense bad graph. The finite diagnostic A=B={0,...,m−1}, all labels 0,...,2m−2 marked bad, has 2m−1 labels and m² bad pairs. Embedded in ambient X=m³, 2m−1=o(X/log X), yet every pair is bad. This example has NO prime coverage and is NOT a counterexample to T013R; it only falsifies the bare cardinality-to-normalized-pair inference.

A viable extension needs a theorem that, using actual near-prime coverage as well as sparse errors, constructs cleaned or weighted summands with enough retained prime coverage, sufficiently small bad-pair mass, and a replacement for the complementary-support collision budget. No such theorem has been proved here. Restricting representation counts would change T013R and is not accepted as a substitute.

## Independent failed interface: sparse missing primes versus a growing weight

Source013 §05, prop:supply, sets X=exp(exp L), R=√X and K=ceil(C_K L). From alleged Fourier sparsity it builds

    W(n)=(Σ_{I⊆S, |I|≤K} ∏_{p∈I} b_p(n))² ≥0,
    U=exp(O(ε₀L))>0.

Its exact prime mean eq:src34 is

    Σ_{p prime} (log p) φ(p/X) W(p) = (1+o(1)) U X ∫φ.

The pointwise bound used at the coverage step is

    ||W||∞ ≤ exp(O(K exp(.9L))) = X^{o(1)}.

Exact prime coverage lets every relevant prime supply a pair, after deleting only X^{3/4+o(1)} boundary primes using square-root summand bounds. Under E=o(π), the extra missing-prime error admits only

    Σ_{p missing} (log p) φ(p/X)W(p)
    ≤ ||φ||∞ log X · ||W||∞ M(X).

To make this o(UX) from this bound requires

    (M(X)/π(X)) · ||W||∞/U →0.                  (3)

M=o(π) alone does not imply (3), since its rate can be arbitrarily slow. This is insufficiency of this particular bound, not proof that the actual W must concentrate on the missing primes. A useful repair would be uniform integrability of W/U on the prime measure (or another bounded witness with adequate contraction); no such estimate is established here. Replacing W by min(W,H U) requires a lower bound for the clipped prime mean uniform in L; positivity alone does not give it. Even such a repair would leave the separate residue/pair-mass and square-root-size interfaces unpaid.

The final §09 tree symmetrization is not itself the first obstruction. Its fixed depth k and later limit L→∞ do not freeze §05's growing prime set or turn arbitrary o(1) into the rate in (3). The optional zero-free refinement in §05 improves prime-distribution errors; it does not address either distinct bad sums or arbitrary missing-prime sets.

## Actual primary comparison and contribution status

Elsholtz–Harper, arXiv:1309.0593v1, Theorem 2.6 and §7, first bound ν_B(p)≤p−ν_A(p) using that no sum is divisible by p. Their reciprocal-support inequality and large-sieve denominator/Hildebrand estimate depend on this exact exclusion. §3.4 allows a reasonably large subset of the target, but still insists the entire sumset lies inside the sieve target; Theorem 4.1 explicitly assumes every target element avoids the selected primes. This handles omission of target elements under exact avoidance, not composite contamination of o(π) cardinality.

Croot–Elsholtz, arXiv:math/0209137v1, has a different ternary thin-prime theorem. Its definition of regularity controls the total representation mass above a polylogarithmic multiplicity threshold. Theorem 1 assumes a regular triple and an entirely prime sumset. In §7, Proposition 3 begins with this tail-mass inequality, then uses random thinning to obtain many distinct sums. The starting inequality is an assumption unavailable under T013R. Invoking the thinning argument without it would silently add the missing hypothesis. It does not settle T013R or justify a bounded-representation replacement.

I99 previously recorded that the source lower bound retains exact coverage/fixed decomposition data and did not nominate a robustness theorem. It is a bounded prior screen, not a developed full proof. The present screen supplies a complete finite-factor bound, the conditional contamination construction, and the two distinct failed interfaces. These are useful technical diagnostics, not a substantial full-scope result, priority claim, or candidate for the campaign count.

Status: FULL TARGET UNRESOLVED; NO NOMINATION; ZERO COUNT. Stop this mechanism at the identified boundaries rather than promote the finite-factor lemma or add regularity hypotheses. A fresh eligible family is the next discovery task.
