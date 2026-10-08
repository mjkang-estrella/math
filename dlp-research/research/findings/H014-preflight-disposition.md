# H014 pre-run corrections: admission and symmetry-aware controls

2026-10-08. Native Astra proposed protocol; separate Claude Opus reviewed;
root checked mathematics and revised BEFORE any numerical execution. Raw review
retained. This is a qualitative information-source screen, not a solver benchmark.

## Deterministic admission bug caught before running

At p43, Hasse plus q=7 mod12 and q!=p leave q31 only. Then t13 and
t^2-4p=-3. The order Z[pi] already has maximal discriminant-3, so
Z[pi]=End(E)=O_(Q(sqrt(-3))). Its order-six units give extra geometric
automorphisms, forcing j0 and a0 in characteristic43. Thus no curve allowed by
the original nonzero-a rule can pass. Root checked the endomorphism-ring
inclusions in [Sutherland, Theorem15.6](https://math.mit.edu/classes/18.783/2013/LectureNotes15.pdf)
and the short-Weierstrass isomorphism classification there. No runtime needed.

Root replaces p43 by p59 before the run: compatible q67 has discriminant-187,
so this particular contradiction is absent. This is not a guarantee a permitted
curve occurs in the lexicographic window. Fields are now59,101,251,256 candidates
per field, each admission failure recorded without skipping other frozen fields.
The single global cap still terminates all work. No post-outcome selection/reset.
Reviewer class-number hit probabilities and the quoted10k events per curve were
unvalidated estimates, NOT adopted as certified counts or runtime predictions.

## Correct null model and exact encoding

Both frozen features and chi6 are odd, so opposite scalar summands agree.
Unpaired label permutations destroy that symmetry. Replace them by permutations
of opposite pairs plus independent orientation signs; the implemented PRNG
provides reproducible controls, not a probability guarantee. Under the separate
ideal uniform signed-pair model, cross terms vanish and

    E|c_null|^2 = 4*sum_(half representatives)|f|^2/(q-1)^2
                = 2*sum_(all nonzero points)|f|^2/(q-1)^2.

Report the exact rational value. The frozen3RMS flag compares |c|^2 to nine
times that value; it is descriptive, not a three-seed significance test. Zeros
remain in both sums. Character, feature and planted controls are fixed point
functions when changing G; generator rotations are algebraic checks, not new
independent data. Source/protocol specify the exact LCG/rejection/permutation.

Reviewer ring arithmetic and phase mapping accepted. Two broader raw comments
are corrected: if h even, f_par is EVEN with chi, not automatically an odd-null
feature. And a j0 order-three automorphism forces zero only when chi acts
nontrivially on that automorphism; h divisible3 can defeat that particular null.
Neither issue affects the frozen h odd, nonzero-a,b family.

## Relation to the actual main goal

No scalar-search backend with one cheap addition per multiplicative step is
supplied. The m6 coset-size factor3 over negation is a cardinality observation;
fixed-base scalar multiplication, fine calibration and features can erase it.
No full-size improvement is predicted from m6 alone. Do not describe tiny signal
as a fast attack. Fixed m and a log-growing backend cost cannot yield an exponent
improvement. The probe concerns whether this concrete feature FAMILY offers any
signal worth further analysis at useful orders m, not whether enumeration wins.

Native Sol independently checked the conditional scaling calculation: if
m=q^delta divides q-1 along the claimed family, signal=q^(-beta), and all
evaluation/setup/training costs really fit their paid bounds, then phase
sampling is q^(2delta+2beta) up to logarithms and explicit coset BSGS costs
q^((1-delta)/2) up to logarithms. Balancing gives delta=(1-4beta)/5 and exponent
(2+2beta)/5, potentially below1/2 only for beta<1/4. This is a conditional cost
identity, NOT an algorithm or evidence of such signal/divisors. Character-table
space q^delta and explicit baby-table space q^((1-delta)/2) remain; balanced
space is q^((2+2beta)/5). Lower memory needs a separately justified algorithm.
If an available automorphism group has size a and intersection with kerchi has
size t, the state-space ratio is m*t/a, not m automatically. This corrects the
earlier m2 direction and prevents double-crediting negation.

Code is under independent ownership and numerical execution remains pending
root inspection/review. Any cap failure remains a result, not a reset request.
