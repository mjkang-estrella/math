# Two-coordinate encoding: concrete unpaid interfaces

The full frozen target is unchanged. This is an author attempt, not a proof, counterexample or nominee.

## 1. What classical matrix packing actually provides

Pack a collection of self-adjoint entry coordinates into two Hermitian k-by-k matrices Z1,Z2 over a tracial algebra, using real diagonal entries and real/imaginary off-diagonal coordinates. There are2k² real entry slots. Additional slots can be filled with freely independent semicircular variables, but any entropy additivity invoked for these fillers must retain the original limsup convention. The source's gap tuple alone does not automatically give a specified all-matrix-size limit.

The actual Shlyakhtenko primary §5 relates entry entropy to entropy of the packed matrices RELATIVE to scalar Mk. Its exact formula is stated for matching ultrafilters; the ordinary-limsup statement printed there is a one-sided inequality. Neither removing conditioning nor replacing ultrafilter entropy by the original limsup entropy is an identity supplied by that theorem. The Nica–Shlyakhtenko–Speicher matrix theorem explicitly uses chi(Z|Mk)<=chi(Z). Its equality mechanism requires freeness from Mk, not arbitrary encodings.

Even granting a matching conditional gap, write schematically, whenever all four terms are finite,

 G_unconditional=G_relative+I_star-I_micro,
 I_star=chi_star(Z)-chi_star(Z:Mk),
 I_micro=chi(Z)-chi(Z|Mk).

The gap is preserved only if the excess I_micro-I_star is smaller than G_relative. No such estimate has been established. The sign chi<=chi_star alone gives no comparison of these two increments. With one packed self-adjoint variable unconditional chi=chi_star, so in every finite setting with a relative gap that increment difference cancels it exactly. This is a diagnostic against treating matrix compression as automatically gap-preserving; it is not a counterexample to the two-variable target.

## 2. Why direct spectral markers do not close it

One can put a finite-spectrum scalar marker D in the first matrix and store coefficients in blocks of the second. At zero perturbation the first variable has atoms, hence its one-variable microstates entropy is minus infinity and the pair cannot have finite chi. The matrix source finite-chi argument does apply after adding nonzero free semicircular noise to both encoded variables, provided bounded deterministic matrix models are retained. That proves only finiteness, not a positive gap.

For small noise, separated marker spectral bands remain recognizable in operator norm. Their spectral projections can identify coarse blocks, but recovering a full scalar matrix algebra additionally requires compatible off-diagonal partial isometries. Even if that recovery is proved, it does not bound I_micro-I_star above. The entropy of orbit directions and the analytic conjugate-variable cost of resolving the marker must be computed with the same noise scale. A generic generator theorem or source287's trace-preserving isomorphism supplies neither estimate.

The actual companion entropy-dimensions proof transports each tuple coordinatewise, preserving its joint law and its number of variables. It deliberately distinguishes algebraic generation from W*-generation. It therefore does not provide a quantitative entropy change under replacement by two generators.

## 3. A rigorous obstruction to transplanting the source block witness

Replace the source's p signal coordinates by a fixed r, while keeping an arbitrary fixed number q of blocks. Consider the same terminal event with equal variance v GUE coordinates:

 sum_i ||D_i||_(2,d)^2<=16vr,
 exists q orthogonal blocks of ranks<=2d/q with
 sum_i ||sum_l P_l D_i P_l||_(2,d)^2>=r/16.

For d>=q, partition an eigenbasis of D1 into q groups of sizes at most ceil(d/q)<=2d/q. The resulting blocks commute with D1, so the compressed energy is at least ||D1||_(2,d)^2. Under GUE this converges in probability to v, while the total tuple energy converges to rv. Thus whenever v>r/16, this event has probability tending to1. It cannot have probability exp(-c d²). In particular r=1 or2 with v>=1 is excluded, irrespective of how many blocks the marker names.

This is not merely a failure of the source's numerical unitary-net bound: the event itself is nonrare. The proof uses finite-dimensional spectral decomposition and GUE second-moment concentration. It applies only to this copied witness with its displayed threshold, not to all possible two-coordinate witnesses. Sharpening net constants or taking more marker blocks cannot fix it. A viable pair construction must use a stronger joint invariant than large energy in some block decomposition, or retain controlled information about the marker in the terminal event.

## 4. Concrete next estimate required

For a noisy packed pair, one needs either:

(a) a specified-ensemble terminal event whose GUE rate beats the analytic free-Fisher deficit, with joint marker and coefficient compatibility surviving noise; or
(b) matched small-noise expansions of microstates and nonmicrostates conditional-to-unconditional increments, accurate beyond the positive relative gap.

The source's positive-time ensemble lemma would then transfer an actual terminal deficit back to the initial pair, but an arbitrary terminal microstates law cannot replace its specified ensembles. No such event or matched expansion is proved here. The full target is retained; a conditional or many-variable statement will not be substituted.

## 5. Exact collapse of the simplest Gaussian-entry packing

Let k² freely independent variance-one semicircular variables provide a standard Hermitian Gaussian-entry matrix H: diagonal entries s_ii/sqrt(k), off-diagonal entries (s_ij+i t_ij)/sqrt(2k), and their adjoints. Let the entries lie in a tracial factor N. Put the scalar marker Y in a separate tensor factor, as in the source, and use normalized trace on Mk(N tensor W*(Y)). Then H and I_k tensor Y commute.

The scalar distribution of H is exactly variance-one semicircular for every k. A direct proof uses the free Wick expansion: every surviving pairing is noncrossing, and the entry covariance E(H_ij H_lm)=k^-1 delta_im delta_jl. For each noncrossing pairing of a cyclic word of length2a, the free-index summation contributes k^(a+1), the a covariance factors contribute k^-a, and normalized trace contributes k^-1. Each pairing therefore contributes1; odd moments vanish. The even moments are the Catalan numbers. This is an exact moment computation, not a large-k limit.

Since the Y factor is tensor independent, every mixed word in H,Y reduces by commutation to H^a Y^b and its trace is tau(H^a)tau(Y^b). Thus the joint scalar law is precisely (one variance-one semicircular B, the original central Y), independent of how many Gaussian entry slots were packed. Adding a freely independent semicircular pair at any fixed noise time preserves equality of these joint laws. No high-dimensional entropy gain can be inferred from this encoding. This does not assert that the resulting noisy commuting-signal pair has zero gap; it only removes the proposed dependence on the number of hidden Gaussian entries.

A two-matrix packing that also distributes the label among entries need not collapse this way. Its relative/unconditional information loss, original-limsup interface, and joint terminal event remain unproved.
