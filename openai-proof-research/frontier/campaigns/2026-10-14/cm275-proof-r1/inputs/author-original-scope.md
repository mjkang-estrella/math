# Frozen original scope CM275

Author: Myeongjin Kang, no affiliation. Original prose CC BY 4.0; original code MIT. Third-party inputs private.

For every well-formed input consisting of M>=1 pairwise distinct rational positions R_1,...,R_M in Q^3, N>=1 encoded in unary, and rational a<b, encode rational coordinates and thresholds by signed binary numerator and positive binary denominator in lowest terms, using the fixed standard self-delimiting encoding of the stipulated source. Let L be the total input length. Assume b-a>=L^(-1).

Let H=-1/2 sum_i Delta_i - sum_{i,alpha}|x_i-R_alpha|^(-1) + sum_{i<j}|x_i-x_j|^(-1), with every nuclear charge exactly1, on the full spinful antisymmetric space wedge^N(L2(R3) tensor C2). Its quadratic-form domain is the intersection with H1(R^(3N);(C2)^tensorN), antisymmetry exchanges spatial and spin coordinates together, and E=inf spec H. Nuclear repulsion is omitted. The promise is E<=a (YES) or E>=b (NO).

**Full target:** this promise problem belongs to QMA, with a uniform polynomial-size verification circuit and polynomial-size witness in L. Combined with the stipulated source Theorem1, the same unchanged problem is QMA-complete under deterministic classical polynomial-time many-one reductions.

There is no neutrality, binding, eigenvector attainment, excitation-gap, nuclear-separation, bounded-coordinate-value, supplied-basis, selected-spin-sector, or confinement promise. All allowed rational nuclear positions, all unary electron counts and both unbound and bound spectra remain included. No theorem for exponentially large binary charges is claimed. There is no smaller replacement target if this claim fails.

Freeze chronology: coulomb-feasibility.md already contained a plausible multistep argument before this scope was frozen. screening-before-freeze.md records actual source/primary and historical comparison completed before the freeze. This is an honest pre-freeze feasibility record, not a claim that every mathematical idea was developed only after freezing. Detailed proof and adversarial validation follow this freeze.
