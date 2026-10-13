# I203: the all-height elliptic density bound is attained

2026-10-12. **PROVED NOMINATION: the entire all-height periodic problem has value 1+k², attained by a compact nondegenerate parallelogram.** This is submitted to the parent; neither acceptance gate is claimed completed.

For every real 2 by 2 matrix A with tr A=0 and d=det A>0, and every L>0, put k=L sqrt(d). There are a full-rank lattice Gamma and a compact parallelogram F such that

    F+(I+sA)Gamma = R² for every |s|<=L,
    |F|/covol(Gamma) = 1+L²d.

Consequently the infimum over all bounded measurable admissible F and all full-rank lattices is exactly 1+L²d. No attainment assumption is used. The proof constructs an attaining pair.

In the normalized case A=J and |t|<=k, write D=1+k² and use

    B = [[k,2k],[-1,0]],
    G = [[0,2k/D],[-1,2k²/D]],
    F = B[-1/2,1/2]²,       Gamma = G Z².

A direct multiplication gives

    B^(-1)(I+tJ)G = [[1,-2k(t+k)/D],[(t-k)/(2k),1]].

The product of its off-diagonal entries is (k²-t²)/D in [0,k²/D], strictly below one. The accepted deformed-square covering lemma therefore covers every transverse plane, including all irrational intermediate heights and both endpoints. The determinant ratio is |det B|/|det G|=D. Conjugation transfers the construction to every A in the theorem. An independent strip-and-staircase proof is given in the analytic record.

The essential step is the fixed skew lattice and fixed parallelogram that turn the whole elliptic path, after a unimodular change of lattice basis, into positive-product square-covering matrices. This is more than selecting a common endpoint tile or adding elementary resonances. The pointwise square-covering lemma is an accepted operation and overlaps the classical notched-square mechanism; it is not nominated anew.

The [analytic record](../experiments/i203_all_height_tiles/analytic-attempt.md) also proves finite nonlinear covers with total perpendicular area at most

    h integral_Domain [1+L²(det DV)_+] J_h(V) + epsilon

for compact label sets, C¹ fields with tr DV=0 and det DV>-L^(-2), and arbitrary L,h>0. A determinant cutoff handles loss of uniform template conditioning near zero. This improves I201's factor 1+2L²(det DV)_+; the finite-retention operation itself is paid. Sharpness is established for the periodic affine problem only, not arbitrary finite cylinder covers or a new convex-body extremal bound.

The [literature record](../sources/i203_all_height_tiles/literature.md), [reading and failure log](../experiments/i203_all_height_tiles/reading-and-failures.md), and [input authentication](../experiments/i203_all_height_tiles/input-authentication.json) give the completed source comparison and symbolic validation. The unrestricted measurable Steinhaus problem and equal-covolume multi-lattice tiling problems are not asserted equivalent to this varying-covolume cover problem. No worldwide priority claim is made. Eight previously accepted findings remain accepted; nomination and significance decisions remain with the parent.
