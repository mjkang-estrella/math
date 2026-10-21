# Prefreeze continuation: where constant optimization actually fails

No theorem was frozen or weakened. The fully quantified strong and contractive-approximation reductions are retained in CALCULATIONS.md and CONTRACTIVE.md. This note tests the next concrete step in their polynomial mechanism; it is not a nomination of a known open conjecture.

## 1. The stronger payment has already removed several apparent gaps

The exact QSP proof permits one polynomial for a finite signed operator tuple, a Bernoulli coloring with uniform conditional marginals, free compression of all complementary terms, and transfer of a sum of fixed even moments. The common spectral cut and scalar Jensen close simultaneous compression. PV15's spectral regularization can also synchronize with finitely many diagonal step functions without refining the paving colors. AP's noncentral support decomposition and small-diagonal positive contraction then close contractive quadratic approximation via one normal completely positive contraction.

Thus neither a product-of-pavings estimate, nor a bare statement that conditional expectations are absent, nor a presumed norm-control gap is an adequate stopping point. The source/primary mechanisms pay them in the displayed construction.

## 2. Quantitative place where the present reduction loses constants

For a tuple of m operators, the finite zero-cost threshold is t>3/√(mr). The fully colored norm-detection threshold is 2mβt, β=80. The state proof then bounds the Cartan and off-normalizer parts separately, before adding them. Even an exact free-compression estimate would not remove this Cartan buffer or the triangle-inequality payment. PV16's sharper L-free dilation works under its actual singular tracial freeness hypothesis; arbitrary Cartan words in QSP do not meet that hypothesis. The atomless off-normalizer kernel says nothing comparable about normalizer words.

A natural attempted local improvement is to keep the penalty fixed when assigning a color (β=1), and seek a universal C with

    min_i (d_i−d)≤C m_0,

where d is the arrow's positive-trace deletion increment and m_0 its rooted positive cost. This is the precise inequality the hazard iteration needs, with coefficient one on the old deletion increment. Replacing it by d_i≤C d would not yield the zero-initial-cost propagation used by QSP.

The following explicit calculation rules out this *generic arrow-residue lemma*. It does not rule out a stronger inequality for the special arrows actually realized by paving polynomials, nor a different measured construction.

## 3. A three-by-three arrow diagnostic

Let r≥8 and a=1, with deletion matrix Λ=diag(1,−1). Take r equally likely color options. For one option set the residues at (+1,−1) to (1/r,0). For each of the other r−1 options set them to (0,1+1/(2r)). Their averages are

    b_+=1/r²,   b_−=c_r=(1−1/r)(1+1/(2r))<1.

The parent arrow is

    H_r = [ −1       1/r       √c_r ]
          [ 1/r       1          0  ]
          [ √c_r      0         −1  ].

Its principal block on coordinates 0 and 2 is strictly negative definite. Interlacing, or inertia, therefore shows that H_r has exactly one positive eigenvalue, λ=1+d>1. The root equation is

    λ+1 − (1/r²)/(λ−1) − c_r/(λ+1)=0,

so

    d[(2+d)²−c_r]=(2+d)/r².

The deletion positive trace is 1, hence its positive-trace increment is exactly d. Since λ+1−c_r/(λ+1)≥3/2,

    0<d≤2/(3r²).

The rooted spectral mass at λ is

    w=[1+(1/r²)/d²+c_r/(2+d)²]^−1,

and there are no other positive eigenvalues. Thus m_0=(1+d)w and, for r≥2,

    0<m_0≤(1+d)d²r²≤14/(27r²).

For the first option the unbuffered child deletion increment is

    d_+=√(1+1/r)−1.

For every other option it is

    d_−=√(1+1/(2r))−1.

The smaller is d_−, and d_−≥1/(5r) for r≥2. Therefore, for r≥8,

    min_i(d_i−d)≥1/(5r)−2/(3r²)≥7/(60r).

Dividing by the rooted-cost bound gives

    min_i(d_i−d)/m_0≥(9/40)r.

In fact the defining equation gives d=(2/3+o(1))r^−2, m_0=(4/9+o(1))r^−2, and min_i(d_i−d)=(1/4+o(1))r^−1, so the ratio is (9/16+o(1))r. No constant C independent of the color count can satisfy the proposed unbuffered generic inequality.

Every parent and child here is an ordinary Hermitian arrow, the deletion data agree, and the nonnegative residues have exactly the required uniform average. This is an exact finite calculation. It is not asserted that this collection comes from one finite zero-diagonal contraction with the precise paving-color conditional laws. That additional realizability constraint is exactly why the diagnostic is not an impossibility theorem for sharp paving.

## 4. The unpaid operation, scoped honestly

After the closed reductions, a further constant-level improvement through this route needs a sharper local cost law using *realizable paving-polynomial structure*, or a different compatible cost whose nonsingular deletion/height limits and uniform color marginals can all be established. A bound on finite largest roots alone is insufficient to run the source's integrated cost/hazard proof without its buffer. Alternatively one would need a joint model norm estimate that handles the Cartan and off-normalizer pieces without the present additive losses; singular tracial L-freeness cannot simply be asserted for that model.

No such operation was closed here. The generic unbuffered repair just tested is actually false, whereas the desired realized-polynomial or joint-model repair is left unresolved. This is a local obstruction to one proposed lemma, not a global failure of the source, a proof that its constants are optimal, or a worldwide-open-problem claim.

PREFREEZE/no nominee: the closed consequences have an explicit compatible source/primary construction, and no distinct nonroutine operation was identified for a substantial-result freeze. This is a discovery decision. Independent grades, adoption and counts belong to the parent.
