# The quantitative debt in the nonhomogeneous route

Live author derivation; no full target frozen or proved yet. Primary Fernández-Real–Serra2609.05669v1 was read in actual HTML: introduction and overview through line327, notions of solution384–422, critical dimension489–531, the displayed flux admissibility2452–2458, neck-count proof2363–2444, and neck-charge proof2898–3020. Remaining portions of that long proof are not claimed read.

The primary distinguishes n_* for STABLE cones classical away from the vertex from the minimizing-cone critical dimension of source367. Equality of these thresholds cannot be inferred from inclusion of minimizers in stable solutions. Source367's lower tensor/cutoff operations might separately establish stable-cone exclusion, but this requires reading and checking their full hypotheses.

Even granting n_*=7, the final nonhomogeneous step is not a routine dimension substitution. The primary's neck charge is rho²=sum(r_i/R)^(n-2). Its selected excess exponent alpha gives artificial-boundary gain gamma_alpha=1+2/alpha. The exact flux requirements are

 p alpha < (n-1)/(n-2),   2p < 1+2/alpha.

The below-excess-scale Neumann contraction uses both errors with positive epsilon powers. Generalizing the displayed dimension-four powers requires

 2-(n-1)/p > 0,   2p-(n-1) > 0,

that is p>(n-1)/2. There exists any p meeting all three strict requirements if and only if

 alpha < 2/(n-2).

Indeed the upper endpoints are (n-1)/[(n-2)alpha] and 1/2+1/alpha; each exceeds (n-1)/2 precisely under that condition. Thus dimension5 needs alpha<2/3, dimension6 needs alpha<1/2. The primary's small strict improvement alpha_*<=1/(1+chi/6)<1 does not meet either threshold. Repeating the written conclusion does not compound it: it is a bound relative to the original excess epsilon, not a multiplicative recurrence for alpha_*.

Equivalently, a neck-charge gain rho<=epsilon^beta strong enough for this architecture would need beta>(n-2)/2, rather than merely beta>1. At n=6 the missing exponent is greater than2. The source's homogeneous certificate cannot by itself supply this quantitative nonhomogeneous gain, because it gives an integrated angular contradiction and no estimate relating the number/size of necks to a global vee excess.

Two possible operations remain to investigate, not assume: (i) a weighted curvature test derived from the source tensor certificate which changes the effective neck charge, or (ii) a repeated local excess/charge bootstrap with genuinely improved input exponent and controlled center selection. The ordinary dimension-four improvement supplies neither automatically. This calculation is an interface obstruction, not a counterexample to stable rigidity.

## Exact bounded reweighting experiment

The source's retained independent engine and bounds module were read completely, as was reproduce.py; they were not executed in the private archive. reweight_probe.py copies the two modules to a fresh /var/tmp directory, authenticates all inputs first, and computes the signed change of the Table-I polynomial at a'=a+t. The canonical frozen source coefficient output supplies the stipulated original Gram remainder; the full Gram expansion is not replayed and no independent certificate verdict is asserted. Terms with positive g or z powers are removed only after signed collection, since this experiment concerns g=z=0.

The resulting 3x3 rational comparison matrix on (|w|,|ell|,|X|) is positive definite at t=0 and t=1/500000 by exact leading principal minors. It is not positive definite at t=1/100000,1/1000,17/100,9/50,43/100. These failures concern the fixed source Gram plus its magnitude-remainder method, NOT the true reweighted tensor inequality. In particular no arbitrary tensor counterexample was produced. Tiny certified self-improvement does not reach the useful t>.17 threshold.

Receipt: /var/tmp/r99-reweight-dk8uhe7w/receipt.json, SHA256 c5bbe63377b33c0b63d52e32cbffc3273870af6208893bdb9f9cbcc226ef09a0. Prior six-point experiment is preserved separately at /var/tmp/r99-reweight-6m69z100/receipt.json, SHA25695b29830f37378ddbbf84a22d70f401f0428ccb3a186880e5ecdaf3f6489c6b3. The later run adds the tiny positive case. This is author exploratory arithmetic, not a review gate.
