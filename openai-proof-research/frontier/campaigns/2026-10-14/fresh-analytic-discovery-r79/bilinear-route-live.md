# Live alternative: transverse paired propagation

Not a theorem claim or frozen candidate scope. The full investigative target remains hyperbolic diagonal restriction for every p>3. The ruling obstruction rules out the unchanged linear capacity theorem; it does not rule out the following paired mechanism.

## Why the primary strip argument alone is insufficient

I read Demeter–Wu v2, section 4, in full in extracted text lines 1116–1740. At equations (4.24)–(4.25), their two estimates for a transverse product have respective scale factors (λr)^(-3/4) and (λr). Interpolation cancels these at weights 4/7 and 3/7, producing p=22/7. In general a quartic factor (λr)^(-a) paired with the same quadratic factor cancels at weight 1/(1+a), hence p=2+2/(1+a). Reaching p=3 by this exact scalar interpolation requires a=1. Their broad-narrow reduction does not supply that improvement: the strip rescaling closes once p>3, but the broad estimate remains unpaid. Their existing bilinear theorem plus their existing incidence bound is already paid and cannot be nominated here.

## A concrete paired cancellation worth testing

The pinned companion B, section 06, terminal-mass proof and final contradiction, use two ingredients: geometric capacity control with factor m^(2(1-s))h, and mass bounds min(m^(-2(1-s)),h^(-1)). For two transverse packet populations, the exact algebra suggests the following replacement. Write M_i for their initial normalized mass and K_i for their initial capacity. Suppose an actually constructed common retained output has capacities bounded by

    K_out,i ≤ m^(2(1-s_i)+20κ+o(1)) h_i K_i,

and mixed mass bounded by

    r w² Σ_b |c_1,b c_2,b|
      ≤ m^o(1) (M_1 M_2)^(1/2)
         min(m^(-2+s_1+s_2), (h_1 h_2)^(-1/2)).

Multiplying by (K_out,1 K_out,2)^(1/4) cancels the time and amplitude losses, because with S=(s_1+s_2)/2 and H=(h_1 h_2)^(1/2),

    m^(1-S) H^(1/2) min(m^(-2(1-S)),H^(-1)) ≤ 1.

The resulting paired gauge would have cost at most

    m^(10κ+o(1)) (M_1 M_2)^(1/2) (K_1 K_2)^(1/4).

This algebra is exact even when s_1≠s_2 and h_1≠h_2. It is only conditional algebra: the common retained output and both asserted bounds have not been constructed.

The mixed-mass fourth-power input would need a discrete transverse analogue of source `eq:source-33`:

    r_+ w_+² Σ_b |c_1,b c_2,b|²
      ≤ m^o(1) (k_1 k_2)^(1/2)
         ∏_{i=1,2} (r_- w_-² Σ_v |d_i,v|⁴)^(1/2).

Demeter–Wu Theorem 1.10 has the correct bilinear power and multiplicity factors. However, a proof must transfer it to the exact full-matrix discrete samples. In particular, convolutional sampling of each factor introduces two separately shifted spatial arguments; these require a uniform translated-packet application and correct enlarged activity tubes. One cannot simply multiply two linear sample inequalities, since the required linear fourth-power inequalities fail.

## The new hard step, not concealed by the algebra

The source's section 06 is an extremal argument for a *single linear operator* and its atomic output norm. Its masks retain near-extremal amplification and simultaneously force stable root path counts, time dimensions, and coefficient classes. None of its stated results directly supplies those masks for a paired output. Taking two independent near-extremizers does not ensure substantial common output, while restricting both to their common output can destroy each population's minimal time/path extremality.

A complete route therefore requires a new paired extremal selection theorem. It must retain a large mixed output while giving both leg-specific capacity/path bounds and a transverse fourth-power estimate at every transition. The mixed gauge above is not yet a proved composable atomic norm. Decomposing either input must be compatible with the product output and every subsequent mask; this must be established rather than borrowed from the linear source lemma.

There is also a frequency-scale issue. Transversality is separation in *both* coordinates. Arbitrary masks and repeated synthesis may enlarge frequency supports. One possible setup is to start in two fixed transverse boxes and stop frame insertion while every window is smaller than a fixed fraction of their separation; finite many coarse windows then handle final sampling. This needs an exact support/error proof. Ordinary rescaling of one child window is not an automatic simultaneous normalization of two distant windows.

These are concrete new obligations beyond the primary strip argument. The scalar cancellation is encouraging but does not settle them. No full restriction estimate, broad propagation theorem, or independent gate is claimed.

## A concrete obstruction to naive paired composition

There is a stronger problem than selecting common masks. A diagonal mixed quantity cannot serve as the intermediate norm of arbitrary exact transitions. Already on two coordinates, let a=(1,0), b=(0,1) and let H=2^(-1/2)[[1,1],[1,-1]]. Then every positive-power diagonal mixed sum of a,b vanishes, whereas Ha and Hb have nonzero products on both coordinates. Thus no estimate of the form mixed(Ta,Tb)≤C mixed(a,b) holds for general mixing transitions. This is a finite linear-algebra illustration of the missing composition property, not a counterexample to the proposed final bilinear restriction estimate.

Passing to a⊗b restores a linear composition law, but inserts all *off-diagonal* intermediate position pairs. The bilinear decoupling theorem controls two fields evaluated at the same physical point; it does not directly control that full tensor array. Tracking relative positions as an extra parameter would therefore need a new estimate, including the cost of summing those parameters. A final diagonal projection does not justify diagonal projections at intermediate scales. This is the precise place where an informal transplant of the source's masked linear diagram would lose exactness.

The natural next object is consequently a paired path system retaining relative positions, with simultaneous-time incidence at the terminal layer. It cannot be replaced by the diagonal gauge alone. Establishing its propagation, or finding a finite-scale counterexample to a proposed tensor capacity, is still open in this packet.
