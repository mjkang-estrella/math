# r173 — prescribed witnesses are additional data

This prefreeze diagnostic concerns a completely specified extension assertion. It is not a proposed replacement for any older relative, equivariant, uniform-witness, ideal, or absorption target. It does not test the truth of Source303.

## 1. A pointwise solvable family with incompatible prescribed boundary witness

Let A=O_infinity, K=[0,1], and take the continuous data

    a(x)=b(x)=1, c(x)=x1.

At x=0 prescribe s(0)=t(0)=1. These prescribed values satisfy both exact diagonal equations and the cross equation, since c(0)=0. At every x>0 choose two canonical orthogonal isometries v_1,v_2 in A. They satisfy

    v_i*v_i=1, v_1*v_2=0,
    v_1*c(x)v_2=0.

Thus every individual fiber has exact solutions, including the specified boundary fiber. No existence assumption has been left unverified.

Nevertheless, for any 0<e<1/2 there do not exist norm-continuous S,T:[0,1]->A such that

    S(0)=T(0)=1,
    ||S(x)*S(x)-1||<e, ||T(x)*T(x)-1||<e,
    ||S(x)*c(x)T(x)||<e                                  (1.1)

for every x.

Indeed S(x)*S(x)>=(1-e)1. The continuous functional calculus gives a continuous isometry

    V(x)=S(x)(S(x)*S(x))^(-1/2).

Its defect P(x)=1-V(x)V(x)* is a continuous projection-valued function and P(0)=0. A nonzero projection has norm exactly1, so zero is an isolated point in the space of projections. The zero set of P is both open and closed; connectedness of the interval implies P(x)=0 everywhere. Thus V(x) is unitary everywhere and S(x) is invertible, with ||S(x)^(-1)||<=(1-e)^(-1/2). The same argument applies to T.

At x=1, the product S(1)*T(1) is invertible, with inverse norm at most (1-e)^(-1). Since 1=Z Z^(-1) implies ||Z||>=||Z^(-1)||^(-1),

    ||S(1)*c(1)T(1)||=||S(1)*T(1)||>=1-e>e,

contradicting (1.1). This proof needs no K-theory classification, trace, rank surrogate, or assumption about the simplicity of an auxiliary algebra.

The obstruction is robust to small prescribed-boundary error: if S(0),T(0) are within norm <1 of the identity, they are invertible, so their polar isometries are already unitary and the same argument applies. It is not an artifact of asking for exact initial equality alone.

## 2. Why the completed compression does not solve this extension problem

With no boundary condition, the constant pair v_1,v_2 is an exact solution for all x. In C([0,1],O_infinity), the constructions in CALCULATIONS.md and MIXED.md are consequently consistent with (and overpowered for) this example. They may choose a proper isometry at x=0. The contradiction only appears when a preassigned unitary polar component must be retained there.

Multiplying local witnesses by a partition of unity first creates several target columns. Compressing those columns by a freely chosen properly infinite row may change the range-defect projections at the boundary. Standard hereditary membership and ideal comparison say nothing that preserves that boundary defect. Likewise, moving into an unused O_infinity tensor factor and using its orthogonal isometries changes the boundary witness. Abstract absorption does not make the resulting coefficient agree with the identity there.

A quotient onto the boundary algebra also does not by itself fix this: surjectivity on elements is not surjectivity on continuously prescribed isometry frames with their range-complement data. In this example the incompatible components are visible before any quotient-lifting subtlety, simply from the norm-continuous projection path.

## 3. Exact extent of the conclusion

The failed assertion is unrestricted prescribed-witness interpolation from pointwise solvability, even for this one-parameter, two-diagonal family in O_infinity. It is not a counterexample to O_infinity absorption, strong pure infiniteness, any source norm inequality, or a relative theorem with stronger compatible module/frame data. It does not refute quotient-compatible original-palette saving in r172 and does not yield an actual radius counterexample there.

For a meaningful stronger relative construction one would need an operation that simultaneously extends the chosen cutoff module frames, preserves their prescribed boundary equivalence/component data, and controls the mixed products. If noncommuting relative observables are imposed as well, the simultaneous moment interface in MIXED.md must also be supplied. Neither the free support choice nor the primary nuclear approximately-inner-map collapse establishes this combined operation with arbitrary prescribed frames. No sufficient new set of compatibility hypotheses and no nonroutine full extension proof was obtained in this round. In particular this note does not freeze a theorem that simply assumes the desired extension exists.
