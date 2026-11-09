# Remaining global reduction: a precise partial estimate

The frozen T101G69 target is unchanged. The exact-B/small-D supporting construction in the other r69 notes is not a solution of this reduction.

There is a useful statement for arbitrary D at exact B=I. Fix a small absolute epsilon>0 and take Pi=1_[1−epsilon,1](K), W=range Pi. Write H=sum Ya² and Z=(I−Pi)(YaYb), as before. The partial-trace argument gives H<=(1−epsilon)^(-2)I without assuming D small. The gap on W-perp is now epsilon, not 1/2. Therefore the direct leakage estimate only gives

  ||Z||op² <=4 H_op epsilon/g,

with g=epsilon in general, which is NOT small. A large spectral gap is essential here. It would be incorrect to insert g=1/2 at this new cutoff unless the spectrum of K in (1/2,1−epsilon) had independently been excluded. The high-cutoff idea alone does not give an operator-small product defect.

There is, nevertheless, an exact conditional estimate not requiring a lower bound on H. If a spectral subspace W has upper row Gram H<=hI and coefficient-tensor leakage norm z=||(I−Pi)M||op, then its compressed associator has one-versus-three operator norm at most2sqrt(h)z. Use

  A_sigma(x,y,z)=Pi(x Z_yz−Z_xy z)

up to the global associator sign. Multiplication from (W-perp) tensor W to the ambient matrix HS space has norm at most sqrt(h), by row Cauchy–Schwarz. This controls the full ternary coefficient space. No lower H or small one-input leakage Gram is needed for this particular flattening. Crossed two-versus-two flattenings are still not controlled by this observation.

Thus three separate issues must not be conflated:

* choosing a high cutoff makes the retained Dirichlet energies small, but need not leave a fixed gap below the cutoff;
* even with a fixed gap and small coefficient-tensor leakage, lower H and crossed flattenings require additional arguments;
* deleting directions with deficient H or bad original D can create further Gram/associator error on the retained space. A trace bound on the first deletion is not an operator bound on those new errors and does not justify iteration.

For arbitrary B<=2I, the additional exact-isotropy reduction also remains missing. The operator-ball normalizer in operator-density-correction.md requires beta_inf and all associator flattenings small; the small-total r67 normalizer has an even stronger hypothesis. Neither supplies arbitrary-B preprocessing at trace-paid cost.

This note records a correction to an author exploratory message that mentioned the arbitrary-D high cutoff with a fixed-gap formula. No full theorem or candidate relied on that message. The valid exact-B/small-D notes have their fixed gap from cb near-idempotence and are not affected.
