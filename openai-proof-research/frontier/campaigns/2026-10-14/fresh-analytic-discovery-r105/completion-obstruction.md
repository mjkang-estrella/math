# Exact obstruction to peak-preserving completion

Let K=[-1/2,1/2]^n and Gamma=Z^n. The covering multiplicity m_K(x)=sum_(v in Gamma)1_K(x-v) is one almost everywhere; its density is one and its hole proportion is zero. Thus it satisfies every small-hole premise of the source completion lemma.

For any 0<a<1, the dilated body (1+a)K has coordinate length1+a. On the open box ((1-a)/2,(1+a)/2)^n, each coordinate belongs to precisely two translated intervals, with centers0 and1. Hence its multiplicity is exactly2^n there. This box has positive volume a^n, so ESSENTIAL maximum is2^n, not merely a boundary coincidence. Its average multiplicity is only(1+a)^n. Taking a=1/n keeps average<=e but gives exponential maximum.

Equivalently, rescaling the source final lattice to (1+1/n)^(-1)Gamma for the unchanged K has the same peak. Thus no universal bound peak_after <= polynomial(n)*peak_before follows from source completion, even when the original arrangement has no holes. This does not disprove the frozen existence target: Z^n itself solves the cube instance. A successful construction must retain or select another lattice with controlled overlap, or replace the completion operation with genuinely upper-tail-aware geometry.
