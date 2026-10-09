# Separate R009 paper track

Status: recorded for a separate manuscript; no paper drafted or submitted in this track.

Working title: *Weighted capacity for four-state reconstruction with variable edge channels*.

Author: Myeongjin Kang, Independent researcher. No coauthors supplied.

The scope is the R009 result and its locally finite extension: a deterministic rooted locally finite tree, symmetric four-state ferromagnetic channels with known edge parameters $0<\lambda_e\leq1$, and ordinary level reconstruction. There is no common degree bound or uniform lower bound on positive channel parameters. Zero-channel edges are handled by pruning to the positive-edge root component. Keep the quantitative bounds and the perfect-channel cases in the same paper.

The proposed equivalence is positive limiting reconstruction information if and only if the weighted capacity is positive. With $r_e=\lambda_e^2$ and $R_w$ the product of the $r_e$ along the root-to-$w$ path, the potential is

$$
V(\theta)=\sup_{\xi\in\partial T}\sum_{e=(v,w)\in\xi}(1-r_e^2)\left(\frac{\theta(e)}{R_w}\right)^2,
\qquad C(T)=\sup\{|\theta|:V(\theta)\leq1\}.
$$

The upstream dependency is the preserved posterior class and moment-saving inequality in *A Capacity Criterion for Four-State Potts Reconstruction on Trees*, `build/main.tex`, labels `prop:companion` and `eq:moment-saving`, including the cited threshold companion's Proposition 3.2, at `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The eventual manuscript must inspect and state those exact hypotheses, rather than assume a variable-channel capacity theorem already exists upstream.

Research records in this isolated checkout:

- [R009 finding](../../frontier/findings/R009-variable-channel-capacity.md)
- [Variable-channel proof](../../frontier/iterations/i08-variable-channel-capacity.md)
- [Locally finite extension](../../frontier/iterations/i11-locally-finite-capacity.md)
- [First proof review](../../frontier/reviews/i08-variable-capacity-r2.md)
- [Novelty review](../../frontier/reviews/i08-variable-capacity-novelty-r3.md)
- [Extension proof review](../../frontier/reviews/i11-locally-finite-capacity-r4.md)

These review records are internal AI reviews. Their acceptance labels are not external peer review or formal proof certificates. Worldwide priority has not been established.

Next manuscript work: verify the source class and its closure properties; state the unsmoothed two-law bounds; prove the uniform recursion and capacity comparison; include the degree-independent truncation and zero-edge argument; check the quantitative constants; then run a separate primary-source literature review. Do not merge this probability result into the prime-predecessor paper.
