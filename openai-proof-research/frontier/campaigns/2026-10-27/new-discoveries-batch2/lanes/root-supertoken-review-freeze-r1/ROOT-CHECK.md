# Supertoken candidate: root check, not acceptance

I read the candidate proof and the actual cached published source text, Section 3
and Conjecture 4.2 on printed page 28. Repeated token positions are explicitly
allowed. I also read Bailey–Cameron Theorem 3.32 and Corollary 3.33 in the cached
author manuscript, pp. 24–25. This records a text read, not a PDF visual audit.

Independent proof of the block separation: if two supports have the same four
edge-incidence counts on P5, their indicator difference v satisfies
v_i + v_(i+1) = 0. Thus v = (a,-a,a,-a,a), where a is -1, 0, or 1.
If a=1, the first support contains positions 1,3,5, contradicting its size at
most two. If a=-1, the second support has the same contradiction. Hence a=0.
Two disjoint P5 landmark blocks recover both local supports. A support of one
or two positions uniquely determines an occupancy vector with total two.
The base graph is still K10. The eight landmarks therefore resolve all 55
vertices, contradicting the universal equality nine. No exact dimension is claimed.

The attached independent checker derives adjacency from occupancy differences,
runs BFS from every vertex, checks all 3,025 distances, and verifies all 55
signatures. It also checks the 16 block supports and the candidate's full manifest.

The strongest objection remains substantive: Bailey–Cameron's disjoint P3
incidence-signature construction is not literally valid for doubled tokens,
but replacing P3 by P5 may be a routine classical adaptation. The failure of P3
alone does not settle this objection. An independent review must assess the
complete adaptation, closely related separating-family results, and current
prior art before any formalization. No credit, paper, or Lean investment yet.

The other r114 leads remain unresolved or already publicly refuted as reported;
they are not nominated. Candidate bytes are frozen and must not be edited.
