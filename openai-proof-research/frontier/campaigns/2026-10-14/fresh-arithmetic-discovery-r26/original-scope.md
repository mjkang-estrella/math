# T266: unrestricted third-charge orientation identity

Frozen2026-10-18 04:12 UTC, before a full proof. This is a research target, not a proved theorem or nominee. No restricted replacement scope is authorized by this freeze.

For every ordered triplet of pairwise mutually unbiased orthonormal bases in C^6, and every ordered pair of distinct bases from that triplet, let H be its unscaled6×6 transition matrix. Put α=(1,1,1,−1,−1,−1), and for a balanced integer charge a define

    g_H(a)=(1/6) sum_{k=0}^5 product_{i=0}^5 H_ik^(a_i),
    Γ_H(a)=(1/720) sum_{π∈S6} |g_H(πa)|².

The target is the complete assertion

    Γ_H(α)=0 and Γ_H(3α) Γ_{H*}(3α)=0.

The second equality says that one orientation has every permuted third-charge character zero; it does not just assert a cancellation in a signed average. The nonnegative product also equals zero iff all independently permuted products vanish. Bases, phases, their ordering and their transition matrices are unrestricted; no Fourier-family, Szöllősi-family, algebraicity, genericity, product-basis or marked-coordinate assumption is made. There is no approximation tolerance. This is the full universal identity in Matolcsi–Matszangosz–Varga–Weiner, arXiv2503.14752v2, Conjecture2 / (4.9), after harmless positive normalizations. The already-known first-charge component is retained and credited; the third-charge component is the unpaid target.

Exact matrix domain: equivalently take arbitrary H,K∈T^(6×6) with H*H=K*K=6I and |(H*K)_ij|²=6 for every i,j. Apply the assertion to H,K,H*K/√6 and their adjoints. This domain covers exactly the triplets after one common unitary makes the first basis standard.

Pre-freeze comparison: the pinned Fourier companion proves the α vanishing outside Tao's cubic class; its complete-family certificate uses seven bases and an order-two completeness identity. The pinned N(6)=3 companion excludes quadruplets under its execution/arithmetic contract and does not classify triplets or prove the displayed orientation identity. The primary triplet paper's (4.9) is the same desired assertion, not a new formulation credited here. Brierley–Weigert's exclusion of a triplet containing the cubic pair is a primary antecedent, not a fresh step.

Candidate mechanism under investigation: build a triplet moment/Gram calculation retaining the rank20 orthogonal complement of the three diagonal subspaces, instead of the zero complement available for seven bases. Use only genuine triplet orthogonality and cross identities, plus the stipulated single-matrix Fourier constraints, to obtain a new positive identity forcing the product to vanish. No such certificate has been constructed at freeze. The changed Gram/rank identities and tests below are technical support and cannot themselves count as the target.
