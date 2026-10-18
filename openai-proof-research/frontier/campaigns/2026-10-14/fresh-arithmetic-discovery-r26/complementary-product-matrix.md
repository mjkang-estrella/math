# A real10×10 interface for the unchanged target

This is an exact algebraic reduction, not a proof of T266 and not a nominee. It uses the first-charge vanishing for H and H*, credited to the pinned Fourier theorem together with exclusion of the cubic pair from a triplet.

Let I and S range over three-subsets of {0,…,5}. Write I^c,S^c for complements and put

    B_IS= product_{i∈I,k∈S} H_ik · product_{i∈I^c,k∈S^c} H_ik,
    D=product_{i,k}H_ik.

Choose either δ∈T with δ²=D. Select the10 representatives I containing0 and likewise the10 representatives S containing0. Define the real matrix

    M(H)_IS=Re(δ^(−1) B_IS).

Changing δ changes the whole matrix's sign. Changing a representative to its complement leaves its real entries unchanged, since

    B_(I^c,S)=B_(I,S^c)=D/B_IS,
    B_(I^c,S^c)=B_IS.

In particular the definition is compatible with arbitrary row/column permutations: they permute the10 complementary pairs. Row or column phase factors multiply every B_IS by the same unit phase η and D by η², so M changes at most by its common sign. Taking adjoints transposes M, with a compatible choice of δ. Thus M is a well-defined real invariant up to sign and row/column permutation, with entries between−1 and1.

Suppose g_H(α_I)=0 for every I, where α_I=+1 on I and−1 on I^c. For fixed I set u_k=product_i H_ik^(α_I,i), and let e_j denote the elementary symmetric functions of its six entries. Then Σu_k=0, and Newton's identity gives Σu_k³=3e_3. Hence g_H(3α_I)=e_3/2. Define D_(I^c)=product_{i∈I^c,k}H_ik. Expanding e_3 over column three-subsets gives the exact equality

    D_(I^c)e_3 = sum_{|S|=3} B_IS
                 =2δ sum_{S contains0} M(H)_IS.

All omitted factors have modulus one. Therefore

    |g_H(3α_I)|²=(sum_S M(H)_IS)²,
    Γ_H(3α)=(1/10)||M(H)1||².

The normalization follows because the720 coordinate permutations give each of20 three-subsets36 times, and complementary subsets have equal squared character modulus. Apply the same calculation to H*: its matrix is M(H)^T, and the first-charge hypothesis holds in that orientation as well. Thus the unpaid T266 product is exactly

    Γ_H(3α)Γ_H*(3α)
      = (1/100)||M(H)1||² ||M(H)^T1||².

Consequently the full target asks that every triplet transition have the all-one vector in either the right kernel or the left kernel of this10×10 real matrix. Neither the sign choice nor labeling affects the assertion. It is not enough to show that the grand sum of entries is zero, that the row-sum and column-sum vectors have zero inner product, or that M is singular: none of those real-matrix conditions forces the displayed product to vanish.

This reduction removes the per-charge phase factors and exposes the precise orientation disjunction. It does not construct the missing implication from the existence of a third unbiased basis to one of these two kernel conditions. The rank20 projection from triplet-gram.md acts in a different coordinate space; no justified compression/intertwining relation forcing this10×10 kernel condition has been found.
