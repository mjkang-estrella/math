# H025 alternating-frontier arithmetic compatibility

2026-10-08. Native Astra /root/h007_additive_relations independent component
audit COMPLETED; root checked the block sets and ordinary formula arithmetic.
A scoped compatibility result, not complete-solver performance. No new execution
or Lean claim. Verified ECDLP improvement NONE.

Let W=2ell+1, B=kW, T_i=s_iG, S_i=b_iQ+c_iG. Central affine centers are
C_ij=S_i+(-floor(B/2)+ell+jW)T_i for0<=j<k. Each emits its own abscissa and
x(C_ij±uT_i),1<=u<=ell, exactly the first centered interval of B indices.
Store full next centers C_ij+BT_i and C_ij-BT_i. Positive blocks use/advance
only the positive array by+BT_i; negative blocks use/advance only the negative
array by-BT_i. This produces the exact adjacent intervals frozen for B. Internal
order may differ on negative blocks because no inspection precedes block end;
future-block keys must not be inserted. Batch only the current family's current
k centers, not multiple future family blocks.

With field multiplication M, squaring S and inversion I, the regular cost of a
subsequent block is

    K=(ell+1)*(I+(5k-3)M)+k(2ell+1)S,
    Cx=K/B.

The first block must fork both frontiers. The full paired advance shares one
inverse batch but computes both ordinates:4M+2S per center after inversion,
versus2M+S for one full advance. Its ordinary cost is therefore

    K+k*(2M+S).

Advances are executed and paid before block inspection, including the terminal
block. Deferring a backward advance still costs work; omitting terminal advances
needs a different specified stopping ledger. At initial probe k=ell=1, use
Cx=S+4M/3+2I/3, NOT the asymptotic2.5M+S. The extra first-block fork is2M+S
per reached family. This is why key-count improvements alone were not accepted.

B's shared initialization includes U=[floor(q/73)]G; six doublings for
U,4U,16U,64U; three doublings for Q,2Q,4Q,8Q; four additions to form S_i;
[M]G (here M is the integer stride magnitude, not the field-cost unit), three
additions by G for neighboring strides and signs; offsets, WT_i, BT_i,
central offset and remaining centers. Offsets can be generated incrementally,
WT_i=2(ell*T_i)+T_i, BT_i=[k](WT_i). These are paid support constructions,
not inspected search outputs. Special coincidences require dispatch.

Four families need8k full affine center records, up to4ell full offsets,
constant support points, indices and O(k) reusable inversion scratch, in
addition to search records. The recorded finite key-table maxima omit these.
The known one-frontier control need not allocate a second array.

For a family, if the expanded center-index span including next buffers is
less than q and stride is nonzero modulo q, the used centers are distinct.
Each equality to ±uT_i then occurs at most once per sign; infinity at most
once, and advance exceptions concern ±BT_i. The resulting O(ell) exceptional
dispatches per family still cost actual work. Initialization exceptions are
separate. This argument is not a zero-exception assumption or finite ledger.

Expected ordinary arithmetic can thus be expressed as

    Cx*E[generated keys]
      + sum_i Pr(reach central block of family i)*k*(2M+S),

plus paid initialization, exceptions, comparisons, storage and verification.
For cases reaching fallback its separate schedule/support must also be priced;
this bridge is for B's main phase and is not permission to apply the fork term
to a fallback family. Nor does it give field-to-CPU/GPU throughput.

This is a focused use of H019's accepted specialization of known paired BSGS
arithmetic. The next-cost design role can use it with these qualifications;
no general interpreter or proof infrastructure is required.
