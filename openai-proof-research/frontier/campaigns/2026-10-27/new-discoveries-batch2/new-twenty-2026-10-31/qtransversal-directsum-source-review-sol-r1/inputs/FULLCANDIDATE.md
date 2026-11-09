# 373611: full ordinary direct-sum argument, author-only

No scientific qualification, independent PASS, formal dispatch, acceptance, or credit is asserted. This document preserves a complete proposed proof even though significance/routine-adaptation adjudication is unpaid. All fields below are finite base fields; all spaces are finite dimensional over the SAME field. No representation assumption or coordinate hypothesis is used.

Literal and source: originals/373611.jsonl; Fulcher arXiv2603.13550v1, Definition2.7 and Conjecture4.8. With presentations A=(A_i)_{i=1}^k on E1 and B=(B_j)_{j=1}^l on E2, the combined presentation is
D=(A_i directsum E2)_i concatenated with (E1 directsum B_j)_j.
This is the displayed family in the proof of source Theorem4.7 (p11), not a naive concatenation of embedded subspaces. Its independent spaces are precisely spaces every linear basis of which admits an injective assignment of basis vectors to presentation entries that those vectors avoid. The proposed conclusion is equality of this q-matroid with the source direct sum, for every subspace X of E1 directsum E2, not only split X.

Authenticated primary inputs: Saaltink arXiv2503.12201v1, Section3.1 p7 induced rank formula, Theorem15 and its full Hall proof pp8–10, Corollary16, and Theorem18. Fulcher Definition2.7 p3 supplies direct-sum rank. Texts and original PDFs are saved and hashed. Saaltink's Definition14 has a typographical dimension-n phrase for partial transversals; Theorem15's proof explicitly treats an arbitrary m-dimensional space and is the convention also explicitly used by Fulcher Definition2.12. No definition repair to the target is needed.

For any presentation C=(C_i) of length s define f_C(Y)=#{i:Y is not contained in C_i}. The authenticated induced-rank theorem gives
r_C(X)=min_{Y<=X}(f_C(Y)+dim X-dim Y).               (1)
The Hall proof is applicable to arbitrary subspaces, not just coordinate spaces: a basis of a subspace Y extends to a basis of X; an avoiding injection forces f_C(Y)>=dim Y. Conversely, for an arbitrary basis b_a of X, the neighbor sets N_a={i:b_a notin C_i} satisfy Hall because f_C(span{b_a:a in J})=|union_{a in J}N_a|>=|J|. Thus the independence notions agree. Formula(1) is the explicit source induced-rank formula; it is an attributed primary theorem, not a newly proved foundational q-matroid theorem.

FIRST DERIVATION: intersection minima. For I subset [s], put C_I=intersection_{i in I} C_i, with C_empty=E. Then
r_C(X)=min_I(dim X-dim(X intersect C_I)+s-|I|).    (2)
Proof: for Y<=X set I(Y)={i:Y<=C_i}. Its term in(1) is s-|I(Y)|+dim X-dim Y, at least the I(Y) term in(2). In the other direction, for any I take Y=X intersect C_I. Then f_C(Y)<=s-|I|, proving the reverse bound between the two minima. Both minima are attained (finite field, finite dimension); empty I and empty presentations are included.

Write a_I=k-|I|, b_J=l-|J|, A_empty=E1, B_empty=E2. The rank q(X) of D, by(2), is
min_{I,J} [dim X-dim(X intersect (A_I directsum B_J))+a_I+b_J]. (3)
Let d(X) be source direct-sum rank:
d(X)=min_{Y<=X}[r_A(pi1 Y)+r_B(pi2 Y)+dim X-dim Y].
Expand both component ranks by(2). For fixed I,J,Y the term is
 dim X-dim Y + dim(pi1 Y)-dim(pi1 Y intersect A_I)
 + dim(pi2 Y)-dim(pi2 Y intersect B_J) + a_I+b_J.
Let L:Y -> (E1/A_I) directsum (E2/B_J) be the combined quotient map. The sum of the two individual image dimensions is at least dim image L. Its kernel is Y intersect (A_I directsum B_J). Therefore this term is at least
 dim X-dim(Y intersect (A_I directsum B_J))+a_I+b_J,
which is at least the corresponding expression in(3). This proves d(X)>=q(X). Conversely, for fixed I,J choose Y=X intersect (A_I directsum B_J). Both quotient images vanish. The expanded term becomes exactly the I,J term in(3), hence d(X)<=q(X). Thus d=q on ALL subspaces, proving the exact asserted presentation equality.

SECOND DERIVATION: nested minimizers, a check independent of expanding intersection minima. For D, f_D(Y)=f_A(pi1 Y)+f_B(pi2 Y). Since component ranks are at most component f's, d(X)<=q(X). Fix Y<=X and choose T_i<=pi_i Y attaining(1) for each component. Set Z=Y intersect pi1^{-1}(T1) intersect pi2^{-1}(T2). The quotient map from Y to (pi1Y/T1) directsum (pi2Y/T2) has kernel Z, so
 dimY-dimZ <= (dim pi1Y-dimT1)+(dim pi2Y-dimT2).
Monotonicity gives f_A(pi1Z)<=f_A(T1), and likewise for B. Inserting Z into q's minimum yields
 q(X)<=r_A(pi1Y)+r_B(pi2Y)+dimX-dimY.
Minimize over Y to get q<=d. This verifies the reverse direction without assuming projections of X are independent, or that X splits.

Boundary audit: X=0 gives rank0; zero dimensional summands, zero length presentations, repeated presentation entries, entries equal to the whole ambient space, loops, nonminimal presentations, arbitrary prime powers and characteristic2 are all covered. No quotient is assumed to split canonically; rank-nullity alone is used. The finite-field hypothesis ensures all minima exist; no asymptotic or extension-field assumption enters.

Significance and prior disposition: historical exact scalar-ID/key/sourceURL reconciliation over 782 allowed files found no prior target disposition. It found only separate scopes on0811.0949. The root's accepted57+39 remain authoritative and no family is recounted. This derivation completely bridges actual applicable Saaltink rank/union machinery to Fulcher's exact target. Therefore an exclusion as a routine adaptation has a concrete mathematical bridge, rather than relying on shortness. The strongest contrary case is that a March2026 primary paper explicitly formulates the arbitrary noncoordinate statement as Conjecture4.8 after proving only its coordinate case; the proof above removes that exact restriction and pays arbitrary mixed subspaces. Whether that makes the result substantively eligible is NOT decided by its author. Zero qualified survivors/credit here; root significance review remains required.

Current bounded public screen: search3 found a concrete public general representability claim for Saaltink q-transversal matroids on trureturing.org. This is NOT an authenticated direct-sum proof and no representability-to-direct-sum bridge is asserted; its body was not acquired. No novelty clearance follows. Four registry root metadata artifacts are inherited unavailable and were not retried or reconstructed. No worldwide absence assertion. No latest/final equivalence beyond the actual fetched v1 manuscripts is claimed.

Remaining gates: separate adversarial ordinary proof/fidelity audit; significance/routine-adaptation adjudication against the complete bridge above; source latest/final and targeted public direct-sum chronology; literal full Lean endpoint, dependencies and axiom audit; fresh strict replay; paper; root acceptance. None has been dispatched.
