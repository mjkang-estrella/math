# Torsion-free solutions of nonsingular group equations

Myeongjin Kang; no affiliation. 2026-10-16.
Original prose CC BY 4.0; original code MIT. Third-party inputs remain private and retain their rights.

**UNRESOLVED_FULL_TFS.** This fresh round selects family 256, distinct from the prior Spin, Artin, commutative-algebra, combinatorial and analytic targets. It neither proves nor refutes its frozen assertion. No substantial nomination, independent proof/contribution PASS, manuscript, Lean package, publication, or count increase is claimed. The accepted count remains **4/10**.

The main research finding is an exact coefficient-preservation problem for the standard torsion-free radical, together with a rank obstruction to applying the stipulated theorem during radical removal. A primary example makes the need for successive removal concrete. These are supporting deductions and credited operations, not a restricted replacement for the full theorem.

## Full frozen assertion

For every torsion-free group G, every pair of integers 1<=m<=n, and every ordered list w_1,...,w_m in G*F(x_1,...,x_n), assume its integer exponent-sum matrix A has rank m over Q. TFS asserts that there exist a torsion-free group H, an embedding i:G->H, and h_1,...,h_n in H satisfying all equations w_i(i(G),h_1,...,h_n)=1.

Every cardinality, finite-generation status, word sign, nonzero invariant factor, and square or rectangular nonsingular system is retained. There is no solvability, residual, orderability, local-indicability, layering, or unimodularity hypothesis on G or the equations. The trivial coefficient group is allowed. TFS does not assert uniqueness, finite presentation of H, relative asphericity, or torsion-freeness of the universal presented quotient. `original-scope.md` was frozen before sustained proof work; its SHA256 is `be98807412ea2c5fc4a2b71f44ce63ee3f46bc21d4c6522185a56a92b46f9c06`.

## The stipulated source and paid nearby operations

At openai/math revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, [Nonsingular systems of equations over arbitrary groups](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Nonsingular-systems-of-equations-over-arbitrary-groups-October-5-2026/nonsingular-systems-over-arbitrary-groups.pdf), **Theorem 1**, says that for every group G and every such nonsingular system the canonical map

                   G -> U=(G*F_n)/<<w_1,...,w_m>>

is injective. This truth is stipulated, not audited. The theorem supplies an unrestricted solution group U, with no torsion-free conclusion for U or for a further image. Remark 5.1 already extends the unrestricted assertion to arbitrary independent sets of equations. That extension is not a candidate contribution.

Its companion [The Kervaire theorem for groups](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Kervaire-Theorem-for-Groups-September-24-2026/The-Kervaire-Theorem-for-Groups-September-24-2026.pdf), **Theorem 1.1**, gives one-variable unimodular coefficient injectivity; **Corollary 1.2** gives quotient nontriviality for every word over a nontrivial group. These are not statements about torsion-free solution groups. Their interfaces were read directly.

Before freezing TFS, the operation-level screen rejected three nearby alternatives. Nitsche--Thom Theorem 1.3's covering transfer can already drop its Connes-embeddability hypothesis once unrestricted nonsingular solvability is available; the paper explicitly explains this. Klyachko--Mikheenko--Roman'kov (KMR) already preserve finite series of torsion-free abelian factors. Forester--Rourke already propagate torsion-freeness for layered unimodular systems through relative asphericity. Repackaging any of these is not the desired new operation. The additional operation selected here is coefficient-preserving removal of all torsion for arbitrary torsion-free G and arbitrary nonsingular systems.

## An exact equivalent gap, with proof

Identify G with its embedded image in U. Set T_0=1 and, recursively,

           T_{s+1}=<<u in U : u^k in T_s for some k>=1>>_U,
           T_omega=union_{s>=0} T_s.

This construction is already in Chiodo, [arXiv:1107.1489v3](https://arxiv.org/pdf/1107.1489v3), **Definition 3.9 and Proposition 3.10**, crediting the torsion-free radical of Brodsky--Howie. It is not an original mechanism.

Each T_s is normal and the sequence increases. If (u T_omega)^k=1 then u^k belongs to some finite T_s, so u belongs to T_{s+1}. Thus U/T_omega is torsion free. For any homomorphism f:U->H with H torsion free, induction shows T_s subset ker f: a k-th power in ker f forces its root into ker f, and normal closure preserves inclusion. Hence T_omega subset ker f.

Consequently full TFS for this input is equivalent to

                          G intersect T_omega(U)=1.          (*)

If (*) holds, U/T_omega itself is a required solution group. Conversely every torsion-free solution factors the presentation map through a homomorphism U->H injective on G, and that map kills T_omega. Equivalently, one must establish G intersect T_s(U)=1 at every finite stage. This reformulation retains all frozen quantifiers and is not a proof of (*).

Suppose v in G*F_n represents torsion in U, with v^k in <<w_i>>. A finite normal-closure expression and the exponent homomorphism E:G*F_n->Z^n give

                       k E(v)=sum_i d_i E(w_i),  d_i in Z.

Thus E(v) is in the rational row span of A. Adjoining v=1 adds a dependent row, so Theorem 1 cannot be invoked again. Inductively the same is true for every word adjoined at a later finite radical stage: all earlier new exponent vectors lie in the original row span, and taking a root preserves membership in that rational span. Nothing here proves that a coefficient is actually lost. It proves that the proposed iteration has left the source theorem's hypotheses exactly where a new preservation theorem is needed.

The rational abelianized part is paid: write V=G_ab tensor Q. Then

 U_ab tensor Q = (V direct-sum Q^n)/span_Q{(c_i,a_i)},

where c_i is the coefficient class of w_i and a_i its exponent row. The map V into this quotient is injective, since a combination with zero variable component has sum_i lambda_i a_i=0, forcing all lambda_i=0. The target is a torsion-free abelian group and therefore kills T_omega. It follows that G intersect T_omega(U) lies in ker(G->G_ab tensor Q). The hard obstruction can remain in the rational derived subgroup; this calculation does not eliminate it.

## A checked primary example: torsion removal can create torsion

Chiodo's discussion after Proposition 3.10 gives

                     P=<x,y,z | x^2,y^3,xy z^{-6}>.

Here is the full relevant calculation. In A=C_2*C_3, xy has infinite order by reduced-word normal form. Thus P=A*_{<xy>=<z^6>}<z>, with both edge maps injective, and z has infinite order. A finite-order element of an amalgam is conjugate into a vertex group: a cyclically reduced word of length at least two has powers of positive length and cannot have finite order. Applying the same observation in A shows all torsion of P is conjugate into <x> or <y>. Hence

                 T_1(P)=<<x,y>>,  P/T_1(P)=C_6,  T_2(P)=P.

The quotient really is C_6 because setting x=y=1 leaves exactly z^6=1, with a surjection onto a cyclic group of order six. Thus z acquires torsion only after the first removal.

For any torsion-free G, the same three equations with trivial coefficients have matrix rows (2,0,0),(0,3,0),(1,1,-6), determinant -36. Their universal group is G*P, while its first and second radical quotients are G*C_6 and G. This actual TFS input disproves automatic torsion-freeness of U and sufficiency of a single torsion-removal step. It has a torsion-free solution x=y=z=1 in G and is not a counterexample to TFS.

If instead C=<z> is the coefficient group and x,y the two unknowns, the same relations preserve the infinite cyclic C in P, but every torsion-free solution forces x=y=z=1. This is an actual failure of coefficient-preserving de-torsion for an unrestricted system. Its exponent matrix has THREE rows and only two columns, with rank two. It violates the frozen nonsingularity hypothesis and is explicitly not offered as a TFS counterexample. The corresponding nonsingular root-adjunction repair is recorded in `torsion-tower-checkpoint.md`, with its limited scope.

## Other serious proof attempts and their precise limits

Smith normal form can be realized by Nielsen variable operations and normal-closure-preserving relator operations. It diagonalizes exponent rows, not the actual noncommutative words. A relation with exponent zero in another variable may still contain that variable in commutators. Thus it does not construct the layering required in Forester--Rourke Theorem 1; arbitrary nonunit invariant factors also lie beyond that theorem. No universal elimination of those commutator dependencies was proved.

The source's planar **Proposition 4.1** has coefficient-only boundary words and pairs every variable slot. Its balance equations sum_i(p_i-m_i)a_ij=0 give equal positive and negative disk counts. Those equal arrays permit its involution and use of the simultaneous-fixed-space **Theorem 2**. A relation v^k in the normal closure usually has variable slots on its outside boundary and instead gives sum_i d_i a_ij=k E_j(v). Equal counts and the coefficient-only exceptional boundary are absent. No extension paying those changes was obtained; silently copying the proof would assume its central missing hypotheses. The full operational analysis is in `proof-attempt-checkpoint.md`.

There is a useful but already paid residual bound. Define G_r^(0)=G and G_r^(j+1)=ker(G_r^(j)->(G_r^(j))_ab tensor Q). Every G/G_r^(j) has a finite series of torsion-free abelian factors, so the KMR Main theorem and its explicit all-torsion-free-factor corollary give a torsion-free solution over that quotient. The induced U->H_j kills T_omega and is injective on G/G_r^(j). Therefore

               G intersect T_omega(U) subset intersection_j G_r^(j).

This settles groups with trivial such intersection by a standard residual operation; it is not the all-group target or a substantial nomination. For perfect torsion-free G the right side is G. The checkpoint constructs a nontrivial perfect torsion-free direct limit of free groups and proves that standard separated integer-degree Magnus completion cannot embed every torsion-free group. It does not rule out all filtered constructions or give a TFS counterexample.

Ramirez-Cote--Wise **Theorems 9--10** solve square nonsingular systems inside specified power-series groups for groups already embedded there, with the determinant inverted in the scalar ring. This is a genuine paid fixed-point operation; the needed embedding for an arbitrary G is not among its conclusions. KMR's extension theorem cannot be applied with the entire torsion-free class as its starting Howie quasivariety without assuming the assertion under investigation.

Finally, every finite system involves a finitely generated coefficient subgroup C. A torsion-free solution over C extends to one over G by the torsion-free amalgam G*_{C}H_C. Thus arbitrary cardinality is not an extra independent obstacle, but all finitely generated torsion-free coefficient groups still remain. No finite-generation, presentation or residual hypothesis was added to the disposition.

## Contribution comparison, continuity and verification limits

This is a bounded primary comparison, not a worldwide novelty or present-open-status certificate. The full proposed extension would require a nonroutine coefficient-preserving torsion-removal theorem beyond the read inputs. That theorem was not proved. Universal torsion-free quotients, their omega-stage construction, the torsion-tower example, layered propagation, solvable preservation, covering transfer and power-series fixed points are all credited to their primary antecedents. The present reductions and obstruction bookkeeping are technical support. No known subclass or renamed statement is nominated.

The full mandatory 119774-byte r2 brief authenticates to the user-supplied SHA256 `fbd660f35673e94a60dca3180182c530498ffd5a5c52c9aa0821183964ec64f1` and was read, including its Artin, r12 and prior responses. The latest Q4 candidate and scope were read without attempting Q4. Mutable ledger/context bytes are snapshotted inside this directory. Artin R remains an independently passed technical consequence with GHLY/Godelle attribution; prior cross-Hom and unique-root objections are preserved. Q4 remains unresolved after two attempts; a repaired Spin8 schedule is not full Q4 and special-vertex integrality remains unpaid. C/U/H/B/signing/EPnI/BG4/Liouville/mixing/Randers/reconstruction and the other stated vetoes remain untouched. F/G FK remain technical; no endpoint repackaging, Salem work or crossing manuscript work occurred.

`source-contracts.md` and `source-records.json` distinguish actual theorem/proof reading from authentication. The complete nontruncated preprint catalogue was parsed, with all 13223 entries inspected structurally for paths, types and identities; that is not semantic reading of every manuscript. Two pinned PDF blobs are authenticated by Git object identity and SHA256. Primary PDFs and extracted text are privately retained. The failed Brodsky--Howie download is recorded; no full body reading or uninspected small-presentation theorem from that paper is claimed.

No numerical scans or mathematical executable diagnostics were needed for these arguments. No historical or third-party code was executed. The read-only verifier checks exact owned membership, input/output hashes, the frozen scope, two pinned source blobs, retained primary bytes and the exact two external historical files. It certifies integrity only, not TFS, new mathematics, contribution or acceptance. Its code is inspected and authenticated before execution. The detached seal binds manifests; it does not bind future live ledger state. All writes stay inside this owned r13 directory, with no nested agents, staging, commits, uploads, external messages, submission or publication.

**Exact unpaid operation:** prove G intersect T_s((G*F_n)/<<w_i>>)=1 for every finite s and every original torsion-free nonsingular input, or provide one such input with a nontrivial intersection. Neither was obtained. Full TFS remains UNRESOLVED unchanged, and the accepted count stays 4/10.
